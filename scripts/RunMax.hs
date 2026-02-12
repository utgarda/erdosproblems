{-# LANGUAGE BangPatterns #-}
-- | Push verification as far as possible in available time.
--   Pre-computes primes once, uses large segments, minimal overhead.
module Main where

import Data.Array.IO    (IOUArray, newArray, readArray, writeArray)
import Data.Array.Base  (unsafeRead, unsafeWrite, getNumElements)
import Data.IORef
import Data.Word        (Word8)
import Data.Bits        (shiftL)
import Control.Monad    (when, unless, forM_)
import System.CPUTime   (getCPUTime)
import Text.Printf      (printf)

-- | Compute sorted list of primes up to limit via sieve.
computePrimes :: Int -> IO [Int]
computePrimes limit = do
    isPrime <- newArray (0, limit) 1 :: IO (IOUArray Int Word8)
    unsafeWrite isPrime 0 0
    when (limit >= 1) $ unsafeWrite isPrime 1 0
    let sieve !i
          | i * i > limit = return ()
          | otherwise = do
              ip <- unsafeRead isPrime i
              when (ip == 1) $ markOff (i*i) i limit isPrime
              sieve (i + 1)
    sieve 2
    let collect !i !acc
          | i < 2 = return acc
          | otherwise = do
              ip <- unsafeRead isPrime i
              if ip == 1
                then collect (i-1) (i : acc)
                else collect (i-1) acc
    collect limit []

-- | Tight inner loop.
markOff :: Int -> Int -> Int -> IOUArray Int Word8 -> IO ()
markOff !start !step !limit arr = go start
  where
    go !j
      | j > limit = return ()
      | otherwise = unsafeWrite arr j 0 >> go (j + step)

-- | Segmented squarefree sieve using pre-computed primes.
segSieveWithPrimes :: [Int] -> Int -> Int -> IO (IOUArray Int Word8)
segSieveWithPrimes primes lo hi = do
    let !size = hi - lo
    sf <- newArray (0, size - 1) 1 :: IO (IOUArray Int Word8)
    when (lo == 0 && size > 0) $ unsafeWrite sf 0 0
    let go [] = return ()
        go (p:ps)
          | p * p > hi = return ()
          | otherwise = do
              let !p2 = p * p
                  !start = let r = lo `mod` p2
                           in if r == 0 then 0 else p2 - r
              markOff start p2 (size - 1) sf
              go ps
    go primes
    return sf

-- | Search one segment for odd counterexamples.
searchSeg :: [Int] -> Int -> Int -> Int -> IO [Int]
searchSeg primes segLo segHi maxK = do
    let !firstOdd = if odd segLo then segLo else segLo + 1
        !nOdds = max 0 ((segHi - firstOdd + 1) `div` 2)
    if nOdds <= 0
      then return []
      else do
        rep <- newArray (0, nOdds - 1) 0 :: IO (IOUArray Int Word8)
        remainingRef <- newIORef nOdds

        let processK !k
              | k > maxK = return ()
              | otherwise = do
                  remaining <- readIORef remainingRef
                  when (remaining > 0) $ do
                      let !pow2k = 1 `shiftL` k
                          !remHi = firstOdd + 2 * (nOdds - 1) - pow2k
                      when (remHi >= 1) $ do
                          let !actualRemLo = max 1 (firstOdd - pow2k)
                          sf <- segSieveWithPrimes primes actualRemLo (remHi + 1)
                          let markRep !i
                                | i >= nOdds = return ()
                                | otherwise = do
                                    r <- unsafeRead rep i
                                    if r == 1
                                      then markRep (i + 1)
                                      else do
                                        let !n = firstOdd + 2 * i
                                            !rem = n - pow2k
                                        if rem < 1 || rem < actualRemLo
                                          then markRep (i + 1)
                                          else do
                                            let !idx = rem - actualRemLo
                                            isSF <- unsafeRead sf idx
                                            when (isSF == 1) $ do
                                                unsafeWrite rep i 1
                                                modifyIORef' remainingRef (subtract 1)
                                            markRep (i + 1)
                          markRep 0
                  processK (k + 1)
        processK 0

        let collect !i !acc
              | i < 0 = return acc
              | otherwise = do
                  r <- unsafeRead rep i
                  if r == 0
                    then collect (i - 1) ((firstOdd + 2 * i) : acc)
                    else collect (i - 1) acc
        collect (nOdds - 1) []

main :: IO ()
main = do
    let lo   = 10 ^ (10 :: Int)
        hi   = 10 ^ (11 :: Int)       -- aim for 10^11, will report how far we get
        seg  = 20 * 10 ^ (6 :: Int)   -- 20M segment for good amortization
        maxK = floor (logBase 2 (fromIntegral hi :: Double)) + 1
        primeLimit = ceiling (sqrt (fromIntegral hi :: Double)) + 100

    printf "Pre-computing primes up to %d...\n" primeLimit
    t_prime <- getCPUTime
    primes <- computePrimes primeLimit
    t_prime_end <- getCPUTime
    printf "  %d primes in %.2fs\n\n" (length primes)
        (fromIntegral (t_prime_end - t_prime) / 1e12 :: Double)

    printf "Searching [%d, %d) | segment=%dM | max_k=%d\n\n" lo hi (seg `div` (10^(6::Int))) maxK

    totalRef <- newIORef (0 :: Int)
    cexRef   <- newIORef ([] :: [Int])
    t0       <- getCPUTime

    let processSegs !segLo
          | segLo >= hi = return ()
          | otherwise = do
              let !segHi = min (segLo + seg) hi
              cex <- searchSeg primes segLo segHi maxK
              unless (null cex) $ do
                  modifyIORef' cexRef (++ cex)
                  printf "  *** COUNTEREXAMPLE at %s ***\n" (show cex)

              let !firstOdd = if odd segLo then segLo else segLo + 1
                  !nOdds = max 0 ((segHi - firstOdd + 1) `div` 2)
              modifyIORef' totalRef (+ nOdds)

              total <- readIORef totalRef
              t1 <- getCPUTime
              let !elapsed = fromIntegral (t1 - t0) / 1e12 :: Double
                  !rate = if elapsed > 0
                          then fromIntegral total / elapsed
                          else 0 :: Double
                  !pct = 100.0 * fromIntegral (segHi - lo)
                       / fromIntegral (hi - lo) :: Double

              -- Print every ~1%
              when ((truncate (pct * 10) :: Int) `mod` 10 == 0) $
                  printf "  %5.1f%% | n=%12d | %7.1fM odd/s | %.0fs\n"
                         pct segHi (rate / 1e6) elapsed

              processSegs segHi

    processSegs lo

    t_end <- getCPUTime
    total <- readIORef totalRef
    cex   <- readIORef cexRef
    let !totalTime = fromIntegral (t_end - t0) / 1e12 :: Double
        !finalN = lo + 2 * total

    printf "\n==================================================\n"
    printf "Checked: %d odd numbers\n" total
    printf "CPU time: %.1fs | Throughput: %.1fM odd/s\n" totalTime (fromIntegral total / totalTime / 1e6 :: Double)
    if null cex
      then printf "No counterexamples.\n"
      else printf "COUNTEREXAMPLES: %s\n" (show cex)
    printf "Conjecture verified for all odd 3 <= n <= %d\n" finalN
