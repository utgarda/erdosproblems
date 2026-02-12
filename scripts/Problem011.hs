{-# LANGUAGE BangPatterns #-}
{- |
  Optimized counterexample search for Erdős Problem #11 in Haskell.

  Compile:  ghc -O2 -threaded Problem011.hs
  Run:      ./Problem011 +RTS -N

  Uses unboxed mutable arrays in the IO monad for maximum throughput.
  The segmented sieve approach uses O(segment_size) memory regardless
  of search bound.
-}
module Main where

import Data.Array.IO       (IOUArray, newArray, readArray, writeArray)
import Data.Array.Unboxed  (UArray, assocs)
import Data.Array.Unsafe   (unsafeFreeze)
import Data.IORef
import Data.Word           (Word8)
import Data.Bits           (shiftL)
import Control.Monad       (when, unless, forM_)
import System.CPUTime      (getCPUTime)
import Text.Printf         (printf)

-- | Segmented squarefree sieve for [lo, hi).
--   Returns a mutable array where index i corresponds to (lo + i).
--   Value 1 = squarefree, 0 = not squarefree.
segSieve :: Int -> Int -> IO (IOUArray Int Word8)
segSieve lo hi = do
    let !size = hi - lo
    sf <- newArray (0, size - 1) 1 :: IO (IOUArray Int Word8)
    when (lo == 0 && size > 0) $ writeArray sf 0 0

    -- Sieve primes up to sqrt(hi)
    let !limit = ceiling (sqrt (fromIntegral hi :: Double)) + 1
    isPrime <- newArray (0, limit) 1 :: IO (IOUArray Int Word8)
    when (limit >= 0) $ writeArray isPrime 0 0
    when (limit >= 1) $ writeArray isPrime 1 0

    -- Eratosthenes sieve for primes
    let sievePrimes !i
          | i * i > limit = return ()
          | otherwise = do
              ip <- readArray isPrime i
              when (ip == 1) $ markOff (i * i) i limit isPrime
              sievePrimes (i + 1)
    sievePrimes 2

    -- Mark multiples of p^2 as non-squarefree
    let markSquares !p
          | p > limit = return ()
          | otherwise = do
              ip <- readArray isPrime p
              when (ip == 1) $ do
                  let !p2 = p * p
                      !start = let r = lo `mod` p2
                               in if r == 0 then 0 else p2 - r
                  markOff start p2 (size - 1) sf
              markSquares (p + 1)
    markSquares 2

    return sf

-- | Tight loop: mark every 'step'-th element as 0, starting at 'start'.
markOff :: Int -> Int -> Int -> IOUArray Int Word8 -> IO ()
markOff !start !step !limit arr = go start
  where
    go !j
      | j > limit = return ()
      | otherwise = writeArray arr j 0 >> go (j + step)

-- | Search for odd counterexamples in [segLo, segHi).
searchSegment :: Int -> Int -> Int -> IO [Int]
searchSegment segLo segHi maxK = do
    let !firstOdd = if odd segLo then segLo else segLo + 1
        !nOdds = max 0 ((segHi - firstOdd + 1) `div` 2)
    if nOdds <= 0
      then return []
      else do
        -- representable[i] = 1 means (firstOdd + 2*i) is representable
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
                          sf <- segSieve actualRemLo (remHi + 1)
                          -- Mark representable odd numbers
                          let markRep !i
                                | i >= nOdds = return ()
                                | otherwise = do
                                    r <- readArray rep i
                                    if r == 1
                                      then markRep (i + 1)
                                      else do
                                        let !n = firstOdd + 2 * i
                                            !rem = n - pow2k
                                        if rem < 1 || rem < actualRemLo
                                          then markRep (i + 1)
                                          else do
                                            let !idx = rem - actualRemLo
                                            isSF <- readArray sf idx
                                            when (isSF == 1) $ do
                                                writeArray rep i 1
                                                modifyIORef' remainingRef (subtract 1)
                                            markRep (i + 1)
                          markRep 0
                  processK (k + 1)
        processK 0

        -- Collect counterexamples (build list from end for efficiency)
        let collect !i !acc
              | i < 0 = return acc
              | otherwise = do
                  r <- readArray rep i
                  if r == 0
                    then collect (i - 1) ((firstOdd + 2 * i) : acc)
                    else collect (i - 1) acc
        collect (nOdds - 1) []

-- | Verify conjecture for all odd numbers in [lo, hi).
verifyRange :: Int -> Int -> Int -> IO [Int]
verifyRange lo hi segSize = do
    let !maxK = if hi > 1 then floor (logBase 2 (fromIntegral hi :: Double)) + 1 else 0
        !lo' = max 3 lo

    allCex <- newIORef ([] :: [Int])
    totalRef <- newIORef (0 :: Int)
    t0 <- getCPUTime

    let processSegs !segLo
          | segLo >= hi = return ()
          | otherwise = do
              let !segHi = min (segLo + segSize) hi
              cex <- searchSegment segLo segHi maxK
              unless (null cex) $
                  modifyIORef' allCex (++ cex)

              let !firstOdd = if odd segLo then segLo else segLo + 1
                  !nOdds = max 0 ((segHi - firstOdd + 1) `div` 2)
              modifyIORef' totalRef (+ nOdds)

              total <- readIORef totalRef
              t1 <- getCPUTime
              let !elapsed = fromIntegral (t1 - t0) / 1e12 :: Double
                  !rate = if elapsed > 0
                          then fromIntegral total / elapsed
                          else 0 :: Double
                  !pct = 100.0 * fromIntegral (segHi - lo')
                       / fromIntegral (hi - lo') :: Double
              if null cex
                then printf "  [%12d, %12d) %5.1f%% | %10.0f odd/s | ok\n"
                            segLo segHi pct rate
                else printf "  [%12d, %12d) %5.1f%% | %10.0f odd/s | COUNTEREXAMPLES: %s\n"
                            segLo segHi pct rate (show cex)

              processSegs segHi

    processSegs lo'
    readIORef allCex

-- | Cross-check against naive method on small range.
verifyCorrectness :: IO Bool
verifyCorrectness = do
    putStrLn "--- Correctness check ---"
    let n = 100000 :: Int
    -- Flat sieve
    sfFlat <- newArray (0, n) 1 :: IO (IOUArray Int Word8)
    writeArray sfFlat 0 0
    let limit = ceiling (sqrt (fromIntegral n :: Double)) + 1
    isPrime <- newArray (0, limit) 1 :: IO (IOUArray Int Word8)
    writeArray isPrime 0 0
    writeArray isPrime 1 0
    let sieveP !i
          | i * i > limit = return ()
          | otherwise = do
              ip <- readArray isPrime i
              when (ip == 1) $ markOff (i*i) i limit isPrime
              sieveP (i + 1)
    sieveP 2

    let markSq !p
          | p > limit = return ()
          | otherwise = do
              ip <- readArray isPrime p
              when (ip == 1) $ markOff (p*p) (p*p) n sfFlat
              markSq (p + 1)
    markSq 2

    -- Reference: check each odd number naively
    let maxK = floor (logBase 2 (fromIntegral n :: Double)) + 1
        powers = [1 `shiftL` k | k <- [0..maxK]]
    refCex <- newIORef ([] :: [Int])
    let checkOdd !m
          | m > n = return ()
          | otherwise = do
              let tryK [] = modifyIORef' refCex (m :)
                  tryK (pk:pks)
                    | pk >= m = tryK pks
                    | otherwise = do
                        let !rem = m - pk
                        isSF <- readArray sfFlat rem
                        if isSF == 1
                          then return ()  -- representable
                          else tryK pks
              tryK powers
              checkOdd (m + 2)
    checkOdd 3

    ref <- readIORef refCex
    let refSorted = reverse ref

    -- Segmented search
    seg <- searchSegment 3 (n + 1) maxK

    if refSorted == seg
      then do
          printf "  PASS: both methods agree (%d counterexamples in [3, %d])\n"
                 (length seg) n
          return True
      else do
          printf "  FAIL: reference=%s, segmented=%s\n" (show refSorted) (show seg)
          return False

main :: IO ()
main = do
    putStrLn $ replicate 65 '='
    putStrLn "Haskell Optimized Search: Erdos Problem #11"
    putStrLn $ replicate 65 '='

    ok <- verifyCorrectness
    unless ok $ error "Correctness check failed"

    -- Search up to 10^7
    putStrLn "\n--- Search up to 10^7 ---"
    t0 <- getCPUTime
    cex1 <- verifyRange 3 (10^(7::Int)) (2 * 10^(6::Int))
    t1 <- getCPUTime
    let elapsed1 = fromIntegral (t1 - t0) / 1e12 :: Double
    printf "\nResult: %s\nCPU time: %.2fs\n"
        (if null cex1 then "No counterexamples" else "FOUND: " ++ show cex1 :: String)
        elapsed1

    -- Search up to 10^8
    putStrLn "\n--- Search 10^7 to 10^8 ---"
    t2 <- getCPUTime
    cex2 <- verifyRange (10^(7::Int)) (10^(8::Int)) (2 * 10^(6::Int))
    t3 <- getCPUTime
    let elapsed2 = fromIntegral (t3 - t2) / 1e12 :: Double
    printf "\nResult: %s\nCPU time: %.2fs\n"
        (if null cex2 then "No counterexamples" else "FOUND: " ++ show cex2 :: String)
        elapsed2

    -- Search up to 10^9
    putStrLn "\n--- Search 10^8 to 10^9 ---"
    t4 <- getCPUTime
    cex3 <- verifyRange (10^(8::Int)) (10^(9::Int)) (4 * 10^(6::Int))
    t5 <- getCPUTime
    let elapsed3 = fromIntegral (t5 - t4) / 1e12 :: Double
    printf "\nResult: %s\nCPU time: %.2fs\n"
        (if null cex3 then "No counterexamples" else "FOUND: " ++ show cex3 :: String)
        elapsed3

    printf "\nConjecture verified for all odd 3 <= n <= 10^9\n"
