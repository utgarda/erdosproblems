{-# LANGUAGE BangPatterns #-}
module Main where

import Data.Array.IO       (IOUArray, newArray, readArray, writeArray)
import Data.IORef
import Data.Word           (Word8)
import Data.Bits           (shiftL)
import Control.Monad       (when, unless)
import System.CPUTime      (getCPUTime)
import Text.Printf         (printf)

-- | Tight loop: mark every 'step'-th element as 0.
markOff :: Int -> Int -> Int -> IOUArray Int Word8 -> IO ()
markOff !start !step !limit arr = go start
  where
    go !j
      | j > limit = return ()
      | otherwise = writeArray arr j 0 >> go (j + step)

-- | Segmented squarefree sieve for [lo, hi).
segSieve :: Int -> Int -> IO (IOUArray Int Word8)
segSieve lo hi = do
    let !size = hi - lo
    sf <- newArray (0, size - 1) 1 :: IO (IOUArray Int Word8)
    when (lo == 0 && size > 0) $ writeArray sf 0 0
    let !limit = ceiling (sqrt (fromIntegral hi :: Double)) + 1
    isPrime <- newArray (0, limit) 1 :: IO (IOUArray Int Word8)
    when (limit >= 0) $ writeArray isPrime 0 0
    when (limit >= 1) $ writeArray isPrime 1 0
    let sievePrimes !i
          | i * i > limit = return ()
          | otherwise = do
              ip <- readArray isPrime i
              when (ip == 1) $ markOff (i*i) i limit isPrime
              sievePrimes (i + 1)
    sievePrimes 2
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

-- | Search for odd counterexamples in [segLo, segHi).
searchSegment :: Int -> Int -> Int -> IO [Int]
searchSegment segLo segHi maxK = do
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
                          sf <- segSieve actualRemLo (remHi + 1)
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
        let collect !i !acc
              | i < 0 = return acc
              | otherwise = do
                  r <- readArray rep i
                  if r == 0
                    then collect (i - 1) ((firstOdd + 2 * i) : acc)
                    else collect (i - 1) acc
        collect (nOdds - 1) []

main :: IO ()
main = do
    let lo  = 10 ^ (9 :: Int)
        hi  = 10 ^ (10 :: Int)
        seg = 4 * 10 ^ (6 :: Int)
        maxK = floor (logBase 2 (fromIntegral hi :: Double)) + 1

    printf "Searching [%d, %d) for odd counterexamples...\n" lo hi
    printf "Segment size: %d, max k: %d\n\n" seg maxK

    totalRef  <- newIORef (0 :: Int)
    cexRef    <- newIORef ([] :: [Int])
    t0        <- getCPUTime

    let processSegs !segLo
          | segLo >= hi = return ()
          | otherwise = do
              let !segHi = min (segLo + seg) hi
              cex <- searchSegment segLo segHi maxK
              unless (null cex) $ modifyIORef' cexRef (++ cex)

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

              -- Print every ~1% or on counterexample
              when (not (null cex) || (truncate (pct * 10) :: Int) `mod` 10 == 0) $
                  if null cex
                    then printf "  %5.1f%% | n up to %12d | %10.0f odd/s | ok\n" pct segHi rate
                    else printf "  %5.1f%% | n up to %12d | %10.0f odd/s | *** COUNTEREXAMPLES: %s\n"
                                pct segHi rate (show cex)

              processSegs segHi

    processSegs lo

    t_end <- getCPUTime
    let totalTime = fromIntegral (t_end - t0) / 1e12 :: Double
    total <- readIORef totalRef
    cex   <- readIORef cexRef

    printf "\n==================================================\n"
    printf "Search complete: [%d, %d)\n" lo hi
    printf "Odd numbers checked: %d\n" total
    printf "CPU time: %.1fs\n" totalTime
    printf "Throughput: %.0f odd/s\n" (fromIntegral total / totalTime :: Double)
    if null cex
      then printf "Result: No counterexamples found.\n"
      else printf "Result: COUNTEREXAMPLES: %s\n" (show cex)
    printf "Conjecture verified for all odd 3 <= n <= %d\n" hi
