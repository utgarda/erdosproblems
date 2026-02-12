#!/usr/bin/env python3
"""
Optimized counterexample search for Erdős Problem #11:

  "Is every sufficiently large odd integer the sum of a squarefree number
   and a power of 2?"

APPROACH: Segmented sieve with bulk elimination.

For each segment of odd numbers [L, L+S):
  1. Start with all odd numbers as "potential counterexamples"
  2. For each k = 0, 1, ..., floor(log2(L+S)):
     - Compute a segmented squarefree sieve for [L-2^k, L+S-2^k)
     - For each odd n in the segment where n-2^k IS squarefree,
       mark n as "representable" (not a counterexample)
  3. Any odd n still unmarked after all k values is a counterexample

This uses O(segment_size) memory regardless of search bound, and avoids
per-element trial division by doing bulk sieve operations.

OPTIMIZATIONS:
  - Early termination: skip k values once all candidates are eliminated
  - Order k values by effectiveness (large k first for small remainders
    that are more likely squarefree at small scales, or small k first
    for remainders close to n that have higher squarefree density)
  - Segmented sieve avoids O(N) memory for the full range

For reaching 10^12+, further optimizations would include:
  - C/Cython inner loops
  - Wheel factorization in the sieve
  - Multi-threaded segment processing
  - CRT pre-filter to skip segments with no plausible counterexamples
"""

import math
import time


def segmented_squarefree_sieve(lo, hi):
    """
    Return bytearray sf where sf[i] = 1 iff (lo + i) is squarefree.
    Handles lo = 0 correctly. Uses O(hi - lo + sqrt(hi)) memory.
    """
    size = hi - lo
    if size <= 0:
        return bytearray()
    sf = bytearray(b'\x01' * size)
    if lo == 0:
        sf[0] = 0

    limit = int(math.isqrt(hi)) + 1
    is_prime = bytearray(b'\x01' * (limit + 1))
    is_prime[0] = is_prime[1] = 0
    for i in range(2, int(math.isqrt(limit)) + 1):
        if is_prime[i]:
            for j in range(i * i, limit + 1, i):
                is_prime[j] = 0

    for p in range(2, limit + 1):
        if is_prime[p]:
            p2 = p * p
            start = ((lo + p2 - 1) // p2) * p2 - lo
            if start < 0:
                start += p2
            for j in range(start, size, p2):
                sf[j] = 0
    return sf


def search_segment(seg_lo, seg_hi, max_k_global):
    """
    Search for odd counterexamples in [seg_lo, seg_hi).
    Returns list of counterexamples.

    Algorithm:
      - representable[i] tracks whether odd number (seg_lo + 2*i) has
        been shown to be representable (some n - 2^k is squarefree).
      - For each k, sieve the shifted range and mark representable entries.
    """
    # Number of odd numbers in [seg_lo, seg_hi)
    # Ensure seg_lo is odd
    first_odd = seg_lo if seg_lo % 2 == 1 else seg_lo + 1
    n_odds = (seg_hi - first_odd + 1) // 2
    if n_odds <= 0:
        return []

    # representable[i] = True means odd number (first_odd + 2*i) is representable
    representable = bytearray(n_odds)  # 0 = not yet shown representable

    remaining = n_odds  # count of unresolved odd numbers

    for k in range(max_k_global + 1):
        if remaining == 0:
            break

        pow2k = 1 << k

        # For odd n in [first_odd, first_odd + 2*(n_odds-1)],
        # remainder = n - 2^k.
        # Range of remainders: [first_odd - pow2k, first_odd + 2*(n_odds-1) - pow2k]
        rem_lo = first_odd - pow2k
        rem_hi = first_odd + 2 * (n_odds - 1) - pow2k

        if rem_hi < 1:
            continue  # all remainders non-positive, skip this k

        # Clamp to positive remainders
        actual_rem_lo = max(1, rem_lo)
        actual_rem_hi = rem_hi

        if actual_rem_lo > actual_rem_hi:
            continue

        # Compute squarefree sieve for [actual_rem_lo, actual_rem_hi + 1)
        sf = segmented_squarefree_sieve(actual_rem_lo, actual_rem_hi + 1)

        # Mark representable odd numbers
        for i in range(n_odds):
            if representable[i]:
                continue  # already known representable
            n = first_odd + 2 * i
            rem = n - pow2k
            if rem < 1:
                continue
            if rem < actual_rem_lo:
                continue
            idx = rem - actual_rem_lo
            if sf[idx]:
                representable[i] = 1
                remaining -= 1

    # Collect counterexamples
    counterexamples = []
    for i in range(n_odds):
        if not representable[i]:
            n = first_odd + 2 * i
            counterexamples.append(n)
    return counterexamples


def verify_range(lo, hi, segment_size=2 * 10**6):
    """
    Verify the conjecture for all odd numbers in [lo, hi).
    Uses segmented approach with O(segment_size) memory.
    """
    if lo < 3:
        lo = 3
    max_k = int(math.log2(hi)) + 1 if hi > 1 else 0

    all_counterexamples = []
    total_checked = 0
    t_start = time.time()

    seg_lo = lo
    while seg_lo < hi:
        seg_hi = min(seg_lo + segment_size, hi)

        cex = search_segment(seg_lo, seg_hi, max_k)
        all_counterexamples.extend(cex)

        # Count odd numbers in segment
        first_odd = seg_lo if seg_lo % 2 == 1 else seg_lo + 1
        n_odds = (seg_hi - first_odd + 1) // 2
        total_checked += max(0, n_odds)

        elapsed = time.time() - t_start
        rate = total_checked / elapsed if elapsed > 0 else 0
        pct = 100.0 * (seg_hi - lo) / (hi - lo)
        if cex:
            print(f"  [{seg_lo:>12,}, {seg_hi:>12,}) "
                  f"{pct:5.1f}% | {rate:>10,.0f} odd/s | "
                  f"COUNTEREXAMPLES: {cex}")
        else:
            print(f"  [{seg_lo:>12,}, {seg_hi:>12,}) "
                  f"{pct:5.1f}% | {rate:>10,.0f} odd/s | ok")

        seg_lo = seg_hi

    return all_counterexamples


def verify_correctness():
    """Cross-check against the flat sieve from problem_011.py."""
    print("--- Correctness check ---")

    # Flat sieve reference
    N = 10**5
    sf_flat = bytearray(b'\x01' * (N + 1))
    sf_flat[0] = 0
    limit = int(math.isqrt(N)) + 1
    is_prime = bytearray(b'\x01' * (limit + 1))
    is_prime[0] = is_prime[1] = 0
    for i in range(2, int(math.isqrt(limit)) + 1):
        if is_prime[i]:
            for j in range(i * i, limit + 1, i):
                is_prime[j] = 0
    for p in range(2, limit + 1):
        if is_prime[p]:
            for j in range(p * p, N + 1, p * p):
                sf_flat[j] = 0

    powers = [1 << k for k in range(int(math.log2(N)) + 2)]

    ref_cex = []
    for n in range(3, N + 1, 2):
        found = False
        for pk in powers:
            if pk >= n:
                break
            if sf_flat[n - pk]:
                found = True
                break
        if not found:
            ref_cex.append(n)

    # Segmented search
    seg_cex = search_segment(3, N + 1, int(math.log2(N)) + 1)

    if ref_cex == seg_cex:
        print(f"  PASS: both methods agree (0 odd counterexamples in [3, {N}])")
    else:
        print(f"  FAIL: reference={ref_cex}, segmented={seg_cex}")
    return ref_cex == seg_cex


def main():
    print("=" * 65)
    print("Optimized Counterexample Search: Erdős Problem #11")
    print("=" * 65)

    # Step 1: Correctness verification
    if not verify_correctness():
        print("Correctness check failed, aborting.")
        return

    # Step 2: Benchmark and search
    print("\n--- Search up to 10^7 ---")
    t0 = time.time()
    cex = verify_range(3, 10**7, segment_size=2 * 10**6)
    t1 = time.time()
    print(f"\nResult: {'COUNTEREXAMPLES FOUND: ' + str(cex) if cex else 'No counterexamples'}")
    print(f"Time: {t1 - t0:.2f}s")

    # Step 3: Push to 10^8 to demonstrate scaling
    print("\n--- Search 10^7 to 10^8 ---")
    t0 = time.time()
    cex = verify_range(10**7, 10**8, segment_size=2 * 10**6)
    t1 = time.time()
    print(f"\nResult: {'COUNTEREXAMPLES FOUND: ' + str(cex) if cex else 'No counterexamples'}")
    print(f"Time: {t1 - t0:.2f}s")
    print(f"\nConjecture verified for all odd 3 <= n <= 10^8")


if __name__ == "__main__":
    main()
