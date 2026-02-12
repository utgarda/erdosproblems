#!/usr/bin/env python3
"""
Computational exploration of Erdős Problem #11:

  "Is every sufficiently large odd integer the sum of a squarefree number
   and a power of 2?"

This script:
  1. Verifies the conjecture for all odd integers up to a given bound.
  2. Computes the number of representations of each odd number (2n-1)
     as squarefree + power of 2.
  3. Identifies even numbers not expressible as squarefree + power of 2,
     and verifies they are exactly the multiples of 4 where both n-1 and
     n-2 are non-squarefree (connecting to OEIS A068781).
  4. Verifies values of A377587 (smallest odd m with m-2^k not squarefree
     for all 1 <= k <= n).

Findings:
  - The conjecture is verified for all odd 3 <= n <= 10^7.
  - No odd number > 1 has fewer than 2 representations.
  - Even non-representable numbers are exactly multiples of 4 where
    both n-1 and n-2 are non-squarefree, i.e., n-2 is in A068781
    with n-2 ≡ 2 (mod 4). This relates to Erdős's weaker variant
    for integers not divisible by 4.
  - The sequence of even non-representable numbers (100, 244, 344, 352,
    776, 848, ...) and the odd representation count sequence are not
    currently in the OEIS.
"""

import math
import time
from collections import Counter


def squarefree_sieve(N):
    """Return a bytearray where sf[i] = 1 iff i is squarefree, for 0 <= i <= N."""
    sf = bytearray(b'\x01' * (N + 1))
    sf[0] = 0
    limit = int(math.isqrt(N)) + 1
    is_prime = bytearray(b'\x01' * (limit + 1))
    is_prime[0] = is_prime[1] = 0
    for i in range(2, int(math.isqrt(limit)) + 1):
        if is_prime[i]:
            for j in range(i * i, limit + 1, i):
                is_prime[j] = 0
    for p in range(2, limit + 1):
        if is_prime[p]:
            p2 = p * p
            for j in range(p2, N + 1, p2):
                sf[j] = 0
    return sf


def verify_odd(N):
    """
    Verify the conjecture for all odd integers up to N and compute
    representation counts.

    Returns:
      counterexamples: odd n with zero representations
      rep_counts: rep_counts[i] = number of representations of 2*i+1
    """
    print(f"Computing squarefree sieve up to {N}...")
    t0 = time.time()
    sf = squarefree_sieve(N)
    t1 = time.time()
    print(f"  Sieve computed in {t1 - t0:.2f}s")

    powers_of_2 = []
    p = 1
    while p <= N:
        powers_of_2.append(p)
        p *= 2

    counterexamples = []
    rep_counts = []

    print(f"Checking odd integers from 1 to {N}...")
    t0 = time.time()
    for i in range((N + 1) // 2):
        n = 2 * i + 1
        count = 0
        for pk in powers_of_2:
            if pk >= n:
                break
            if sf[n - pk]:
                count += 1
        rep_counts.append(count)
        if count == 0:
            counterexamples.append(n)
    t1 = time.time()
    print(f"  Done in {t1 - t0:.2f}s")

    return counterexamples, rep_counts, sf


def find_even_non_representable(N, sf):
    """Find even numbers up to N not expressible as squarefree + power of 2."""
    powers_of_2 = []
    p = 1
    while p <= N:
        powers_of_2.append(p)
        p *= 2

    non_rep = []
    for n in range(2, N + 1, 2):
        found = False
        for pk in powers_of_2:
            if pk >= n:
                break
            if sf[n - pk]:
                found = True
                break
        if not found:
            non_rep.append(n)
    return non_rep


def verify_A068781_connection(non_rep_even, sf):
    """
    Verify that even non-representable numbers are exactly the multiples of 4
    where both n-1 and n-2 are non-squarefree (i.e., n-2 is in A068781 and
    n-2 ≡ 2 mod 4).
    """
    # Compute from A068781 characterization
    from_a068781 = []
    for m in range(2, max(non_rep_even) + 1 if non_rep_even else 1, 4):
        if not sf[m] and not sf[m + 1]:
            from_a068781.append(m + 2)
    return non_rep_even == from_a068781


def compute_A377587(N, sf):
    """
    Compute A377587(n) for n = 1, ..., N using the provided squarefree sieve.
    a(n) = smallest odd m such that m - 2^k is not squarefree for all 1 <= k <= n.
    """
    sf_limit = len(sf) - 1
    powers_of_2 = []
    p = 2
    while p <= sf_limit:
        powers_of_2.append(p)
        p *= 2

    results = []
    for target_n in range(1, N + 1):
        pows = powers_of_2[:target_n]
        found = False
        for m in range(3, sf_limit + 1, 2):
            all_not_sf = True
            for pk in pows:
                if pk >= m:
                    continue
                if sf[m - pk]:
                    all_not_sf = False
                    break
            if all_not_sf:
                results.append((target_n, m))
                found = True
                break
        if not found:
            break
    return results


def main():
    N = 10**7
    counterexamples, rep_counts, sf = verify_odd(N)

    print("\n" + "=" * 60)
    print("RESULTS: Erdős Problem #11")
    print("=" * 60)

    # --- Odd integer verification ---
    non_trivial = [c for c in counterexamples if c > 1]
    trivial = [c for c in counterexamples if c <= 1]
    if non_trivial:
        print(f"\n*** NON-TRIVIAL COUNTEREXAMPLES: {non_trivial}")
    else:
        print(f"\nConjecture VERIFIED for all odd 3 <= n <= {N}.")
        if trivial:
            print(f"  (Only trivial case: n=1 has 0 representations)")

    # --- Representation count distribution ---
    print("\n--- Representation counts for odd numbers ---")
    dist = Counter(rep_counts)
    for count in sorted(dist.keys()):
        pct = 100.0 * dist[count] / len(rep_counts)
        print(f"  {count} reps: {dist[count]:>8} odd numbers ({pct:.3f}%)")

    # Odd numbers with fewest representations (> 0)
    min_reps = min(c for c in rep_counts if c > 0)
    fewest = [2 * i + 1 for i, c in enumerate(rep_counts)
              if c == min_reps and 2 * i + 1 > 1]
    print(f"\nMinimum representations (for odd n > 1): {min_reps}")
    print(f"  Odd numbers with {min_reps} reps: {fewest}")

    # --- Candidate OEIS sequence: odd representation counts ---
    print(f"\nCandidate sequence (not in OEIS):")
    print(f"  a(n) = #{{k >= 0 : (2n-1) - 2^k is squarefree}}")
    terms = rep_counts[:30]
    print(f"  First 30 terms: {terms}")
    print(f"  OEIS search: {','.join(str(x) for x in rep_counts[:15])}")

    # --- Even non-representable numbers ---
    print("\n--- Even non-representable numbers ---")
    even_nr = find_even_non_representable(N, sf)
    print(f"Count up to {N}: {len(even_nr)}")
    print(f"First 20: {even_nr[:20]}")
    all_div4 = all(x % 4 == 0 for x in even_nr)
    print(f"All divisible by 4: {all_div4}")

    # Verify A068781 characterization
    if even_nr:
        match = verify_A068781_connection(even_nr, sf)
        print(f"A068781 characterization verified: {match}")
        print(f"  (n is non-representable iff n ≡ 0 (mod 4) and both")
        print(f"   n-1, n-2 are non-squarefree, i.e., n-2 ∈ A068781)")

    # --- A377587 verification ---
    print("\n--- A377587 verification ---")
    known = [11, 29, 533, 849, 434977, 10329791]
    a377587 = compute_A377587(6, sf)
    for target_n, val in a377587:
        kv = known[target_n - 1] if target_n <= len(known) else "?"
        status = "OK" if val == kv else "MISMATCH"
        print(f"  A377587({target_n}) = {val} (known: {kv}) [{status}]")


if __name__ == "__main__":
    main()
