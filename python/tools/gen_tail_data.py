#!/usr/bin/env python3
"""Exact tail of the sieve's death depth d(M).

    python3 python/tools/gen_tail_data.py [K]

Scans one full period of 3^K consecutive odd numbers, which hits every residue
mod 3^K exactly once, so a_k in  P(d >= k) = a_k / 3^k  is exact, not sampled.
"""
import math
import sys

sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parents[1]))
from collatz_maxodd.deathdepth import exact_tail, tail_ratios  # noqa: E402

K = int(sys.argv[1]) if len(sys.argv) > 1 else 12
a = exact_tail(K)
lam = (lambda t: t ** t / (t - 1) ** (t - 1))(math.log2(3))

print(f"one full period: 3^{K} = {3**K:,} consecutive odd numbers\n")
print(f"{'k':>3} {'a_k':>12} {'P(d>=k) = a_k/3^k':>20} {'a_k/a_(k-1)':>12}")
for k, ak in enumerate(a, 1):
    r = f"{ak / a[k - 2]:>12.4f}" if k > 1 else f"{'':>12}"
    print(f"{k:>3} {ak:>12,} {ak / 3**k:>20.9f} {r}")
print(f"\na_k = {a}")
print(f"\nbackward-tree growth lambda = {lam:.5f}  (a^a/(a-1)^(a-1), a = log2 3)")
print(f"conjectured tail rate lambda/3 = {lam/3:.5f}")
print(f"last observed ratio           = {list(tail_ratios(a))[-1]:.5f}  (not converged)")
print("\nNot found in OEIS (full sequence and prefixes, checked 2026-08-26).")
