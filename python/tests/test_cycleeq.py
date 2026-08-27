"""The cycle equation, log2(3) continued fractions, and the length bound."""

from __future__ import annotations

from fractions import Fraction

import pytest

from collatz_maxodd.cycleeq import (
    BARINA_2025_LIMIT,
    best_upper_approximations,
    cf_record_depths,
    check_cycle_equation,
    cycle_constant,
    length_admissible,
    log2_3,
    log2_3_cf,
    log2_3_convergents,
    min_B_for_L,
    smallest_admissible_length,
)
from collatz_maxodd.cycles import find_cycles

#: Published continued fraction of log2(3).
CF_LOG2_3 = (1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, 1, 4, 3)

#: Published convergents.
CONVERGENTS = (
    (1, 1), (2, 1), (3, 2), (8, 5), (19, 12),
    (65, 41), (84, 53), (485, 306), (1054, 665),
)


def test_cf_matches_published_terms():
    assert log2_3_cf(len(CF_LOG2_3)) == CF_LOG2_3


def test_convergents_match_published():
    assert log2_3_convergents(len(CONVERGENTS)) == CONVERGENTS


def test_convergents_verified_by_exact_integer_arithmetic():
    """No floating point: 2^p vs 3^q decides which side of log2 3 each one is on."""
    for k, (p, r) in enumerate(log2_3_convergents(12)):
        below = 2**p < 3**r
        assert below == (k % 2 == 0), (k, p, r)


def test_convergents_are_best_approximations():
    """Brute force: no smaller denominator beats a convergent, up to q = 700."""
    conv = {r: p for p, r in log2_3_convergents(9)}
    alpha = log2_3(60)
    for r, p in conv.items():
        if r > 700:
            continue
        target = abs(Fraction(p, r) - Fraction(alpha))
        for rr in range(1, r):
            pp = round(rr * float(alpha))
            assert abs(Fraction(pp, rr) - Fraction(alpha)) > target, (r, rr)


def test_min_B_for_L_is_floor_plus_one():
    import math

    for L in range(1, 300):
        assert min_B_for_L(L) == math.floor(L * math.log2(3)) + 1
        assert 2 ** min_B_for_L(L) > 3**L
        assert 2 ** (min_B_for_L(L) - 1) < 3**L


def test_cf_record_depths():
    """Depths where floor(k log2 3) is tightest: convergent/semiconvergent denominators."""
    assert cf_record_depths(700) == [1, 2, 7, 12, 53, 359, 665]
    denominators = {r for _, r in log2_3_convergents(10)}
    assert {2, 12, 53, 665} <= denominators


def test_best_upper_approximations_are_above_and_improving():
    alpha = log2_3(60)
    prev = None
    for p, r in best_upper_approximations(24):
        gap = Fraction(p, r) - Fraction(alpha)
        assert gap > 0
        if prev is not None:
            assert gap < prev
        prev = gap
    assert best_upper_approximations(24)[0] == (2, 1)
    assert (8, 5) in best_upper_approximations(24)
    assert (65, 41) in best_upper_approximations(24)


def test_cycle_equation_on_every_small_cycle():
    for q in range(1, 200, 2):
        if q % 3 == 0:
            continue
        for c in find_cycles(q, 5000):
            assert check_cycle_equation(c), c
            assert c.M * ((1 << c.B) - 3**c.L) == cycle_constant(c) > 0


def test_trivial_cycle_equation():
    (c,) = find_cycles(1, 1)
    assert (c.L, c.M, c.B) == (1, 1, 2)
    assert c.M * ((1 << c.B) - 3**c.L) == 1 * (4 - 3) == cycle_constant(c) == 1


def test_length_admissible_squeeze():
    """The trivial cycle passes; large minimum elements kill every small L."""
    assert length_admissible(1, 1, 1)  # {1}
    for L in range(1, 200):
        assert not length_admissible(L, 10**12, 1)


def test_smallest_admissible_length_is_monotone_and_matches_landmarks():
    L6, B6, m6 = smallest_admissible_length(10**6)
    assert (L6, B6) == (2966, 4701)
    assert m6 > 0
    L12, B12, _ = smallest_admissible_length(10**12)
    assert (L12, B12) == (10_781_274, 17_087_915)
    LB, BB, _ = smallest_admissible_length(BARINA_2025_LIMIT)
    assert LB == 72_057_431_991
    assert L6 < L12 < LB


def test_smallest_admissible_length_agrees_with_brute_force():
    """Brute force over every L, with EXACT integer arithmetic, not just the records.

    This is the check that the continued-fraction shortcut in
    ``best_upper_approximations`` is not silently skipping a smaller admissible
    ``L`` -- which would turn the reported bound into an overclaim.  ``m = 10**6``
    reaches ``L = 2966``, i.e. 2966 exact big-integer comparisons.
    """
    for m in (100, 1000, 10_000, 10**6):
        L, _, _ = smallest_admissible_length(m)
        brute = next(x for x in range(1, L + 1) if length_admissible(x, m, 1))
        assert brute == L, (m, L, brute)


def test_smallest_admissible_length_is_confirmed_by_exact_integers():
    """B really is the minimal exponent for L, at every reported landmark.

    ``length_admissible`` itself is only usable at ``m = 10**6`` (it forms
    ``(3m+q)**L``; at the Barina landmark ``L`` is 7.2e10 and the integer would
    have 10**12 digits).  For the two big landmarks the check is the exact
    integer identity ``B = floor(L log2 3) + 1`` plus ``2^B > 3^L``.
    """
    from decimal import Decimal

    L, B, _ = smallest_admissible_length(10**6)
    assert min_B_for_L(L) == B and length_admissible(L, 10**6, 1)
    alpha = log2_3(300)
    for m in (10**12, BARINA_2025_LIMIT):
        L, B, margin = smallest_admissible_length(m)
        # B is minimal for this L: (B-1)/L < log2 3 < B/L
        assert Decimal(B - 1) / Decimal(L) < alpha < Decimal(B) / Decimal(L), (m, L, B)
        assert margin > 0


def test_barina_limit_value():
    assert BARINA_2025_LIMIT == 2075 * 2**60 == 2_392_312_122_059_207_475_200


def test_no_new_bound_is_claimed():
    """Sanity/honesty: our elementary bound is WEAKER than the published one.

    Hercher (JIS 26 (2023) Art. 23.3.5) gives K > 1.375e11 odd elements using
    Baker's theorem; the elementary continued-fraction squeeze here gives ~7.2e10.
    """
    L, _, _ = smallest_admissible_length(BARINA_2025_LIMIT)
    assert L < 1.375e11
