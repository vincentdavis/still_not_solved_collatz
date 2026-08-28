"""The minimum's mirror constraints, and the min-max sandwich.

Checked against the census of real 3n+q cycles, where minima actually exist.
"""

from __future__ import annotations

import math

import pytest

from collatz_maxodd.bounds import (
    can_be_min_odd,
    drops_below,
    min_residues_mod12,
    sandwich_holds,
    scale,
)
from collatz_maxodd.census import primitive_cycles, total_halvings

ADMISSIBLE = [q for q in range(1, 400, 2) if q % 3]


def _census():
    for q in ADMISSIBLE:
        for L, M, el in primitive_cycles(q, 40 * q):
            m = min(el)
            if m > q and M > q:
                yield q, L, total_halvings(el, q), m, M, el


def test_census_is_big_enough_to_mean_something():
    assert sum(1 for _ in _census()) > 50


def test_minimum_obeys_the_mirror_conditions():
    """b = 1 out of the minimum, and (3m+q)/2 lands odd."""
    for q, _L, _B, m, _M, _el in _census():
        assert can_be_min_odd(m, q), (q, m)


def test_maximum_is_never_a_valid_minimum():
    """The two ends are genuinely different constraints."""
    for q, _L, _B, m, M, _el in _census():
        if M != m:
            assert not can_be_min_odd(M, q), (q, M)


def test_hop_into_the_minimum_takes_at_least_two_halvings():
    def v2(n):
        b = 0
        while n % 2 == 0:
            n //= 2; b += 1
        return b
    def S(n, q):
        y = 3 * n + q
        while y % 2 == 0:
            y //= 2
        return y
    for q, _L, _B, m, _M, el in _census():
        for x in el:
            if S(x, q) == m:
                assert v2(3 * x + q) >= 2, (q, m, x)


def test_min_residue_classes():
    assert min_residues_mod12(1) == (7, 11)
    assert min_residues_mod12(7) == (1, 5)
    for q, _L, _B, m, _M, _el in _census():
        assert m % 12 in min_residues_mod12(q), (q, m)


def test_the_sandwich_holds_on_every_real_cycle():
    """m <= K q L / (B - L log2 3) <= M."""
    n = 0
    for q, L, B, m, M, _el in _census():
        assert sandwich_holds(q, L, B, m, M), (q, L, B, m, M)
        n += 1
    assert n > 50


def test_scale_needs_2B_over_3L():
    with pytest.raises(ValueError):
        scale(1, 3, 4)          # 2^4 = 16 < 27 = 3^3


def test_cycles_sharing_L_and_B_share_a_scale_and_all_straddle_it():
    """q = 47 has five cycles with L = 4, B = 7 -- one scale, five ranges."""
    rows = [(m, M) for q, L, B, m, M, _ in _census() if q == 47 and L == 4 and B == 7]
    assert len(rows) >= 4
    S = scale(47, 4, 7)
    assert all(m <= S <= M for m, M in rows)


def test_drops_below_refutes_half_of_all_odds_in_one_step():
    """e(m) = 1 exactly when m descends, i.e. m = 1 (mod 4) -- the half the
    mirror rule forbids as a minimum."""
    rng = list(range(3, 40001, 2))
    one = [m for m in rng if drops_below(m) == 1]
    assert all(m % 4 == 1 for m in one)
    assert 0.48 < len(one) / len(rng) < 0.52


def test_drops_below_and_can_be_min_are_consistent():
    """If m descends immediately it cannot be a minimum."""
    for m in range(3, 20001, 2):
        if drops_below(m) == 1:
            assert not can_be_min_odd(m)


# ---------------------------------------------------------------------------
# The mirror as formalized in lean/Collatz/Minimum.lean.
#
# Each test below is the Python counterpart of a named Lean theorem, checked on
# real cycles so that the two sides cannot drift apart.
# ---------------------------------------------------------------------------


def _S(n: int, q: int) -> int:
    t = 3 * n + q
    while t % 2 == 0:
        t //= 2
    return t


def _v2i(n: int) -> int:
    b = 0
    while n % 2 == 0:
        n //= 2
        b += 1
    return b


def test_min_mod4_mirrors_T1():
    """Cycle.min_mod4: `3m + q = 2 (mod 4)`, against T1's `3M + q = 0 (mod 4)`.

    The same expression at the two ends, in the two different even classes.
    """
    for q, _L, _B, m, M, _el in _census():
        assert (3 * m + q) % 4 == 2
        assert (3 * M + q) % 4 == 0


def test_min_mod4_prime_puts_the_ends_two_apart():
    """Cycle.min_mod4' vs Cycle.T1_mod4: `m = q + 2` and `M = q` (mod 4)."""
    for q, _L, _B, m, M, _el in _census():
        assert m % 4 == (q + 2) % 4
        assert M % 4 == q % 4
        assert m % 4 != M % 4


def test_min_bb_out_is_a_single_halving():
    """Cycle.min_bb_out: with `q < m`, the step out of the minimum halves once."""
    for q, _L, _B, m, _M, _el in _census():
        assert _v2i(3 * m + q) == 1


def test_min_bb_in_needs_two_halvings_unconditionally():
    """Cycle.min_bb_in: the hop *into* the minimum takes >= 2 halvings.

    Stated with no size hypothesis in Lean, so it is checked here over the
    whole census -- including the cycles with `m <= q`.
    """
    n = 0
    for q in ADMISSIBLE:
        for _L, _M, el in primitive_cycles(q, 40 * q):
            m = min(el)
            pred = [x for x in el if _S(x, q) == m]
            assert pred, (q, m)
            assert _v2i(3 * pred[0] + q) >= 2
            n += 1
    assert n == 349


def test_min_bb_out_really_needs_q_lt_m():
    """Cycle.min_bb_out_needs_hypothesis, and the 197 census witnesses.

    Dropping `q < m` makes the statement false, so the hypothesis is not
    bookkeeping.  `cycle17` is the instance Lean carries; the census has many.
    """
    # the Lean counterexample: {5, 1} is a genuine S_17-cycle
    assert _S(5, 17) == 1 and _S(1, 17) == 5
    assert _v2i(3 * 1 + 17) == 2          # two halvings out of the minimum

    def _breaks(hi: int):
        return [
            (q, min(el))
            for q in range(1, hi, 2)
            if q % 3
            for _L, _M, el in primitive_cycles(q, 40 * q)
            if _v2i(3 * min(el) + q) != 1
        ]

    # every failure is outside the hypothesis.  Note this shows the hypothesis
    # cannot be DROPPED, not that it is necessary: cycles with m <= q that
    # satisfy the conclusion anyway exist (q=7, {11,5}) -- see the Lean
    # theorem min_bb_out_hypothesis_not_necessary.
    assert all(m <= q for q, m in _breaks(400))
    # the figure quoted in docs/CERTIFY.md and on the web page, over its range
    assert len(_breaks(600)) == 197


def test_q1_minimum_is_seven_or_eleven_mod_twelve():
    """Cycle.min_mod12_q1, and its disjointness from T3's `M = 5 (mod 12)`."""
    assert set(min_residues_mod12(1)) == {7, 11}
    assert 5 not in min_residues_mod12(1)
