"""Structural constraints on a cycle given its maximum -- all against real cycles."""

from __future__ import annotations

import math
from fractions import Fraction

import pytest

from collatz_maxodd.census import primitive_cycles, total_halvings
from collatz_maxodd.structure import (ascent_bound, max_cycle_length,
                                      min_single_halving_fraction,
                                      reachable_set, single_halving_bound)


def _S(n, q):
    m = 3 * n + q
    while m % 2 == 0:
        m //= 2
    return m


def _v2(n):
    b = 0
    while n % 2 == 0:
        n //= 2; b += 1
    return b


def _census():
    for q in [q for q in range(1, 600, 2) if q % 3]:
        for L, M, el in primitive_cycles(q, 40 * q):
            if min(el) > q:
                yield q, L, M, el


def test_every_cycle_lies_inside_the_reachable_set():
    n = 0
    for q, _L, M, el in _census():
        assert set(el) <= reachable_set(M, q), (q, M)
        n += 1
    assert n > 50


def test_length_is_bounded_by_the_reachable_set():
    for q, L, M, _el in _census():
        assert L <= max_cycle_length(M, q), (q, M, L)


def test_reachable_set_terminates_on_a_real_cycle_max():
    """backward_depth has to be capped here; this does not."""
    R = reachable_set(49, 5)
    assert {19, 31, 49} <= R
    assert len(R) == 10


def test_ascent_bound_holds():
    """Climbing from the minimum to the maximum cannot be quick."""
    for q, _L, M, el in _census():
        m = min(el)
        up, x = 0, m
        while x != M:
            x = _S(x, q); up += 1
        assert up >= ascent_bound(m, M, q) - 1e-9, (q, m, M, up)


def test_descent_can_be_a_single_step_but_ascent_often_cannot():
    single = 0
    for q, _L, M, el in _census():
        m = min(el)
        down, x = 0, M
        while x != m:
            x = _S(x, q); down += 1
        if down == 1:
            single += 1
    assert single > 10, single          # the two halves are genuinely asymmetric


def test_single_halving_bound():
    for q, L, _M, el in _census():
        B = total_halvings(el, q)
        u = sum(1 for x in el if _v2(3 * x + q) == 1)
        assert u >= single_halving_bound(L, B), (q, L, B, u)


def test_q1_forces_at_least_41_percent_single_halvings():
    """The sandwich pins B/L, so u/L >= 2 - log2(3 + 1/m) -> 0.415."""
    f = min_single_halving_fraction(2392312122059207475200)
    assert 0.41500 < f < 0.41510
    assert min_single_halving_fraction(10 ** 6) < f          # weaker for smaller m
    assert f < 2 - math.log2(3) + 1e-9


def test_rejects_bad_input():
    for bad in (0, -3, 4):
        with pytest.raises(ValueError):
            reachable_set(bad)
    with pytest.raises(ValueError):
        ascent_bound(49, 19)          # m > O


# ---------------------------------------------------------------------------
# The Lean side: lean/Collatz/Reach.lean proves `L <= |R(O)|`, but its count
# `countLE (inR q M M) M` is NOT reduced by the Lean kernel -- `S` goes through
# `oddPart`, which is well-founded recursion and therefore sealed, and
# `native_decide` is banned by lean/check.sh.  So the claim "the count is 10"
# rests on `#eval` plus these tests, while "L is at most the count" is proved.
#
# These reimplement `Collatz.Cycle.inR` exactly and check it against
# `reachable_set`, which is the function the web page and docs quote.
# ---------------------------------------------------------------------------


def _lean_inR(q: int, O: int, d: int, x: int) -> bool:
    """Exactly `Collatz.Cycle.inR q O d x`: odd, and reaching `O` within `d`
    forward steps without ever exceeding `O`."""
    if x % 2 != 1:
        return False
    cur = x
    for _ in range(d):
        if cur == O:
            return True
        if cur > O:
            return False
        cur = _S(cur, q)
    return cur == O


def _lean_countLE(q: int, O: int, d: int) -> int:
    """Exactly `countLE (inR q O d) O`."""
    return sum(1 for x in range(O + 1) if _lean_inR(q, O, d, x))


def _S(n: int, q: int) -> int:
    t = 3 * n + q
    while t % 2 == 0:
        t //= 2
    return t


def test_lean_inR_agrees_with_reachable_set():
    """The Lean predicate and the Python set are the same object.

    Depth `O` is what `Cycle.length_le_reach_M` uses, and it is enough: a path
    to `O` staying `<= O` cannot repeat a value (the map is a function), so it
    visits at most (O+1)/2 odd numbers.
    """
    checked = 0
    for q in (1, 5, 7, 11, 17, 37):
        for O in range(1, 260, 2):
            if O % 3 == 0:
                continue
            assert _lean_countLE(q, O, O) == len(reachable_set(O, q)), (q, O)
            checked += 1
    assert checked > 500


def test_lean_reach_count_on_real_cycle_maxima():
    """The four figures quoted in Reach.lean's header comment."""
    assert _lean_countLE(5, 49, 49) == len(reachable_set(49, 5)) == 10
    assert _lean_countLE(11, 79, 79) == len(reachable_set(79, 11)) == 19
    assert _lean_countLE(1, 3077, 3077) == len(reachable_set(3077, 1)) == 408
    # 10^6+3 is quoted too, but scanning a million candidates in Python is slow;
    # reachable_set alone is enough to pin the value the page quotes.
    assert len(reachable_set(1000003, 1)) == 1


def test_the_bound_actually_holds_on_the_census():
    """`L <= |R(O)|` on every cycle we have -- the theorem, checked."""
    n = 0
    for q in [q for q in range(1, 400, 2) if q % 3]:
        for L, M, _el in primitive_cycles(q, 40 * q):
            assert L <= len(reachable_set(M, q)), (q, L, M)
            n += 1
    assert n > 300


def test_oddness_is_part_of_membership_not_an_afterthought():
    """Dropping the parity test overcounts -- the bug caught during formalizing.

    Even numbers can feed into `O` under `S_q`; they are not in `R(O)`, which
    lives on the odd numbers the Syracuse map acts on.
    """
    def without_parity(q, O, d):
        n = 0
        for x in range(O + 1):
            cur = x
            for _ in range(d):
                if cur == O:
                    n += 1
                    break
                if cur > O:
                    break
                cur = _S(cur, q)
            else:
                if cur == O:
                    n += 1
        return n

    assert without_parity(5, 49, 49) == 12        # vs 10 with the parity test
    assert _lean_countLE(5, 49, 49) == 10


# ---------------------------------------------------------------------------
# The 41.5% figure as lean/Collatz/Halving.lean states it -- with no reals.
#
# The statement "at least 41.5% of steps are single halvings" is the INTEGER
# inequality 1000*u >= 415*L.  What replaces log2(3) is one rational bound,
# 317/200, certified by the integer fact 3^200 < 2^317.
# ---------------------------------------------------------------------------


def test_the_certificate_replacing_log2_three():
    """Collatz.cert: 3^200 < 2^317, written 2^256 * 2^61.

    This single integer fact is the whole of the "real arithmetic" the figure
    was once thought to need.  Lean decides it with NO axioms at all.
    """
    assert 3 ** 200 < 2 ** 256 * 2 ** 61
    assert 2 ** 256 * 2 ** 61 == 2 ** 317        # the split is only for Lean's
    #                                              256-exponent eval threshold
    # 317/200 is above log2(3) and at most 1.585, which is what 41.5% needs
    assert 2 ** 317 > 3 ** 200                   # log2 3 < 317/200
    assert 1000 * 317 <= 1585 * 200              # 317/200 <= 1.585
    assert Fraction(415, 1000) <= Fraction(2) - Fraction(317, 200)


def test_the_nearest_convergent_is_not_good_enough():
    """Why 317/200 and not something smaller.

    65/41 is the convergent of log2(3) just above it, and it is cheap -- but it
    yields only 2 - 65/41 = 41.46%, short of 41.5%.  So the certificate has to
    be about this large; that is a fact about log2(3), not a choice.
    """
    assert 3 ** 41 < 2 ** 65                     # log2 3 < 65/41, and cheaply
    assert Fraction(2) - Fraction(65, 41) < Fraction(415, 1000)
    assert float(Fraction(2) - Fraction(65, 41)) == pytest.approx(0.414634, abs=1e-6)


def test_percent_arithmetic_is_exactly_what_lean_proves():
    """Collatz.Cycle.percent_arithmetic: 200B<=317L and 2L<=B+u => 415L<=1000u."""
    for L in range(1, 60):
        for B in range(1, 3 * L + 2):
            if 200 * B > 317 * L:
                continue
            for u in range(0, 2 * L + 2):
                if 2 * L <= B + u:
                    assert 415 * L <= 1000 * u, (L, B, u)


def test_the_size_hypothesis_is_discharged_not_assumed():
    """Collatz.cert_m: (3m+1)^200 <= 2^317 * m^200 for every m >= 12825.

    This is the ONLY input to the 41.5% theorem, and unlike a Baker-type
    hypothesis it is proved outright -- `decide` at m = 12825 plus monotonicity.
    Note it says nothing about L: an earlier version routed through the
    linearized `squeeze` and picked up a spurious L-vs-m coupling.
    """
    def ok(m):
        return (3 * m + 1) ** 200 <= 2 ** 317 * m ** 200

    assert ok(12825)
    assert not ok(12824)                      # the threshold is exact
    for m in (12825, 12826, 10 ** 6, 10 ** 12, 2392312122059207475200):
        assert ok(m)


def test_barina_clears_the_threshold_by_a_wide_margin():
    """For q=1 the hypothesis is supplied by the verified search.

    Any nontrivial Collatz cycle has minimum > 2.39e21 (Barina 2025), against a
    requirement of 12825 -- seventeen orders of magnitude of headroom.
    """
    barina = 2392312122059207475200
    assert barina > 12825
    assert math.log10(barina / 12825) > 17
    assert (3 * barina + 1) ** 200 <= 2 ** 317 * barina ** 200


def test_the_size_hypothesis_is_load_bearing():
    """Collatz.Cycle.needs_the_size_hypothesis.

    The trivial cycle {1} has L=1, B=2, u=0 and minimum 1, so the conclusion is
    FALSE for it -- dropping the hypothesis would make the theorem false, not
    merely unprovable.  (B/L = 2 > 1.585, as it must be for a cycle this small.)
    """
    L, B, u, m = 1, 2, 0, 1
    assert not (415 * L <= 1000 * u)
    assert m < 12825
    assert 200 * B > 317 * L


def test_lean_bound_is_below_the_true_real_bound():
    """Lean proves >= 0.415; the true bound is 2 - log2(3 + 1/m).

    The formalized constant is deliberately a hair conservative -- that is what
    makes it rational, and hence provable without any real numbers at all.
    """
    m = 2392312122059207475200
    true_bound = 2 - math.log2(3 + 1 / m)
    assert 0.415 <= true_bound
    assert true_bound == pytest.approx(0.4150374992788438, abs=1e-15)
    # and 2 - log2(3) is the limiting value quoted on the page
    assert 2 - math.log2(3) == pytest.approx(0.4150374992788438, abs=1e-15)
