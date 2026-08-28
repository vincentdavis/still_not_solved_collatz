"""Structural constraints on a cycle given its maximum -- all against real cycles."""

from __future__ import annotations

import math

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
