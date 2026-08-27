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
