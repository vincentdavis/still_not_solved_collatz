"""Periodic points of the backward map, and the witness that the sieve never empties."""

from __future__ import annotations

from fractions import Fraction

import pytest

from collatz_maxodd.census import primitive_cycles
from collatz_maxodd.padic import (constant_pattern_point, minus_one_survives,
                                  periodic_point)


def _v2(n):
    b = 0
    while n % 2 == 0:
        n //= 2; b += 1
    return b


def _S(n, q):
    m = 3 * n + q
    while m % 2 == 0:
        m //= 2
    return m


def test_periodic_point_reproduces_every_real_cycle():
    """The rational built from the halving vector alone must equal the maximum."""
    n = 0
    for q in [q for q in range(1, 200, 2) if q % 3]:
        for L, M, el in primitive_cycles(q, 40 * q):
            bs, y = [], M
            for _ in range(L):
                pred = next(x for x in el if _S(x, q) == y)
                bs.append(_v2(3 * pred + q)); y = pred
            assert periodic_point(bs, q) == M, (q, M, bs)
            n += 1
    assert n > 100, n


def test_all_ones_pattern_is_minus_one_at_every_length():
    for L in range(1, 12):
        assert periodic_point([1] * L) == Fraction(-1)


def test_constant_patterns():
    assert constant_pattern_point(1) == Fraction(-1)
    assert constant_pattern_point(2) == Fraction(1)      # the trivial cycle
    assert constant_pattern_point(3) == Fraction(1, 5)
    # only b = 2 lands on a positive integer
    pos = [b for b in range(1, 30)
           if constant_pattern_point(b).denominator == 1 and constant_pattern_point(b) > 0]
    assert pos == [2]


def test_minus_one_survives_every_depth():
    """The explicit witness that a_k >= 1, so the sieve can never empty."""
    for k in range(1, 13):
        assert minus_one_survives(k), k


def test_rejects_bad_input():
    for bad in ([], [0], [1, -2]):
        with pytest.raises(ValueError):
            periodic_point(bad)
    with pytest.raises(ValueError):
        constant_pattern_point(0)
