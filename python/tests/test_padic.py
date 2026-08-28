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


# ---------------------------------------------------------------------------
# The Lean side: lean/Collatz/Periodic.lean.  Each test below is the Python
# counterpart of a named Lean theorem, checked on real patterns and cycles.
# ---------------------------------------------------------------------------


def _PB(bs):
    """Collatz.PB — the total halving count of a pattern."""
    return sum(bs)


def _Pc(q, bs):
    """Collatz.Pc — c_L = 2^{b_k} c_{k-1} + 3^{k-1} q."""
    c = 0
    for k, b in enumerate(bs):
        c = 2 ** b * c + 3 ** k * q
    return c


def test_periodic_point_really_is_fixed_by_the_backward_map():
    """IsPeriodic + cycle_equation, tested the way Lean states them.

    An earlier version of this test multiplied `periodic_point`'s Fraction by
    its own denominator, which is true for any numerator and tested nothing.
    This one iterates the backward map `y -> (2^b y - q)/3` and checks the orbit
    actually closes -- which is what `IsPeriodic` asserts -- and only then checks
    the equation.
    """
    import itertools
    from fractions import Fraction

    n_closed = n_integral = 0
    for L in range(1, 5):
        for bs in itertools.product(range(1, 5), repeat=L):
            bs = list(bs)
            B, q = sum(bs), 1
            if 2 ** B == 3 ** L:
                continue
            y = periodic_point(bs, q)
            # iterate the backward map through the whole pattern
            z = y
            for b in bs:
                z = Fraction(2 ** b * z - q, 3)
            assert z == y, (bs, y, z)          # the orbit closes: IsPeriodic
            n_closed += 1
            assert y * (2 ** B - 3 ** L) == _Pc(q, bs), (bs, y)
            if y.denominator == 1:
                n_integral += 1
    assert n_closed == 340
    # over Z most patterns have NO periodic point -- the reason Lean's
    # cycle_equation is a uniqueness statement, not an existence one.
    assert n_integral < n_closed // 10, (n_integral, n_closed)


def test_most_patterns_have_no_integer_periodic_point():
    """Why Periodic.lean proves uniqueness and not existence.

    `IsPeriodic` lives in Z, and over Z the equation usually has no solution --
    the periodic point is only rational.  b = (3), q = 1 gives 1/5.
    """
    import itertools

    assert periodic_point([3], 1) == __import__("fractions").Fraction(1, 5)
    total = integral = 0
    for L in range(1, 5):
        for bs in itertools.product(range(1, 5), repeat=L):
            bs = list(bs)
            if 2 ** sum(bs) == 3 ** L:
                continue
            total += 1
            if periodic_point(bs, 1).denominator == 1:
                integral += 1
    assert total == 340
    assert integral / total < 0.05, (integral, total)


def test_all_ones_pattern_gives_minus_one_at_every_length():
    """Collatz.minus_one_of_ones, and Collatz.Pc_ones (c_L = 3^L - 2^L)."""
    for L in range(1, 25):
        assert periodic_point([1] * L, 1) == -1
        assert _Pc(1, [1] * L) == 3 ** L - 2 ** L
        assert _PB([1] * L) == L


def test_minus_one_is_not_a_natural_number():
    """Collatz.ones_not_a_cycle -- the whole point, in one line."""
    assert periodic_point([1] * 7, 1) == -1
    assert periodic_point([1] * 7, 1) < 0


def test_every_base_three_digit_of_minus_one_is_two():
    """Collatz.all_digits_two: (3^k - 1) / 3^j = 2 (mod 3) for every j < k.

    This is why the sieve can never eliminate the class of -1: at every depth
    its residue ends in the digit an odd halving count requires.
    """
    for k in range(1, 16):
        r = 3 ** k - 1              # -1 mod 3^k
        for j in range(k):
            assert (r // 3 ** j) % 3 == 2, (k, j)


def test_only_constant_pattern_reaching_a_positive_integer_is_b_two():
    """Collatz.const_positive_integer -- and it gives the trivial cycle."""
    hits = []
    for b in range(1, 40):
        y = periodic_point([b], 1)
        if y > 0 and y.denominator == 1:
            hits.append((b, int(y)))
    assert hits == [(2, 1)]


def test_a_real_cycle_is_a_positive_integer_periodic_point():
    """Collatz.Cycle.cycle_is_positive_periodic and T7_from_periodic."""
    from collatz_maxodd.census import primitive_cycles, total_halvings
    from collatz_maxodd.syracuse import v2

    n = 0
    for q in [q for q in range(1, 200, 2) if q % 3]:
        for L, M, el in primitive_cycles(q, 40 * q):
            # Cycle.bb is indexed BACKWARDS from the maximum: bb 1 is the hop
            # INTO M, so the pattern is the reverse of the forward halvings.
            fwd, y = [], M
            for _ in range(L):
                b = v2(3 * y + q)
                fwd.append(b)
                y = (3 * y + q) >> b
            assert y == M, "the orbit must close"
            bs = list(reversed(fwd))
            assert sum(bs) == total_halvings(el, q)
            pt = periodic_point(bs, q)
            assert pt == M and pt > 0, (q, M, bs, pt)
            n += 1
    assert n > 100
