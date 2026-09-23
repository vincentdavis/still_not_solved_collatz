"""The drop function ``f_q(n) = n - S_q(n)``: how far an odd number falls to the next odd.

Setting as in ``syracuse.py``: ``S_q(n) = (3n+q)/2^x`` with ``x = v2(3n+q)``, ``n`` odd,
``q`` odd, ``3`` not dividing ``q``.  Write ``s = S_q(n)`` (the *target*, the next odd
number on the trajectory) and

    f_q(n) = n - s = ((2^x - 3) n - q) / 2^x .

Classical Collatz is ``q = 1``; the general ``q`` is the test harness only.  Everything
below is exact integer arithmetic and elementary.

Lemmas (all PROVED, proofs in ``docs/DROP.md``)
----------------------------------------------
D1  ``f_q(n)`` is even.  ``f_q(n) < 0`` iff ``x = 1`` iff ``n = -q (mod 4)`` (a *rise*);
    otherwise ``x >= 2`` and ``f_q(n) = ((2^x-3)n - q)/2^x >= (n - q)/4``.  For ``q = 1``:
    ``f(n) = 0`` iff ``n = 1``, and ``f(n) > 0`` iff ``n = 1 (mod 4)`` and ``n > 1``.
D2  (height classes) the sources at height ``x`` are one residue class mod ``2^{x+1}``, on
    which ``f_q`` is affine with slope ``1 - 3/2^x``; the drops at height ``x`` form the
    arithmetic progression ``d_0(x) + 2(2^x - 3) k``, ``k >= 0``.
D3  (fibers) odd ``n`` with ``f_q(n) = d`` correspond one-to-one to the heights ``x >= 1``
    with ``(2^x - 3) | (3d + q)``, positive quotient ``s = (3d+q)/(2^x-3)`` and
    ``n = s + d > 0``.  For ``q = 1``: every even ``d < 0`` has exactly one source,
    ``-2d - 1``; ``d = 0`` has only ``n = 1``; an even ``d > 0`` has one source for each
    divisor of ``3d + 1`` of the form ``2^x - 3`` with ``x >= 2`` (``1, 5, 13, 29, 61, ...``).
D4  the fiber size is unbounded: with ``M`` the least multiple of
    ``lcm(2^x - 3 : 2 <= x <= X)`` congruent to ``q`` mod 6, ``d = (M - q)/3`` has at
    least ``X - 1`` sources (for ``q = 1``, ``X = 7`` gives ``d = 958208`` with six).
D5  (telescoping) along any orbit ``sum f_q(n_i) = n_0 - n_end``; around a cycle the drops
    sum to 0, i.e. the rises' total ``sum (n+q)/2`` equals the falls' total.

Prior art
---------
``f`` is minus the *net* of the ledger pairs (docs/LEDGER.md section 2) and ``n - s`` in the
landing form (docs/LANDING.md).  D2 is the standard description of ``S`` on residue classes
mod ``2^{x+1}`` (Terras 1976; Lagarias 1985, section 2.1).  D3 and D4 reorganise the inverse
map ``(2^x s - q)/3`` by the drop instead of by the target; see docs/DROP.md for the
literature check.  D5 is a telescoping sum.  Nothing here is claimed as new.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import lcm

from .syracuse import check_q, syracuse_with_exponent

__all__ = [
    "two_pow_minus_3",
    "drop",
    "drop_with_exponent",
    "HeightClass",
    "height_class",
    "sources_at_height",
    "drop_fiber",
    "drop_multiplicity",
    "multiplicity_witness",
    "DropStep",
    "trajectory_drops",
    "cycle_drops",
    "rise_fall_totals",
]


def two_pow_minus_3(x: int) -> int:
    """``2^x - 3``: the coefficient of the target in ``(2^x - 3) s = 3d + q``."""
    if x < 1:
        raise ValueError("x must be >= 1")
    return (1 << x) - 3


def drop_with_exponent(n: int, q: int = 1) -> tuple[int, int]:
    """``(f_q(n), x)`` for odd ``n > 0``: the signed drop to the next odd, and its height."""
    s, x = syracuse_with_exponent(n, q)
    return n - s, x


def drop(n: int, q: int = 1) -> int:
    """``f_q(n) = n - S_q(n)``: positive on a fall, negative on a rise, 0 at a fixed point."""
    return drop_with_exponent(n, q)[0]


@dataclass(frozen=True)
class HeightClass:
    """The sources at height ``x``: one residue class mod ``2^{x+1}`` (Lemma D2).

    ``n = n0 + n_step*k``, ``s = s0 + 6k``, ``d = d0 + d_step*k`` for ``k >= 0``, with
    ``n_step = 2^{x+1}`` and ``d_step = 2(2^x - 3)``.
    """

    q: int
    x: int
    n0: int
    s0: int
    d0: int
    n_step: int
    d_step: int

    @property
    def coefficient(self) -> int:
        """``2^x - 3``."""
        return two_pow_minus_3(self.x)


def height_class(x: int, q: int = 1) -> HeightClass:
    """The arithmetic data of the sources at height ``x`` (Lemma D2).

    A target ``s`` is landed on from height ``x`` iff ``s`` is odd, ``2^x s = q (mod 3)``
    and ``2^x s > q``; so ``s = q*(-1)^x (mod 3)``, i.e. ``s`` runs through one odd class
    mod 6, and ``n = (2^x s - q)/3``, ``d = n - s = ((2^x - 3) s - q)/3``.
    """
    check_q(q)
    if x < 1:
        raise ValueError("x must be >= 1")
    r = 1 if (q * (-1) ** x) % 3 == 1 else 5
    s0 = r
    while (s0 << x) <= q:
        s0 += 6
    n0 = ((s0 << x) - q) // 3
    return HeightClass(q, x, n0, s0, n0 - s0, 1 << (x + 1), 2 * two_pow_minus_3(x))


def sources_at_height(x: int, count: int, q: int = 1) -> list[tuple[int, int, int]]:
    """The first ``count`` sources at height ``x`` as ``(n, s, d)`` triples, increasing."""
    h = height_class(x, q)
    return [(h.n0 + h.n_step * k, h.s0 + 6 * k, h.d0 + h.d_step * k) for k in range(count)]


def drop_fiber(d: int, q: int = 1) -> list[int]:
    """All odd ``n > 0`` with ``f_q(n) = d``, increasing (Lemma D3).

    ``f_q(n) = d`` with height ``x`` means ``(2^x - 3) s = 3d + q`` for the target ``s``,
    and then ``n = s + d``.  Odd ``d`` never occurs (``n`` and ``s`` are both odd).
    """
    check_q(q)
    if d % 2:
        return []
    out: list[int] = []
    # x = 1: coefficient -1, so s = -(3d + q); needs s > 0 and n = s + d = -2d - q > 0.
    s = -(3 * d + q)
    if s > 0 and s + d > 0:
        out.append(s + d)
    rhs = 3 * d + q
    x = 2
    while two_pow_minus_3(x) <= rhs:
        m = two_pow_minus_3(x)
        if rhs % m == 0:
            s = rhs // m
            if s > 0 and s + d > 0:
                out.append(s + d)
        x += 1
    return sorted(out)


def drop_multiplicity(d: int, q: int = 1) -> int:
    """The number of odd sources with drop ``d``; for ``q = 1``, ``d > 0`` even, this is the
    number of divisors of ``3d + 1`` of the form ``2^x - 3``, ``x >= 2``."""
    return len(drop_fiber(d, q))


def multiplicity_witness(x_max: int, q: int = 1) -> int:
    """The Lemma D4 drop: least ``d`` with ``(2^x - 3) | (3d + q)`` for every ``2 <= x <= x_max``.

    ``3d + q`` must be an odd multiple of ``L = lcm(2^x - 3)`` congruent to ``q`` mod 3,
    i.e. congruent to ``q`` mod 6; ``L`` is odd and prime to 3, so such a multiple exists.
    The returned ``d`` has at least ``x_max - 1`` sources.
    """
    check_q(q)
    if x_max < 2:
        raise ValueError("x_max must be >= 2")
    big = 1
    for x in range(2, x_max + 1):
        big = lcm(big, two_pow_minus_3(x))
    m = big
    while m % 6 != q % 6:
        m += big
    return (m - q) // 3


@dataclass(frozen=True)
class DropStep:
    """One odd step: source ``n`` at height ``x`` lands on ``s`` with drop ``d = n - s``."""

    n: int
    x: int
    s: int
    d: int


def trajectory_drops(n: int, q: int = 1, stop_at: int | None = None, max_steps: int = 1_000_000) -> list[DropStep]:
    """The drops along the odd orbit of ``n``.

    For ``q = 1`` the walk stops on reaching 1 (the fixed point contributes nothing).  For
    other ``q`` (or ``stop_at=None`` with ``q != 1``) it stops when the next odd number
    has been seen already, so a start inside a cycle returns exactly one lap.  Lemma D5:
    ``sum(step.d) = n - (last target)``.
    """
    check_q(q)
    if n <= 0 or n % 2 == 0:
        raise ValueError("n must be a positive odd integer")
    if stop_at is None and q == 1:
        stop_at = 1
    steps: list[DropStep] = []
    seen = {n}
    while len(steps) < max_steps:
        if stop_at is not None and n == stop_at:
            break
        s, x = syracuse_with_exponent(n, q)
        steps.append(DropStep(n, x, s, n - s))
        if stop_at is None and s in seen:
            break
        seen.add(s)
        n = s
    else:
        raise RuntimeError(f"no stop after {max_steps} odd steps")
    return steps


def cycle_drops(elements: tuple[int, ...] | list[int], q: int = 1) -> list[DropStep]:
    """The drops around one lap of a cycle given by its odd members in orbit order."""
    check_q(q)
    out = []
    for n in elements:
        s, x = syracuse_with_exponent(n, q)
        out.append(DropStep(n, x, s, n - s))
    return out


def rise_fall_totals(steps: list[DropStep]) -> tuple[int, int]:
    """``(sum of |d| over rises, sum of d over falls)``; equal around any cycle (Lemma D5)."""
    rises = sum(-st.d for st in steps if st.x == 1)
    falls = sum(st.d for st in steps if st.x >= 2)
    return rises, falls
