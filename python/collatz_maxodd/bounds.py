"""The MINIMUM of a cycle, and how it pairs with the maximum.

The project's theorems T1–T8 all constrain the maximum.  The minimum obeys an
exact mirror image, and pairing the two ends gives a quantity that must land
*inside* the cycle.

The mirror
----------
Let ``m`` be the minimum odd element of an ``S_q``-cycle, with ``m > q``.

* **out of m**: ``S_q(m) >= m`` forces ``2^b <= 3 + q/m < 4``, so ``b = 1`` --
  the minimum ascends by a single halving, and ``(3m+q)/2`` must be odd, i.e.
  ``3m + q = 2 (mod 4)``.  For ``q = 1``: ``m = 3 (mod 4)``.
* **into m**: a predecessor ``y >= m`` forces ``2^a >= 3 + q/m``, so ``a >= 2``.
* ``3`` does not divide ``m`` (T0 applies to every element).

For ``q = 1`` that gives ``m = 7 or 11 (mod 12)``, against ``M = 5 (mod 12)``:

===========  ==========  ===========  =========================
   end        hop in      hop out      residue (q = 1)
===========  ==========  ===========  =========================
 maximum      1 halving   >= 2         M = 1 (mod 4), 5 (mod 12)
 minimum      >= 2        1 halving    m = 3 (mod 4), 7 or 11 (mod 12)
===========  ==========  ===========  =========================

Verified: 0 violations over every primitive cycle in the census.

The sandwich
------------
From ``2^B = prod (3 + q/x_j)`` and ``m <= x_j <= M``,

    (3 + q/M)^L  <=  2^B  <=  (3 + q/m)^L

Taking logs with ``d = B - L*log2(3) > 0`` and ``K = 1/(3 ln 2)``:

    K q L / M  <=  d  <=  K q L / m        hence        m  <=  K q L / d  <=  M

So :func:`scale` -- computed from ``(q, L, B)`` alone -- must land between the
cycle's minimum and maximum.  Verified: 0 violations over the census.
(``q = 47`` is a good illustration: five distinct cycles share ``L = 4, B = 7``
and hence one scale ``136.95``, and every one of them straddles it.)

Certifying from either end
--------------------------
Every cycle has both a minimum and a maximum, so refuting either kills it:

* :func:`drops_below` -- ``e(m)``, forward steps until the orbit falls below
  ``m``.  Finite means ``m`` is not a cycle minimum.  Deterministic, no
  branching; this is the classic convergence test.
* ``certify.backward_depth`` -- ``d(M)``.  Finite means ``M`` is not a cycle
  maximum.

Both certify "no cycle lies entirely below X".  Measured over 200 000 odd
numbers from ``10^7``: min side 698 192 work units, max side 414 293 -- the
**max side is 1.7x cheaper**.  Half of all odd numbers are refuted as minima in
a single step, which is exactly the ``m = 1 (mod 4)`` half that descends.

PRIOR ART / NOVELTY: none claimed.  The mirror constraints are the same one-line
arguments as T1/T2 read at the other end, and the squeeze is the standard one.
"""

from __future__ import annotations

import math

__all__ = ["can_be_min_odd", "min_residues_mod12", "scale", "sandwich_holds",
           "drops_below"]

_K = 1.0 / (3.0 * math.log(2.0))


def _v2(n: int) -> int:
    b = 0
    while n % 2 == 0:
        n //= 2
        b += 1
    return b


def can_be_min_odd(m: int, q: int = 1) -> bool:
    """Can ``m`` be the smallest odd element of an ``S_q``-cycle with ``m > q``?

    Applies the mirror conditions: coprime to 3, a single halving out, and that
    single halving landing on an odd number (``3m + q = 2 mod 4``).
    """
    if m <= 0 or m % 2 == 0:
        return False
    if m % 3 == 0:
        return False
    return (3 * m + q) % 4 == 2 and _v2(3 * m + q) == 1


def min_residues_mod12(q: int = 1) -> tuple[int, ...]:
    """The residues mod 12 a cycle minimum may occupy.  ``q = 1``: ``(7, 11)``."""
    return tuple(r for r in range(12) if r % 2 == 1 and r % 3 != 0
                 and (3 * r + q) % 4 == 2)


def scale(q: int, L: int, B: int) -> float:
    """``K q L / d`` with ``d = B - L log2 3``.  Must satisfy ``m <= scale <= M``.

    Raises ``ValueError`` if ``2^B <= 3^L``, which no cycle can have.
    """
    d = B - L * math.log2(3.0)
    if d <= 0:
        raise ValueError("2^B must exceed 3^L for a cycle")
    return _K * q * L / d


def sandwich_holds(q: int, L: int, B: int, m: int, M: int) -> bool:
    """Is the scale actually between the minimum and the maximum?"""
    return m <= scale(q, L, B) <= M


def drops_below(m: int, q: int = 1, cap: int = 10 ** 6) -> int:
    """``e(m)``: forward odd-steps until the orbit falls below ``m``.

    A finite value refutes ``m`` as a cycle minimum.  Returns ``-1`` if the cap
    is reached without dropping (which, for ``q = 1``, would be a cycle).
    """
    x, w = m, 0
    while w <= cap:
        y = 3 * x + q
        while y % 2 == 0:
            y //= 2
        x = y
        w += 1
        if x < m:
            return w
    return -1
