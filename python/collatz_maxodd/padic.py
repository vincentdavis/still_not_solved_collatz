"""Why a congruence sieve can never finish -- with an explicit witness.

Everything else in this package establishes that some sieve or other *cannot*
close the problem, usually by measuring a density that fails to reach zero.
This module says why, concretely, and without any analysis.

Periodic points
---------------
Run the backward map with a fixed halving pattern ``(b_1, ..., b_L)`` and ask for
a fixed point.  Telescoping gives exactly one, and it is a rational:

    y  =  c_L / (2^B - 3^L)        with   c_L = sum_j 3^(j-1) 2^(...) q

That is the **cycle equation**.  So the periodic points of the backward map are
precisely the candidate cycles, one per halving pattern, and a genuine cycle is
a periodic point that happens to land on a **positive integer**.
:func:`periodic_point` reproduces all 136 real ``3n+q`` cycles in the census
exactly from their halving vectors alone.

The witness
-----------
Take the pattern with every ``b_j = 1``.  Then ``3y = 2y - 1``, so ``y = -1``,
for every length ``L``.  In ``Z_3`` the number ``-1`` is ``...2222``: it is
``= 2 (mod 3^k)`` for every ``k``, which is exactly the parity condition an odd
``b`` needs at every step.  So:

    the class  -1 (mod 3^k)  survives the backward sieve at EVERY depth

hence ``a_k >= 1`` for all ``k``, provably, with a witness -- the sieve can never
empty.  And ``-1`` is not a natural number.

Constant patterns give ``y = q/(2^b - 3)``:

    b = 1  ->  -q          b = 2  ->  q         b = 3  ->  q/5   ...

For ``q = 1``, ``b = 2`` gives ``1``: the trivial cycle, and the only constant
pattern whose periodic point is a positive integer.

The point
---------
A congruence sieve tests membership in ``Z_3``.  It cannot see **sign** or
**integrality**.  The limit set is full of 3-adic points like ``-1`` and ``1/5``
that pass every congruence test and are not natural numbers.  Collatz is the
statement that no periodic point other than ``1`` lands on a positive integer --
and that is not a congruence question at all.

PRIOR ART / NOVELTY: none claimed.  The rational form of a cycle is
Boehm-Sontacchi (1978); the 3-adic reading is standard.  This module records it
because it is the cleanest available answer to "why can't the sieve finish".
"""

from __future__ import annotations

from fractions import Fraction

__all__ = ["periodic_point", "constant_pattern_point", "minus_one_survives"]


def periodic_point(halvings: list[int] | tuple[int, ...], q: int = 1) -> Fraction:
    """The unique fixed point of the backward chain with this halving pattern.

    ``c_L / (2^B - 3^L)`` -- the cycle equation.  A genuine cycle is one of these
    that lands on a positive integer.
    """
    bs = list(halvings)
    if not bs or any(b < 1 for b in bs):
        raise ValueError("halvings must be a non-empty list of positive integers")
    L, B = len(bs), sum(bs)
    if (1 << B) == 3 ** L:
        raise ValueError("2^B = 3^L is impossible for B, L >= 1")
    c = 0
    for j, b in enumerate(bs, 1):
        c = (1 << b) * c + 3 ** (j - 1) * q
    return Fraction(c, (1 << B) - 3 ** L)


def constant_pattern_point(b: int, q: int = 1) -> Fraction:
    """``q / (2^b - 3)`` -- the periodic point of the all-``b`` pattern.

    ``b = 1`` gives ``-q``; ``b = 2`` gives ``q``.  For ``q = 1`` that second one
    is the trivial cycle, and it is the only constant pattern landing on a
    positive integer.
    """
    if b < 1:
        raise ValueError("b must be >= 1")
    if (1 << b) == 3:
        raise ValueError("2^b = 3 is impossible")
    return Fraction(q, (1 << b) - 3)


def minus_one_survives(k: int, q: int = 1) -> bool:
    """Is the class ``-1 (mod 3^k)`` alive in the magnitude-free backward sieve?

    Always True for ``q = 1``: ``-1`` is the fixed point of the all-``b=1``
    chain, and ``-1 = 2 (mod 3^k)`` supplies the odd-``b`` parity at every step.
    This is the explicit witness that ``a_k >= 1``, i.e. that the sieve never
    empties.
    """
    from .certify import class_is_certified
    return not class_is_certified(3 ** k - 1, k, q)
