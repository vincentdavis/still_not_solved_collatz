"""Structural constraints on a cycle, given its maximum.

Three results, all elementary, all checked against every cycle in the census.

1.  ``L <= |R(O)|``  (:func:`reachable_set`, :func:`max_cycle_length`)
    A cycle with maximum ``O`` lies entirely inside the set reachable *backward*
    from ``O`` without ever exceeding ``O``.  So its length is bounded by the
    size of that set.

    Computing ``R(O)`` with a VISITED SET rather than enumerating chains always
    terminates -- even when a cycle exists -- because the set is finite.

    On ordinary inputs it is NOT faster than ``certify.backward_depth``: the
    backward tree usually dies before any value is revisited, so the visited set
    is pure overhead (measured: 0.91x, identical work).  Its advantage is
    conclusiveness.  On a genuine cycle maximum ``backward_depth`` runs until it
    hits its cap and returns nothing usable, whereas ``reachable_set`` stops by
    itself and hands back a finite bound.  For ``q = 5, O = 49`` that is 10
    against a capped non-answer.

2.  ``L_up >= log(O/m) / log((3 + q/m)/2)``  (:func:`ascent_bound`)
    Going forward from the minimum ``m`` up to the maximum ``O``, every factor
    ``(3 + q/x)/2^b`` is at most ``(3 + q/m)/2``, so the climb cannot be quick.
    For large ``m`` that is ``L_up >= 1.71 log2(O/m)``.

    The descent has no matching bound -- a single large halving can undo many
    small climbs, and in 17 of the 77 census cycles the maximum drops to the
    minimum in one step.  The two halves of a cycle are structurally different.

3.  ``u >= 2L - B``  (:func:`single_halving_bound`)
    where ``u`` counts the steps with exactly one halving.  Immediate from
    ``B = u + sum_{b>=2} b >= u + 2(L - u)``.

    For ``q = 1`` the min-max sandwich pins ``B/L`` into
    ``[log2 3, log2(3 + 1/m)]``, so ``u >= (2 - log2 3) L = 0.415 L``:
    **at least 41.5% of the steps of a hypothetical Collatz cycle must be single
    halvings.**

PRIOR ART / NOVELTY: none claimed.  These are one-line consequences of the same
squeeze used throughout; they are recorded because they are checkable and
because (1) gives a better algorithm than the one this package started with.
"""

from __future__ import annotations

import math

__all__ = ["reachable_set", "max_cycle_length", "ascent_bound",
           "single_halving_bound", "min_single_halving_fraction"]


def reachable_set(O: int, q: int = 1) -> set[int]:
    """Every odd ``x`` with a backward chain ``O <- ... <- x`` staying ``<= O``.

    Always terminates: the set is finite because it lies in ``[1, O]``.
    """
    if O <= 0 or O % 2 == 0:
        raise ValueError("O must be a positive odd integer")
    seen, stack = {O}, [O]
    while stack:
        y = stack.pop()
        if y % 3 == 0:
            continue
        b = 2 if (y % 3) == (q % 3) else 1
        while True:
            num = (1 << b) * y - q
            if num <= 0:
                b += 2
                continue
            z, r = divmod(num, 3)
            if z > O:
                break
            if r == 0 and z not in seen:
                seen.add(z)
                stack.append(z)
            b += 2
    return seen


def max_cycle_length(O: int, q: int = 1) -> int:
    """``|R(O)|`` -- an upper bound on the length of any cycle with maximum ``O``."""
    return len(reachable_set(O, q))


def ascent_bound(m: int, O: int, q: int = 1) -> float:
    """Least number of odd steps to climb from the minimum ``m`` to the maximum ``O``."""
    if not 0 < m <= O:
        raise ValueError("need 0 < m <= O")
    if m == O:
        return 0.0
    return math.log(O / m) / math.log((3 + q / m) / 2)


def single_halving_bound(L: int, B: int) -> int:
    """Least number of steps with exactly one halving: ``max(0, 2L - B)``."""
    return max(0, 2 * L - B)


def min_single_halving_fraction(m: int, q: int = 1) -> float:
    """For a cycle with minimum ``m``, the least possible share of single halvings.

    The sandwich forces ``B/L <= log2(3 + q/m)``, so ``u/L >= 2 - log2(3 + q/m)``.
    For ``q = 1`` and large ``m`` this tends to ``2 - log2 3 = 0.415``.
    """
    return 2.0 - math.log2(3 + q / m)
