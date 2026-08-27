"""``d(M)`` -- the depth at which the backward sieve eliminates ``M``.

Definition
----------
``d(M)`` is the length of the longest backward chain starting at ``M`` whose
every element is a positive odd integer ``<= M``::

    M = y_0,  y_1,  y_2,  ...    with    S_q(y_{j+1}) = y_j    and    y_j <= M

"``M`` survives the backward sieve at depth ``k``" means ``d(M) >= k``.

Why it matters
--------------
``Collatz/Equivalence.lean`` proves that an *infinite* such chain exists exactly
when a nontrivial cycle does.  So a counterexample to Collatz is precisely an
odd ``M > 1`` with ``d(M) = infinity``, and a uniform bound on ``d`` would
settle the conjecture.  This module measures how ``d`` is distributed; it proves
nothing.

The exact result
----------------
For ``M`` large enough that the size test is in its asymptotic regime,
``d(M)`` depends **only on ``M mod 3^k``**, so the tail is an exact rational::

    P(d >= k) = a_k / 3^k

with ``a_k`` computed exactly by :func:`exact_tail` (no sampling): scanning
``3^K`` consecutive odd numbers hits every residue mod ``3^K`` exactly once,
because 2 is invertible mod ``3^K``.

    a_k = 1, 2, 3, 6, 10, 22, 50, 104, 254, 538, 1302, 3202, 7553, 19206, ...

PRIOR ART / NOVELTY.  The backward tree and its growth constant are standard
(see ``backtree``).  This particular counting sequence was not found in OEIS
(checked 2026-08-26, full sequence and prefixes).  That is weak evidence it has
not been tabulated -- NOT evidence that anything here is new mathematics.

CONJECTURE (not proved, not measured to convergence).  The ratios
``a_k / a_{k-1}`` appear to approach the backward-tree growth constant
``lambda = a^a / (a-1)^(a-1)`` with ``a = log2 3`` (``lambda ~ 2.83951``), giving

    P(d >= k) ~ C * (lambda/3)^k * k^(-3/2),    lambda/3 ~ 0.94650

At ``k = 14`` the observed ratio is only ``2.54``, so this is a well-motivated
extrapolation, not a result.  An earlier fit of ``0.705`` over ``k = 3..10`` was
simply pre-asymptotic and is wrong.
"""

from __future__ import annotations

from collections import Counter
from typing import Iterator

__all__ = ["death_depth", "death_depth_congruence_only", "exact_tail", "tail_ratios"]

_CAP = 900


def death_depth(M: int, q: int = 1, cap: int = _CAP) -> int:
    """Longest backward chain from ``M`` with every element ``<= M``.

    Uses the exact size test (``y <= M``), not the asymptotic approximation.
    Returns ``cap`` if the chain reaches ``cap`` -- which, by the equivalence
    theorem, would indicate a cycle.
    """
    if M <= 0 or M % 2 == 0:
        raise ValueError("M must be a positive odd integer")
    best, stack = 0, [(M, 0)]
    while stack:
        y, d = stack.pop()
        if d > best:
            best = d
        if d >= cap:
            return cap
        if y % 3 == 0:
            continue
        b = 2 if (y % 3) == (q % 3) else 1
        while True:
            num = (1 << b) * y - q
            if num <= 0:
                b += 2
                continue
            z, r = divmod(num, 3)
            if z > M:
                break
            if r == 0:
                stack.append((z, d + 1))
            b += 2
    return best


def death_depth_congruence_only(M: int, cap: int = _CAP) -> int:
    """``d(M)`` with the size test on ``M`` dropped, keeping only ``2^{B_k} <= 3^k``.

    This is the magnitude-free model.  Agreeing with :func:`death_depth` for
    large ``M`` is what explains why the distribution does not depend on the
    size of ``M``.
    """
    best, stack = 0, [(M, 0, 0)]
    while stack:
        y, d, B = stack.pop()
        if d > best:
            best = d
        if d >= cap:
            return cap
        if y % 3 == 0:
            continue
        b = 2 if y % 3 == 1 else 1
        while True:
            if (1 << (B + b)) > 3 ** (d + 1):
                break
            num = (1 << b) * y - 1
            z, r = divmod(num, 3)
            if r == 0 and z > 0:
                stack.append((z, d + 1, B + b))
            b += 2
    return best


def exact_tail(K: int = 12, base: int = 10 ** 18) -> list[int]:
    """Exact ``a_k`` for ``k = 1..K``, where ``P(d >= k) = a_k / 3^k``.

    Scans one full period: ``3^K`` consecutive odd numbers starting just above
    ``base``.  Since 2 is invertible mod ``3^K`` this hits every residue mod
    ``3^K`` exactly once, so the counts are exact, not sampled.

    Raises ``ValueError`` if a count is not divisible by ``3^(K-k)`` -- that
    would mean ``d`` does not depend on the residue alone, i.e. ``base`` is too
    small for the asymptotic regime.
    """
    start = base + 1 if base % 2 == 0 else base
    counts: Counter[int] = Counter()
    for i in range(3 ** K):
        counts[death_depth(start + 2 * i)] += 1

    out: list[int] = []
    for k in range(1, K + 1):
        cnt = sum(v for d, v in counts.items() if d >= k)
        a_k, rem = divmod(cnt, 3 ** (K - k))
        if rem:
            raise ValueError(
                f"count for k={k} is not divisible by 3^{K-k}: base={base} is "
                "too small for the asymptotic regime"
            )
        out.append(a_k)
    return out


def tail_ratios(a: list[int]) -> Iterator[float]:
    """``a_k / a_{k-1}`` -- conjectured to approach ``2.83951``."""
    for prev, cur in zip(a, a[1:]):
        yield cur / prev
