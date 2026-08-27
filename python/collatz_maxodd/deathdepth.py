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

ASYMPTOTICS -- UNRESOLVED.  Write ``N_k`` for the number of admissible halving
vectors (``backtree.count_admissible_halving_vectors``).  Each vector pins one
residue so ``a_k <= N_k``, and ``N_k ~ C lambda^k k^(-3/2)`` with

    lambda = a^a/(a-1)^(a-1),  a = log2 3,  lambda = 2.8395137305

CONFIRMED here to six significant figures by running that O(k^2) DP to k = 8000
(relative error 8e-6 on a joint fit for both lambda and the power).

NOT settled: whether ``a_k`` shares that rate.  ``a_k/N_k`` declines, and over
the computed range k <= 24 two models fit indistinguishably:

    polynomial   a_k/N_k ~ C k^(-0.74)   -> lambda_a = lambda,  rate 0.9465
    geometric    a_k/N_k ~ C (0.946)^k   -> lambda_a = 2.6874,  rate 0.8958

Neither leads stably -- the ranking FLIPS with one more term:

    through k = 23   polynomial ahead (R^2 0.941 vs 0.928, OOS 6.5% vs 7.6%)
    through k = 24   geometric  ahead (R^2 0.937 vs 0.934, OOS 7.1% vs 11.0%)

That reversal on a single data point is the honest result: the computed range
cannot separate them.  Separating them needs the model gap to clear the residual Sturmian
oscillation of +/-14%, which happens near k = 33 -- about 7e11 tree nodes and
two weeks of compute.  Not attempted.

So the tail rate is BRACKETED, 0.897 <= rate <= 0.947, and NOT confirmed.  An
earlier fit of 0.705 over k = 3..10 was pre-asymptotic and is wrong.

Note also: if the rate is the conjectured lambda/3 then the polynomial factor is
k^(-2.2), NOT the k^(-3/2) an earlier draft recorded, because
``a_k ~ N_k k^(-0.70) ~ lambda^k k^(-3/2-0.70)``.
"""

from __future__ import annotations

from collections import Counter
from typing import Iterator

__all__ = [
    "death_depth",
    "death_depth_congruence_only",
    "exact_tail",
    "surviving_residue_count",
    "tail_ratios",
]

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


def surviving_residue_count(K: int) -> list[int]:
    """``a_k`` for ``k = 1..K`` by DFS over the 3-adic tree of surviving residues.

    Visits ``a_k`` nodes at depth ``k`` rather than ``3^k``, so it reaches far
    deeper than :func:`exact_tail` (which scans a whole period).  The two agree
    exactly where they overlap.

    A node is ``(j, m, chains)`` with ``m = M mod 3^j`` and ``chains`` the live
    ``(B_j, c_j)`` pairs.  Extending ``M`` by a 3-adic digit ``t`` gives
    ``m' = m + 3^j t``; for each chain ``y_j = (2^B m' - c)/3^j mod 3``, where
    ``0`` kills that chain and otherwise the parity of ``b`` is forced, with
    ``b`` running over that parity subject to ``B + b <= floor((j+1) log2 3)``.

    WHY THERE IS NO FINITE TRANSFER MATRIX FOR ``a_k``.  The state governing a
    node's future is the *set* of ``(B_j, y_j mod 3)`` over its live chains.
    ``B_j`` ranges over about ``0.585 j`` values, so the number of reachable
    states grows like ``2^(1.76 j)`` -- unbounded.  ``N_k`` escapes this because
    its state is the single integer ``B_j``, which is exactly why
    ``backtree.count_admissible_halving_vectors`` gets an ``O(k^2)`` DP and this
    does not.
    """
    if K < 1:
        raise ValueError("K must be >= 1")
    pow3 = [3 ** j for j in range(K + 2)]
    cap = [(3 ** j).bit_length() - 1 for j in range(K + 2)]  # exact floor(j log2 3)
    counts = [0] * (K + 1)
    stack: list[tuple[int, int, tuple[tuple[int, int], ...]]] = [(0, 0, ((0, 0),))]
    while stack:
        j, m, chains = stack.pop()
        if j == K:
            continue
        p3, lim = pow3[j], cap[j + 1]
        for t in (0, 1, 2):
            mp = m + p3 * t
            new: list[tuple[int, int]] = []
            for B, c in chains:
                u = (((1 << B) * mp - c) // p3) % 3
                if u == 0:
                    continue
                b = 2 if u == 1 else 1          # need (-1)^b * u == 1 (mod 3)
                while B + b <= lim:
                    new.append((B + b, (1 << b) * c + p3))
                    b += 2
            if new:
                counts[j + 1] += 1
                stack.append((j + 1, mp, tuple(new)))
    return counts[1:]
