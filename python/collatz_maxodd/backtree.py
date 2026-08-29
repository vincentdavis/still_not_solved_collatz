"""The backward tree from a hypothetical largest odd element ``M``.

Closed form (ground truth, section "Backward from M")::

    y_k = (2^{B_k} * M - c_k) / 3^k,   c_k = 2^{b_k} * c_{k-1} + 3^{k-1} * q,  c_0 = 0
    B_k = b_1 + ... + b_k

Unrolled, ``c_k = q * sum_{j=1..k} 3^{j-1} * 2^{B_k - B_j}``.

**T6 (exact).**  ``y_k <= M``  iff  ``M * (2^{B_k} - 3^k) <= c_k``.  This module
uses that inequality *exactly*, never an asymptotic form.  It also imposes
``y_k > 0``, i.e. ``2^{B_k} * M > c_k``, which is equally forced (cycle elements
are positive).

**The refuted shortcut.**  ``B_k <= floor(k * log2 3)`` is NOT unconditional:
``c_k`` grows like ``2^{B_k}``, not ``O(1)``.  Real counterexample: the ``q=5``
cycle ``49 -> 19 -> 31 -> 49`` has ``B_3 = 5 > 4 = floor(3*log2 3)``.  The floor
rule is the *large-M limit* of the exact inequality; ``floor_rule_threshold(k)``
computes exactly how large ``M`` has to be for depth ``k``.

Prior art: the "every backward prefix satisfies a ``2^{B_k}`` vs ``3^k``
inequality" device is standard -- Kaneda (*Fibonacci Quart.* 53(2), 2015,
Thm 2.1 proof, inequality (2.3)), Eliahou (*Discrete Math.* 118 (1993) 45-56),
Halbeisen & Hungerbuehler (*Acta Arith.* 78 (1997) 227-239), Simons & de Weger
(*Acta Arith.* 117 (2005) 51-70), Hercher (*JIS* 26 (2023) Art. 23.3.5).
Nothing here is new.
"""

from __future__ import annotations

import math
from fractions import Fraction
from functools import lru_cache
from typing import Iterator, Sequence

from .syracuse import BackStep, check_q, predecessor_at

_ALPHA = math.log2(3.0)
_LAMBDA = _ALPHA ** _ALPHA / (_ALPHA - 1.0) ** (_ALPHA - 1.0)

__all__ = [
    "floor_bound",
    "c_constant",
    "c_sequence",
    "y_value",
    "size_admissible",
    "max_M_for_vector",
    "admissible_halving_vectors",
    "count_admissible_halving_vectors",
    "floor_rule_threshold",
    "floor_rule_safe_M",
    "backward_chains",
]


@lru_cache(maxsize=None)
def floor_bound(k: int) -> int:
    """``floor(k * log2 3)``, computed exactly as ``bit_length(3**k) - 1``."""
    if k < 0:
        raise ValueError("k must be >= 0")
    return (3**k).bit_length() - 1


def c_sequence(bs: Sequence[int], q: int = 1) -> list[int]:
    """``[c_1, ..., c_k]`` for the backward halving vector ``bs = (b_1, ..., b_k)``."""
    out: list[int] = []
    c = 0
    for j, b in enumerate(bs, start=1):
        c = (1 << b) * c + 3 ** (j - 1) * q
        out.append(c)
    return out


def c_constant(bs: Sequence[int], q: int = 1) -> int:
    """``c_k`` for the backward halving vector ``bs``. ``c_0 = 0``."""
    return c_sequence(bs, q)[-1] if bs else 0


def y_value(m: int, bs: Sequence[int], q: int = 1) -> Fraction:
    """``y_k = (2^{B_k} m - c_k) / 3^k`` as an exact rational.

    It is an integer exactly when a genuine backward chain with that halving
    vector exists from ``m``.
    """
    k = len(bs)
    return Fraction((1 << sum(bs)) * m - c_constant(bs, q), 3**k)


def size_admissible(m: int, bs: Sequence[int], q: int = 1) -> bool:
    """Exact T6 test at every level: ``0 < 2^{B_j} m - c_j <= 3^j m`` for all ``j <= k``.

    Left inequality is ``y_j > 0``; right inequality is ``y_j <= m``.
    No integrality is required here -- this is the pure size condition.
    """
    B = 0
    c = 0
    for j, b in enumerate(bs, start=1):
        B += b
        c = (1 << b) * c + 3 ** (j - 1) * q
        t = (1 << B) * m - c
        if t <= 0 or t > 3**j * m:
            return False
    return True


def max_M_for_vector(bs: Sequence[int], q: int = 1) -> int | None:
    """Largest ``M`` satisfying the exact T6 inequality at every level, or ``None``.

    ``None`` means "no finite upper bound from T6" (every level has
    ``2^{B_j} <= 3^j``).  A returned value ``v`` still has to be checked with
    ``size_admissible`` because the positivity constraint may make the vector
    infeasible for every ``M``.
    """
    best: int | None = None
    B = 0
    c = 0
    for j, b in enumerate(bs, start=1):
        B += b
        c = (1 << b) * c + 3 ** (j - 1) * q
        d = (1 << B) - 3**j
        if d > 0:
            cand = c // d
            best = cand if best is None else min(best, cand)
    return best


def admissible_halving_vectors(
    depth: int, q: int = 1, *, m: int | None = None
) -> Iterator[tuple[int, ...]]:
    """Enumerate backward halving vectors ``(b_1, ..., b_depth)`` allowed by T6.

    Parameters
    ----------
    m:
        If given, use the **exact** inequality ``0 < 2^{B_j} m - c_j <= 3^j m``
        for this specific ``M = m``.
        If ``None``, use the symbolic large-``M`` mode: ``B_j <= floor(j*log2 3)``
        for every ``j``.  That mode is valid for ``M > floor_rule_threshold(depth)``
        (see :func:`floor_rule_safe_M`).

    Note that in the symbolic mode ``b_1 = 1`` comes out automatically, since
    ``floor(1*log2 3) = 1``; this is T2, not an extra assumption.
    """
    check_q(q)
    if depth < 0:
        raise ValueError("depth must be >= 0")

    if m is None:
        limits = [floor_bound(j) for j in range(depth + 1)]

        def rec_sym(j: int, B: int, acc: list[int]) -> Iterator[tuple[int, ...]]:
            if j > depth:
                yield tuple(acc)
                return
            for b in range(1, limits[j] - B + 1):
                acc.append(b)
                yield from rec_sym(j + 1, B + b, acc)
                acc.pop()

        yield from rec_sym(1, 0, [])
        return

    def rec_exact(
        j: int, B: int, c: int, acc: list[int]
    ) -> Iterator[tuple[int, ...]]:
        if j > depth:
            yield tuple(acc)
            return
        # 2^b * (m*2^{B} - c) <= 3^j*m + 3^{j-1}*q, and the bracket is > 0 by
        # the positivity constraint already enforced at level j-1.
        bracket = (1 << B) * m - c
        rhs = 3**j * m + 3 ** (j - 1) * q
        b = 1
        while (1 << b) * bracket <= rhs:
            nc = (1 << b) * c + 3 ** (j - 1) * q
            if (1 << (B + b)) * m - nc > 0:
                acc.append(b)
                yield from rec_exact(j + 1, B + b, nc, acc)
                acc.pop()
            b += 1

    if m <= 0:
        return
    yield from rec_exact(1, 0, 0, [])


@lru_cache(maxsize=None)
def entropy_bound(k: int) -> float:
    """``C(floor(k*alpha), k)`` bounded by ``lambda^k``, the elementary way.

    ``C(n, k) <= n^n / (k^k (n-k)^(n-k))`` -- take ``1 = (p+q)^n >= C(n,k) p^k
    q^(n-k)`` at ``p = k/n``.  That right-hand side is increasing in ``n`` (its
    log-derivative is ``log(n/(n-k)) > 0``), and at ``n = k*alpha`` it is
    exactly ``lambda^k``.  Since ``floor(k*alpha) <= k*alpha``, the chain

        a_k  <=  N_k  <=  C(floor(k*alpha), k)  <=  lambda^k

    holds for EVERY k, with no asymptotics and no Stirling.  Returns the middle
    quantity's bound ``lambda^k``; see :func:`chain_bound_holds`.
    """
    return _LAMBDA ** k


def chain_bound_holds(k: int, a_k: int | None = None) -> bool:
    """Check ``a_k <= N_k <= C(floor(k*alpha), k) <= lambda^k`` at depth ``k``.

    This is the upper half of the rigorous bracket on the death-depth tail
    rate: it gives ``a_k^(1/k) <= lambda`` for every ``k``, hence
    ``mu = lim a_k^(1/k) <= lambda`` and rate ``<= lambda/3``.  Unlike the
    asymptotic ``N_k ~ C*lambda^k*k^(-3/2)`` recorded in GROUND_TRUTH, which is
    measured, this is a bound.  See docs/EXPLORE.md.
    """
    n = math.floor(k * _ALPHA)
    nk = count_admissible_halving_vectors(k)
    ck = math.comb(n, k)
    if a_k is not None and not a_k <= nk:
        return False
    return nk <= ck <= _LAMBDA ** k


def count_admissible_halving_vectors(depth: int) -> int:
    """``N(k)``: number of symbolic (large-``M``) admissible vectors at depth ``k``.

    Counted by dynamic programming over the partial sum ``B_j``, so this is
    usable far beyond what enumeration allows.  ``N(1..5) = 1, 2, 3, 7, 12``
    matches the ground-truth doc.  Independent of ``q`` (the floor rule is).
    """
    if depth < 0:
        raise ValueError("depth must be >= 0")
    if depth == 0:
        return 1
    # dist[B] = number of prefixes of length j with partial sum B
    dist = {1: 1}  # j = 1, floor_bound(1) == 1 forces b_1 = 1
    for j in range(2, depth + 1):
        lim = floor_bound(j)
        nxt: dict[int, int] = {}
        # prefix sums of dist to make this O(range) instead of O(range^2)
        running = 0
        for B in range(j, lim + 1):
            running += dist.get(B - 1, 0)
            if running:
                nxt[B] = running
        dist = nxt
    return sum(dist.values())


@lru_cache(maxsize=None)
def floor_rule_threshold(depth: int, q: int = 1, cap: int = 10**6) -> int:
    """Largest ``M <= cap`` for which ``B_depth > floor(depth*log2 3)`` is T6-admissible.

    For ``M`` strictly larger than this value, the exact T6 inequality at depth
    ``depth`` is equivalent to the floor rule ``B_depth <= floor(depth*log2 3)``.

    For ``q = 1`` this is ``1, 9, 7, 86, 23, ...`` for ``depth = 2, 3, 4, 5, 6``.
    Values computed with this function (``q = 1``, ``cap = 10**6``)::

        k    1   2   3   4   5   6   7   8   9  10  11  12   13   14    15    16     17    18    19
        thr  1   1   9   7  86  23  22  82  62 381 175 173  538  450  2012  1219  17344  3536  3219

    So the running maximum over ``k <= 19`` is ``17344 < 2^14.1``, attained at
    ``k = 17`` -- far below the ``2^68`` quoted in the ground-truth doc, which is
    wildly over-conservative.  The sequence is *not* monotone, so nothing is
    claimed about ``k > 19``; recompute if you need a deeper guarantee.

    ``cap`` bounds the search; the answer is exact whenever the true threshold is
    ``<= cap``.  Raise ``cap`` if the returned value equals it.  The search is
    exponential in ``depth``: ``k = 16`` takes ~20 s and ``k = 18`` ~3 min here.
    """
    check_q(q)
    if depth < 1:
        raise ValueError("depth must be >= 1")
    limit = floor_bound(depth)
    best = 0

    # DFS over (B_j, c_j) carrying an integer interval [lo, hi] of still-possible M.
    #   positivity  y_j > 0   <=>  M >= floor(c_j / 2^{B_j}) + 1      (raises lo)
    #   T6          y_j <= M  <=>  M <= c_j / (2^{B_j} - 3^j)         (lowers hi,
    #                                only binds when 2^{B_j} > 3^j)
    # hi starts at `cap`: levels with 2^{B_j} <= 3^j give no upper bound at all,
    # so the search has to be capped from outside rather than by the inequality.
    def rec(j: int, B: int, c: int, lo: int, hi: int) -> None:
        nonlocal best
        if j > depth:
            if B > limit and hi >= lo and hi > best:
                best = hi
            return
        b = 1
        while True:
            nB = B + b
            nc = (1 << b) * c + 3 ** (j - 1) * q
            d = (1 << nB) - 3**j
            if d > 0:
                cand = nc // d
                if cand < lo:
                    # nc/d is strictly decreasing in b from here on, so no larger
                    # b can succeed either.
                    break
                nhi = min(hi, cand)
            else:
                nhi = hi
            nlo = max(lo, nc // (1 << nB) + 1)
            if nhi >= nlo:
                rec(j + 1, nB, nc, nlo, nhi)
            b += 1

    rec(1, 0, 0, 1, cap)
    return best


@lru_cache(maxsize=None)
def floor_rule_safe_M(max_depth: int, q: int = 1) -> int:
    """``max(floor_rule_threshold(k) for k <= max_depth)``.

    For ``M`` strictly greater than this, the floor rule and the exact T6
    inequality agree for every depth ``k <= max_depth``.
    """
    return max(floor_rule_threshold(k, q) for k in range(1, max_depth + 1))


def backward_chains(
    m: int, q: int = 1, depth: int = 1, *, bound: int | None = None
) -> Iterator[tuple[BackStep, ...]]:
    """Enumerate genuine integer backward chains ``y_1, ..., y_depth`` from ``y_0 = m``.

    Every ``y_j`` must be a positive odd integer with ``y_j <= bound`` (default
    ``bound = m``, the exact cycle-maximality condition) and ``3 | y_j`` false
    (T0).  This is the honest unconditional necessary condition for ``m`` to be
    the largest odd element of an ``S_q``-cycle: no asymptotics, and in
    particular *no* assumption that ``b_1 = 1``.
    """
    check_q(q)
    lim = m if bound is None else bound

    def rec(cur: int, k: int, acc: list[BackStep]) -> Iterator[tuple[BackStep, ...]]:
        if k == 0:
            yield tuple(acc)
            return
        b = 1
        while (1 << b) * cur <= 3 * lim + q:
            y = predecessor_at(cur, b, q)
            if y is not None and y <= lim and y % 3 != 0:
                acc.append(BackStep(b, y))
                yield from rec(y, k - 1, acc)
                acc.pop()
            b += 1

    yield from rec(m, depth, [])
