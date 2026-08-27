"""Exhaustive cycle census for ``3n+q``, and the congruence every cycle obeys.

Why this module exists.  Belief in Collatz rests on a heuristic: the expected
number of backward chains decays like ``(lambda/3)^k``, so cycles "should not"
exist.  The ``3n+q`` family is the only place that heuristic can be checked
against reality, because there cycles genuinely do exist.  This module runs that
check.  The verdict is in ``docs/CENSUS.md``: the heuristic's assumption of a
``q``-independent Poisson rate is **false**, and the reason turns out to also
explain why ``q = 1`` is special.

Finding cycles cheaply
----------------------
A cycle whose maximum is ``<= X`` lies entirely inside ``[1, X]``, so it is
enough to build the functional graph on odds ``n <= X`` with ``S_q(n) <= X`` and
read off its cycles: ``O(X)`` per ``q``, rather than following full trajectories.

Primitivity
-----------
If ``(x_i)`` is a cycle of ``3n+q`` and ``d`` is odd, ``(d x_i)`` is a cycle of
``3n+dq``.  Counting every cycle would therefore count scaled copies of smaller
systems repeatedly, so the census counts only *primitive* cycles --
``gcd(q, x_0, ..., x_{L-1}) = 1``.

The congruence (verified exactly on every cycle found)
------------------------------------------------------
    THEOREM.  For a primitive cycle with L odd elements and B total halvings,

        q  divides  2^B - 3^L        i.e.   2^B = 3^L  (mod q)

    Proof.  (a) For a prime p | q: from ``2^{a_j} x_j = 3 x_{j-1} + q``, if
    p | x_{j-1} then p | 2^{a_j} x_j, and p is odd, so p | x_j.  Going once
    around, p divides every element or none; primitivity rules out "every", so
    gcd(x_0, q) = 1.  (b) Telescoping the same relation gives the cycle equation
    ``x_0 (2^B - 3^L) = q S`` with S a positive integer.  Hence q | x_0(2^B-3^L),
    and with gcd(q, x_0) = 1, q | 2^B - 3^L.  QED

This is standard in the ``3n+q`` literature; it is reproduced here because it is
what makes the census interpretable.

PRIOR ART / NOVELTY: none claimed.  The congruence is folklore; the census and
its dispersion statistics are measurements, not theorems.
"""

from __future__ import annotations

from functools import reduce
from math import gcd

__all__ = ["cycles_upto", "primitive_cycles", "total_halvings", "satisfies_congruence",
           "exact_hits"]


def _odd_step(n: int, q: int) -> int:
    m = 3 * n + q
    while m % 2 == 0:
        m //= 2
    return m


def total_halvings(elements: list[int], q: int) -> int:
    """``B``: the total number of halvings around the cycle."""
    B = 0
    for n in elements:
        m = 3 * n + q
        while m % 2 == 0:
            m //= 2
            B += 1
    return B


def cycles_upto(q: int, X: int) -> list[tuple[int, int, list[int]]]:
    """Every cycle of ``S_q`` all of whose elements are ``<= X``.

    Returns ``(L, M, sorted elements)``.  ``O(X)`` time and memory.
    """
    if q <= 0 or q % 2 == 0 or q % 3 == 0:
        raise ValueError("q must be a positive odd integer not divisible by 3")
    half = (X + 1) // 2
    nxt = [-1] * half
    for i in range(half):
        m = _odd_step(2 * i + 1, q)
        if m <= X:
            nxt[i] = (m - 1) // 2
    color = bytearray(half)
    out = []
    for s in range(half):
        if color[s]:
            continue
        path, v = [], s
        while v != -1 and color[v] == 0:
            color[v] = 1
            path.append(v)
            v = nxt[v]
        if v != -1 and color[v] == 1:
            cyc = [2 * u + 1 for u in path[path.index(v):]]
            out.append((len(cyc), max(cyc), sorted(cyc)))
        for u in path:
            color[u] = 2
    return out


def primitive_cycles(q: int, X: int, min_length: int = 2):
    """Primitive cycles (``gcd(q, elements) == 1``) with at least ``min_length`` odd elements."""
    return [(L, M, el) for L, M, el in cycles_upto(q, X)
            if L >= min_length and reduce(gcd, el, q) == 1]


def satisfies_congruence(q: int, L: int, B: int) -> bool:
    """The theorem's conclusion: ``2^B == 3^L (mod q)``."""
    return (pow(2, B, q) - pow(3, L, q)) % q == 0


def exact_hits(q: int, max_L: int = 400) -> list[tuple[int, int]]:
    """``(L, B)`` with ``2^B - 3^L == q`` exactly.

    These are the strongest cycle-producing configurations: when ``2^B - 3^L``
    equals ``q`` itself, the cycle equation ``x_0 (2^B - 3^L) = q S`` reduces to
    ``x_0 = S``, so *every* admissible halving vector of that ``(L, B)`` yields an
    integer candidate.  One such hit can produce a burst of cycles at once.

    For ``q = 1`` this returns only ``(1, 2)`` -- the trivial cycle.  Reason:
    ``2^B = 3^L + 1`` with ``L >= 2`` forces ``3^L + 1 == 2 or 4 (mod 8)``, so
    ``2^B <= 4``.  An elementary mod-8 argument, no Catalan needed.
    """
    hits = []
    for L in range(0, max_L + 1):
        t = 3 ** L + q
        B = t.bit_length() - 1
        if (1 << B) == t:
            hits.append((L, B))
    return hits
