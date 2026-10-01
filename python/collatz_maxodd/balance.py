"""Loops near perfect balance: the cycle equation in the field Q(2^(1/L)).

Classical Collatz, ``q = 1``.  A loop with ``L`` odd members and ``B`` halvings has halving word
``w = (x_0, ..., x_{L-1})`` and first member ``c(w)/d`` with ``c(w) = sum_i 3^(L-1-i) 2^(X_i)``,
``X_i = x_0 + ... + x_{i-1}``, ``d = 2^B - 3^L`` (Boehm-Sontacchi).  Proofs: ``docs/BALANCE.md``.

* **Reformulation.**  If ``gcd(L, B) = 1`` and ``theta^L = 2``, then ``Z[theta]/(theta^B - 3)``
  is ``Z/d`` with ``theta -> theta0 = 3^u 2^(-v)`` (``uB - vL = 1``), and
  ``c(w) = theta^(B(L-1)) * A(w)  (mod d)``, ``A(w) = sum_i theta^(-D_i)``, ``D_i = iB - L X_i``.
  So ``d | c(w)`` iff ``P_w(theta) := theta^(max D) A(w)`` lies in ``(theta^B - 3)``, and then
  ``d`` divides the norm ``N(P_w(theta))`` -- a necessary condition we call the norm test.
* **Balanced words** (Christoffel words, ``X_i = floor(iB/L)``): ``A = theta^(1-L)/(theta - 1)``
  is a unit, so ``gcd(c, d) = 1``: never integral unless ``d = 1``.  Non-integrality is
  Knight's theorem ("Collatz high cycles do not exist", Discrete Math. 2026); this is a
  second proof.
* **One swap from balance.**  Exchanging two cyclically adjacent distinct letters of the
  Christoffel word reduces, up to units modulo ``(theta^B - 3)``, to
  ``gamma_e = theta^(e+1) - theta^e + 1`` (a ``12 -> 21`` swap, ``0 <= e <= L-1-b``) or
  ``eta_k = theta^k - theta + 1`` (a ``21 -> 12`` swap, ``2 <= k <= L-b``), ``b = B - L``.
  Parseval gives ``|N| <= (41/9)^(L/2)``; Ellison gives ``d > 2.56^L`` for ``L >= 18``; so
  ``d`` cannot divide the norm: no such loop.
* **Two swaps from balance.**  Two swaps move two distinct corners of the staircase by one
  step each.  Up to units the loop condition becomes ``q in (theta^B - 3)`` for a five-term
  ``q`` (families raise-raise, lower-lower, raise-lower).  Parseval, after multiplying the
  raise-lower family by ``1 + theta/2``, gives ``|N(q)| <= 4 G^(L/2) / (1 - 2^(1-L))`` with
  ``G <= 0.9404 * 4^(B/L)``, and ``G <= 8.463`` at ``B = floor(L log2 3) + 1``.  That is below
  ``d`` for every larger ``B`` once ``L >= 100`` and, by Rhin's bound
  ``B log 2 - L log 3 >= B^(-13.3)``, at the smallest ``B`` once ``L >= 4000``.  The finitely
  many remaining slopes are checked exactly (``two_swap_direct``).  Size alone cannot go on
  to three swaps: some three-swap elements have norms larger than ``d``.
"""

from __future__ import annotations

import cmath
import math
from math import gcd

__all__ = [
    "LOG2_3",
    "christoffel",
    "cycle_numerator",
    "theta0",
    "one_swaps",
    "swap_element",
    "word_element",
    "norm_exact",
    "odd_part",
    "norm_test",
    "log_norm_numeric",
    "parseval_log_bound",
    "PARSEVAL_RATE",
    "ELLISON_BASE",
    "spread_threshold",
    "corner_level",
    "two_swaps",
    "two_swap_element",
    "flatten",
    "parseval_mass",
    "two_swap_mass_bounds",
    "two_swap_log_norm_bound",
    "two_swap_direct",
    "move_word",
    "two_swap_loops",
    "level_sum_mod_d",
    "rhin_log_d",
    "RHIN_FROM",
]

LOG2_3 = math.log2(3)
#: (1/2) log(41/9): the Parseval rate bound for every one-swap element
PARSEVAL_RATE = 0.5 * math.log(41 / 9)
#: Knight's Lemma 3.3 (from Ellison 1971): 2^B - 3^L > 2.56^L when 2^B > 3^L and L > 17
ELLISON_BASE = 2.56


def christoffel(L: int, B: int) -> tuple[int, ...]:
    """Lower Christoffel word of slope ``B/L``: ``x_i = floor((i+1)B/L) - floor(iB/L)``."""
    if L < 1 or gcd(L, B) != 1:
        raise ValueError("need L >= 1 and gcd(L, B) = 1")
    return tuple(((i + 1) * B) // L - (i * B) // L for i in range(L))


def cycle_numerator(w: tuple[int, ...] | list[int]) -> int:
    """``c(w) = sum_i 3^(L-1-i) 2^(X_i)``."""
    L = len(w)
    c = X = 0
    for i, x in enumerate(w):
        c += 3 ** (L - 1 - i) * 2**X
        X += x
    return c


def _egcd(a: int, b: int) -> tuple[int, int, int]:
    if b == 0:
        return a, 1, 0
    g, x, y = _egcd(b, a % b)
    return g, y, x - (a // b) * y


def theta0(L: int, B: int) -> int:
    """Image of ``theta`` in ``Z/d``: ``3^u 2^(-v) mod d`` with ``uB - vL = 1``."""
    d = 2**B - 3**L
    if d <= 0 or gcd(L, B) != 1:
        raise ValueError("need 2^B > 3^L and gcd(L, B) = 1")
    _, u, v = _egcd(B, L)
    v = -v
    t3 = pow(3, u, d) if u >= 0 else pow(pow(3, -u, d), -1, d)
    t2 = pow(pow(2, v, d), -1, d) if v >= 0 else pow(2, -v, d)
    return t3 * t2 % d


def one_swaps(L: int, B: int) -> list[tuple[int, str, int, tuple[int, ...]]]:
    """Internal adjacent swaps of the lower Christoffel word as ``(i, kind, param, word)``.

    For ``kind = "12->21"`` the parameter is ``e = L - 1 - D_{i+1}``; for ``"21->12"`` it is
    ``k = D_{i+1} + 1``; ``D_{i+1} = (i+1)B mod L``.  The cyclic swap of the last and first
    letters yields the upper Christoffel word, a rotation of the balanced word, and is omitted.
    """
    w = christoffel(L, B)
    out = []
    for i in range(L - 1):
        if w[i] == w[i + 1]:
            continue
        v = list(w)
        v[i], v[i + 1] = v[i + 1], v[i]
        D = ((i + 1) * B) % L
        if w[i] < w[i + 1]:
            out.append((i, "12->21", L - 1 - D, tuple(v)))
        else:
            out.append((i, "21->12", D + 1, tuple(v)))
    return out


def swap_element(kind: str, param: int) -> dict[int, int]:
    """``{exponent: coefficient}`` of ``gamma_e`` (12->21) or ``eta_k`` (21->12) in ``theta``."""
    if kind == "12->21":
        e = param
        return {1: 1} if e == 0 else {e + 1: 1, e: -1, 0: 1}
    if kind == "21->12":
        k = param
        return {k: 1, 1: -1, 0: 1}
    raise ValueError(kind)


def word_element(w: tuple[int, ...] | list[int], B: int | None = None) -> dict[int, int]:
    """``P_w(theta) = sum_i theta^(Dmax - D_i)`` with ``D_i = iB - L X_i`` (exponents not reduced)."""
    L = len(w)
    B = sum(w) if B is None else B
    X, D = 0, []
    for i, x in enumerate(w):
        D.append(i * B - L * X)
        X += x
    top = max(D)
    out: dict[int, int] = {}
    for Di in D:
        out[top - Di] = out.get(top - Di, 0) + 1
    return out


def norm_exact(coeffs: dict[int, int], L: int) -> int:
    """``N_{K/Q}(sum c_m theta^m)``, ``theta^L = 2``: determinant of multiplication on the basis
    ``1, theta, ..., theta^(L-1)`` (exact, fraction-free Bareiss elimination)."""
    M = [[0] * L for _ in range(L)]
    for i in range(L):
        for m, c in coeffs.items():
            E = m + i
            M[E % L][i] += c * 2 ** (E // L)
    sign, prev = 1, 1
    for k in range(L - 1):
        if M[k][k] == 0:
            for r in range(k + 1, L):
                if M[r][k] != 0:
                    M[k], M[r] = M[r], M[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, L):
            for j in range(k + 1, L):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[L - 1][L - 1]


def odd_part(n: int) -> int:
    n = abs(n)
    while n and n % 2 == 0:
        n //= 2
    return n


def norm_test(w: tuple[int, ...] | list[int]) -> bool:
    """True when the norm test alone proves ``d`` does not divide ``c(w)`` (coprime ``L, B``,
    ``2^B > 3^L``): the odd part of ``N(P_w(theta))`` is positive and smaller than ``d``."""
    L, B = len(w), sum(w)
    d = 2**B - 3**L
    n = odd_part(norm_exact(word_element(w), L))
    return 0 < n < d


def log_norm_numeric(coeffs: dict[int, int], L: int) -> float:
    """``log |N| = sum_j log |P(zeta^j 2^(1/L))|`` in floating point."""
    th = 2 ** (1 / L)
    s = 0.0
    for j in range(L):
        z = cmath.exp(2j * math.pi * j / L) * th
        s += math.log(abs(sum(c * z**p for p, c in coeffs.items())))
    return s


def parseval_log_bound(coeffs: dict[int, int], L: int) -> float:
    """Parseval + AM-GM: ``log|N| <= (L/2) log(sum |c_m|^2 2^(2m/L))`` for distinct ``m < L``."""
    if any(m >= L for m in coeffs):
        raise ValueError("exponents must be below L")
    return 0.5 * L * math.log(sum(c * c * 4 ** (m / L) for m, c in coeffs.items()))


def spread_threshold() -> float:
    """``2^R`` with ``R + (2^R - 1)/(12 ln 2) = 1``: a positive loop with ``M/m`` below it is balanced."""
    lo, hi = 0.0, 1.0
    for _ in range(80):
        mid = (lo + hi) / 2
        if mid + (2**mid - 1) / (12 * math.log(2)) < 1:
            lo = mid
        else:
            hi = mid
    return 2**lo


# ----------------------------------------------------------------------------- two swaps


def corner_level(L: int, B: int, p: int) -> int:
    """Level ``D_p = pB mod L`` of corner ``p`` of the lower Christoffel word.  Corner ``p`` sits
    between the letters ``x_(p-1)`` and ``x_p`` (cyclically; corner 0 between ``x_(L-1)`` and
    ``x_0``); it is a ``21`` corner for ``D < L-b``, ``22`` for ``L-b <= D < b``, ``12`` for ``D >= b``."""
    return (p * B) % L


def two_swaps(L: int, B: int) -> list[tuple[int, int, int, int, tuple[int, ...]]]:
    """Words two swaps from the lower Christoffel word, as ``(p1, s1, p2, s2, word)``.

    A swap of two adjacent different letters moves exactly one corner of the staircase by one
    step, so two swaps that do not undo each other move two distinct corners ``p1 < p2``.
    ``s = +1`` raises corner ``p`` (``x_(p-1) += 1``, ``x_p -= 1``), ``s = -1`` lowers it; only
    moves keeping every letter in ``{1, 2}`` are listed.  Rotations are not identified.
    """
    w = christoffel(L, B)
    out = []
    for p1 in range(L):
        for p2 in range(p1 + 1, L):
            for s1 in (1, -1):
                for s2 in (1, -1):
                    v = list(w)
                    for p, sg in ((p1, s1), (p2, s2)):
                        v[p - 1] += sg
                        v[p] -= sg
                    if all(x in (1, 2) for x in v):
                        out.append((p1, s1, p2, s2, tuple(v)))
    return out


def two_swap_element(L: int, B: int, p1: int, s1: int, p2: int, s2: int) -> tuple[str, dict[int, int]]:
    """Family and element ``q = theta^K (theta - 1) theta^(L-1) A(w)`` of a two-corner move.

    With ``e = L-1-D`` for a raised corner and ``k = D+1`` for a lowered one (``K`` = largest
    ``k``, or 0):  RR ``1 + sum (theta^(e+1) - theta^e)``;  LL ``theta^K + sum (theta^(K-k) -
    theta^(K-k+1))``;  RL ``1 - theta + theta^k - theta^t + theta^(t+1)``, ``t = k + e``.
    The suffix ``adj`` marks cyclically adjacent corners.  ``d | c(w)`` iff ``q in (theta^B - 3)``.
    """
    pairs = ((corner_level(L, B, p1), s1), (corner_level(L, B, p2), s2))
    raises = sorted(L - 1 - D for D, sg in pairs if sg == 1)
    lowers = sorted((D + 1 for D, sg in pairs if sg == -1), reverse=True)
    q: dict[int, int] = {}

    def add(m: int, c: int) -> None:
        q[m] = q.get(m, 0) + c

    if len(raises) == 2:
        fam = "RR"
        add(0, 1)
        for e in raises:
            add(e + 1, 1)
            add(e, -1)
    elif len(lowers) == 2:
        fam = "LL"
        K = lowers[0]
        add(K, 1)
        for k in lowers:
            add(K - k, 1)
            add(K - k + 1, -1)
    else:
        fam = "RL"
        (e,), (k,) = raises, lowers
        for m, c in ((k, 1), (k + e + 1, 1), (k + e, -1), (1, -1), (0, 1)):
            add(m, c)
    if (p2 - p1) % L in (1, L - 1):
        fam += "adj"
    red: dict[int, int] = {}
    for m, c in q.items():
        if c:
            red[m % L] = red.get(m % L, 0) + c * 2 ** (m // L)
    return fam, {m: c for m, c in red.items() if c}


def flatten(coeffs: dict[int, int]) -> dict[int, float]:
    """``q(theta) * (1 + theta/2)``; ``|N(1 + theta/2)| = 1 - (-1)^L 2^(1-L)``, essentially 1."""
    out: dict[int, float] = {}
    for m, c in coeffs.items():
        out[m] = out.get(m, 0) + c
        out[m + 1] = out.get(m + 1, 0) + c / 2
    return {m: c for m, c in out.items() if c}


def parseval_mass(coeffs: dict[int, float], L: int) -> float:
    """``sum c_m^2 theta^(2m)`` (exponents must be distinct and below ``L``): by Parseval and
    AM-GM, ``prod_j |g(zeta^j theta)| <= mass^(L/2)`` for any real polynomial ``g``."""
    if any(m >= L or m < 0 for m in coeffs):
        raise ValueError("exponents must lie in [0, L)")
    return sum(c * c * 4 ** (m / L) for m, c in coeffs.items())


def two_swap_mass_bounds(L: int, B: int) -> dict[str, float]:
    """Upper bounds (Lemma 9 of docs/BALANCE.md) for the Parseval mass of every two-swap element
    of slope ``B/L``: ``a = L - b`` ones, ``s = 2b - L`` corners ``22``, ``W(m) = 4^(m/L)``.
    ``RLflat`` bounds ``flatten(q)`` for raise-lower moves with ``k >= 2`` and ``e >= 1``."""
    b = B - L
    a, s = L - b, 2 * b - L

    def W(m: float) -> float:
        return 4 ** (m / L)

    m1 = min(a, s)
    return {
        "RR": 1 + 4 * W(a),
        "RRadj": 1 + 2 * W(m1) + 2 * W(m1 + a),
        "LL": 1 + W(1) + 3 * W(a),
        "LLadj": 1 + W(1) + W(min(b, 2 * a)) + W(a + 1) + W(a),
        "RL0": max(1 + W(1) + W(a + 1), 1 + W(a) + W(a + 1)),
        "RLflat": (1 + W(1) / 4 + W(2) / 4) + W(a) * (1 + W(1) / 4) + W(2 * a - 1) * (1 + W(1) / 4 + W(2) / 4),
    }


def two_swap_log_norm_bound(L: int, B: int) -> float:
    """Upper bound for ``log |N(q)|`` over all two-swap elements of slope ``B/L``
    (``inf`` when ``2b - L < 2``, where the flattened window does not fit; only ``L < 6``)."""
    if 2 * (B - L) - L < 2:
        return math.inf
    mb = two_swap_mass_bounds(L, B)
    flat = mb.pop("RLflat")
    return max(0.5 * L * math.log(max(mb.values())), 0.5 * L * math.log(flat) - math.log(1 - 2.0 ** (1 - L)))


def level_sum_mod_d(L: int, B: int) -> tuple[int, list[int], int]:
    """``(d, Z, A)`` with ``Z[D] = theta0^(-D) mod d`` and ``A = sum Z`` (the balanced ``A(w)``)."""
    d = 2**B - 3**L
    ti = pow(theta0(L, B), -1, d)
    Z = [1] * L
    for D in range(1, L):
        Z[D] = Z[D - 1] * ti % d
    return d, Z, sum(Z) % d


def two_swap_direct(L: int, B: int) -> list[tuple[int, int, int, int]]:
    """All ``(D1, s1, D2, s2)`` (distinct levels, ``s = +1`` raise, ``-1`` lower) for which moving
    the two corners makes ``A(w) = 0 mod d``, i.e. ``d | c(w)``.  Every pair of levels and signs
    is tried -- a superset of the two-swap words, letters outside ``{1, 2}`` included -- with
    ``O(L)`` work: raise-raise needs ``Z1 + Z2 = -A``, lower-lower ``Z1 + Z2 = 2A``, raise-lower
    ``Z_l = 2(A + Z_r)``.  An empty list proves that no two-swap word of slope ``B/L`` is a loop."""
    d, Z, A = level_sum_mod_d(L, B)
    where: dict[int, list[int]] = {}
    for D, z in enumerate(Z):
        where.setdefault(z, []).append(D)
    sols = []
    for D1, z in enumerate(Z):
        for D2 in where.get((-A - z) % d, []):
            if D2 > D1:
                sols.append((D1, 1, D2, 1))
        for D2 in where.get((2 * A - z) % d, []):
            if D2 > D1:
                sols.append((D1, -1, D2, -1))
        for D2 in where.get(2 * (A + z) % d, []):
            if D2 != D1:
                sols.append((D1, 1, D2, -1))
    return sols


def move_word(L: int, B: int, moves: list[tuple[int, int]]) -> tuple[int, ...] | None:
    """Word after moving the corners at the given levels (``(D, s)`` pairs) of the lower
    Christoffel word, or ``None`` if a letter leaves ``{1, 2}``."""
    v = list(christoffel(L, B))
    Binv = pow(B, -1, L) if L > 1 else 0
    for D, sg in moves:
        p = D * Binv % L
        v[p - 1] += sg
        v[p] -= sg
    return tuple(v) if all(x in (1, 2) for x in v) else None


def two_swap_loops(L: int, B: int) -> list[tuple[int, ...]]:
    """Two-swap words of slope ``B/L`` that are loops of ``3n+1`` (``d | c(w)``), via
    ``two_swap_direct``: solutions whose letters leave ``{1, 2}`` are discarded."""
    out = []
    for D1, s1, D2, s2 in two_swap_direct(L, B):
        w = move_word(L, B, [(D1, s1), (D2, s2)])
        if w is not None:
            out.append(w)
    return out


#: from this length on, Rhin's bound gives ``d > |N(q)|`` for every two-swap element
RHIN_FROM = 4000


def rhin_log_d(L: int, B: int) -> float:
    """Lower bound for ``log(2^B - 3^L)`` when ``2^B > 3^L`` and ``B >= 2``: ``d > 3^L Lambda``
    with ``Lambda = B log 2 - L log 3 >= B^(-13.3)``.  This is Rhin (1987) as stated by Rozier
    and Terracol (arXiv 2502.00948, Proposition 6.3): ``|u0 + u1 log 2 + u2 log 3| >= H^(-13.3)``
    for integers with ``H = max(|u1|, |u2|) >= 2``."""
    return L * math.log(3) - 13.3 * math.log(B)
