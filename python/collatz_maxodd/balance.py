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
* **Runs.**  For any word, ``(theta - 1) theta^(L-1) A(w)`` has coefficients equal to the
  differences of ``2^(displacement)`` between neighbouring levels (``profile_element``).  So
  raising a whole run of consecutive levels by one step costs three terms,
  ``1 - theta^g + theta^f``, whatever its length: the one-swap proof applies and no such word
  is a loop (``run_word``, ``run_element``).
* **Repeats.**  No number field here.  If the halving words starting at two different members
  agree for ``j`` letters of total weight ``X``, then
  ``3^j (n_p - n_q) = 2^X (n_(p+j) - n_(q+j))``, so the two members differ by a multiple of
  ``2^X``.  Every member is at most ``2^sigma / (2^(B/L) - 3)``, ``sigma`` the height spread
  of the staircase.  So a loop has no repeated stretch of weight
  ``X >= sigma - log2(2^(B/L) - 3)``.  Balanced words have only ``j + 1`` stretches of length
  ``j``, so every word that differs from one in few corners, or whose profile has few jumps,
  is excluded once ``L`` is large (``longest_repeat``, ``repeat_excludes``,
  ``max_moved_corners``).
* **Local repeats.**  The gap ``2^(X+1)`` is a gap between the two members the stretch starts
  from, and the member at corner ``p`` is at most ``2^(tau + h_p/L)``, ``h_p`` its height above
  the lowest level.  So ``X + 1 < tau + max(h_p, h_q)/L``: only the two starting members
  matter, and the rest of the staircase enters only through the lowest level (``heights``,
  ``local_repeat``).  A word whose staircase stays on or below a balanced one and touches it
  along ``2j + 2`` consecutive corners, ``floor(jB/L) >= tau``, is therefore not a loop
  (``touching_stretch``, ``low_stretch_length``).
"""

from __future__ import annotations

import cmath
import math
from decimal import ROUND_FLOOR, Decimal, localcontext
from fractions import Fraction
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
    "displacement",
    "normalize",
    "admissible_rotations",
    "profile_element",
    "mass_criterion",
    "run_is_valid",
    "run_word",
    "run_element",
    "run_log_norm_bound",
    "balanced_word",
    "profile_word",
    "generalized_levels",
    "height_spread",
    "repeat_at_length",
    "longest_repeat",
    "smallest_B",
    "size_exponent",
    "size_exponent_bound",
    "window_suffices",
    "swap_span",
    "repeat_excludes",
    "moved_corner_window",
    "max_moved_corners",
    "moved_corner_reach",
    "heights",
    "least_size_exponent",
    "local_repeat",
    "low_stretch_window",
    "low_stretch_length",
    "touching_stretch",
    "max_lowered_corners",
    "heaviest_repeat",
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


# ----------------------------------------------------------------------------- runs


def displacement(w: tuple[int, ...] | list[int]) -> list[int]:
    """Profile of a word against the lower Christoffel word of the same length and sum, indexed
    by level: ``m[D] = X'_p - X_p`` for the corner ``p`` with ``pB mod L = D``.  ``m[0] = 0``."""
    L, B = len(w), sum(w)
    if gcd(L, B) != 1:
        raise ValueError("need gcd(L, B) = 1")
    m = [0] * L
    X = 0
    for p, x in enumerate(w):
        m[(p * B) % L] = X - (p * B) // L
        X += x
    return m


def normalize(w: tuple[int, ...] | list[int]) -> tuple[int, ...]:
    """The rotation of ``w`` that starts at its first corner of least displacement.  Its profile
    is non-negative: rotating by ``r`` turns ``m_p`` into ``m_(p+r) - m_r + [D_p + D_r >= L]``.
    Other rotations can have a non-negative profile too; see ``admissible_rotations``."""
    w = tuple(w)
    L, B = len(w), sum(w)
    best, r, X = 0, 0, 0
    for p, x in enumerate(w):
        if X - (p * B) // L < best:
            best, r = X - (p * B) // L, p
        X += x
    return w[r:] + w[:r]


def admissible_rotations(w: tuple[int, ...] | list[int]) -> list[tuple[int, ...]]:
    """All rotations of ``w`` whose profile is non-negative.  With ``D'_p = pB - L X'_p`` the
    generalized levels of ``w``, they are the rotations starting at a corner ``r`` with
    ``D'_r > max D' - L``.  Lemma 10 gives one element for each; their masses differ."""
    w = tuple(w)
    L, B = len(w), sum(w)
    D, X = [], 0
    for p, x in enumerate(w):
        D.append(p * B - L * X)
        X += x
    top = max(D)
    return [w[r:] + w[:r] for r in range(L) if D[r] > top - L]


def profile_element(m: list[int]) -> dict[int, int]:
    """Lemma 10: ``(theta - 1) theta^(L-1) A(w) = (2 u_(L-1) - u_0) + sum_(j>=1) (u_(j-1) - u_j) theta^j``
    with ``u_j = 2^(m[L-1-j])``, for a profile ``m`` indexed by level with every ``m[D] >= 0``.
    The exponents are ``0, ..., L-1``; ``d | c(w)`` iff this element lies in ``(theta^B - 3)``."""
    L = len(m)
    if min(m) < 0:
        raise ValueError("displacements must be non-negative; rotate the word with normalize()")
    u = [2 ** m[L - 1 - j] for j in range(L)]
    q = {0: 2 * u[L - 1] - u[0]}
    for j in range(1, L):
        q[j] = u[j - 1] - u[j]
    return {j: c for j, c in q.items() if c}


def mass_criterion(w: tuple[int, ...] | list[int]) -> bool:
    """Corollary 11: True when Parseval alone proves that ``w`` is not a loop of ``3n+1``
    (coprime ``L, B``, ``2^B > 3^L``): some rotation with a non-negative profile has a profile
    element of mass ``M`` with ``M^(L/2) < d``.  The verdict is the same for every rotation
    of ``w``, because the smallest mass over the admissible rotations is used."""
    L, B = len(w), sum(w)
    d = 2**B - 3**L
    M = min(parseval_mass(profile_element(displacement(v)), L) for v in admissible_rotations(w))
    return 0.5 * L * math.log(M) < math.log(d)


def run_is_valid(L: int, B: int, D1: int, D2: int) -> bool:
    """Lemma 12: raising the corners of levels ``D1..D2`` (``1 <= D1 <= D2 <= L-1``) keeps every
    letter positive iff ``D1 >= 2L - B`` (all corners followed by a 2) or ``D2 = L - 1``."""
    if not 1 <= D1 <= D2 <= L - 1:
        raise ValueError("need 1 <= D1 <= D2 <= L - 1")
    return D1 >= 2 * L - B or D2 == L - 1


def run_word(L: int, B: int, D1: int, D2: int) -> tuple[int, ...] | None:
    """Raise by one step every corner of the lower Christoffel word whose level lies in
    ``[D1, D2]`` (``x_(p-1) += 1``, ``x_p -= 1`` for each); ``None`` if a letter drops to 0."""
    if not 1 <= D1 <= D2 <= L - 1:
        raise ValueError("need 1 <= D1 <= D2 <= L - 1")
    v = list(christoffel(L, B))
    Binv = pow(B, -1, L)
    for D in range(D1, D2 + 1):
        p = D * Binv % L
        v[p - 1] += 1
        v[p] -= 1
    return tuple(v) if min(v) >= 1 else None


def run_element(L: int, D1: int, D2: int) -> dict[int, int]:
    """Element of the run ``[D1, D2]``: ``1 - theta^g + theta^f`` with ``g = L - 1 - D2`` and
    ``f = L - D1``, or the unit ``theta^f`` when ``g = 0`` (a rotation of the balanced word)."""
    g, f = L - 1 - D2, L - D1
    return {f: 1} if g == 0 else {0: 1, g: -1, f: 1}


def run_log_norm_bound(L: int, B: int) -> float:
    """``(L/2) log(1 + 4^((b-1)/L) + 4^(b/L))``: Parseval bound for ``log |N|`` of every run
    element with ``g >= 1`` and ``D1 >= 2L - B`` (then ``1 <= g < f <= b``)."""
    b = B - L
    return 0.5 * L * math.log(1 + 4 ** ((b - 1) / L) + 4 ** (b / L))


# ----------------------------------------------------------------------------- repeats


def balanced_word(L: int, B: int) -> tuple[int, ...]:
    """The balanced word of length ``L`` and sum ``B``, for any gcd: the lower Christoffel word
    of ``(L/g, B/g)`` repeated ``g = gcd(L, B)`` times."""
    g = gcd(L, B)
    return christoffel(L // g, B // g) * g


def profile_word(L: int, B: int, m: list[int]) -> tuple[int, ...] | None:
    """Inverse of ``displacement``: the word whose corner of level ``D`` sits ``m[D]`` steps above
    the lower Christoffel staircase (``gcd(L, B) = 1``, ``m[0] = 0``); ``None`` if a letter is
    not positive."""
    if gcd(L, B) != 1 or len(m) != L or m[0] != 0:
        raise ValueError("need gcd(L, B) = 1, one displacement per level, and m[0] = 0")
    X = [(p * B) // L + m[(p * B) % L] for p in range(L)] + [B]
    w = tuple(X[p + 1] - X[p] for p in range(L))
    return w if min(w) >= 1 else None


def generalized_levels(w: tuple[int, ...] | list[int]) -> list[int]:
    """``D'_p = pB - L X'_p`` for ``p = 0, ..., L-1``: one integer in each residue class of
    ``pB`` modulo ``L``; ``D'_p / L`` is the height of the line above corner ``p``."""
    L, B = len(w), sum(w)
    out, X = [], 0
    for p, x in enumerate(w):
        out.append(p * B - L * X)
        X += x
    return out


def height_spread(w: tuple[int, ...] | list[int]) -> Fraction:
    """``sigma = (max D' - min D') / L``: the vertical extent, in halvings, of the staircase's
    deviation from the straight line.  A balanced word has ``sigma = (L - g)/L``, ``g = gcd(L, B)``."""
    D = generalized_levels(w)
    return Fraction(max(D) - min(D), len(w))


def repeat_at_length(w: tuple[int, ...] | list[int], j: int) -> tuple[int, int] | None:
    """Two different cyclic positions ``p < q`` whose next ``j`` letters agree, or ``None``."""
    w = tuple(w)
    L = len(w)
    if not 1 <= j < L:
        return None
    ww = w + w
    seen: dict[tuple[int, ...], int] = {}
    for p in range(L):
        f = ww[p : p + j]
        if f in seen:
            return seen[f], p
        seen[f] = p
    return None


def longest_repeat(w: tuple[int, ...] | list[int]) -> tuple[int, int, int, int]:
    """``(j, X, p, q)``: the largest ``j`` such that some stretch of ``j`` letters occurs at two
    different cyclic positions ``p < q``, and the weight ``X`` of that stretch.  ``(0, 0, 0, 0)``
    if all letters are different.  (A repeat of length ``j`` contains one of length ``j - 1``,
    so a binary search finds the largest.)"""
    w = tuple(w)
    L = len(w)
    lo, hi, best = 0, L - 1, None
    while lo < hi:
        mid = (lo + hi + 1) // 2
        r = repeat_at_length(w, mid)
        if r is None:
            hi = mid - 1
        else:
            lo, best = mid, r
    if lo == 0 or best is None:
        return 0, 0, 0, 0
    p, q = best
    return lo, sum((w + w)[p : p + lo]), p, q


def smallest_B(L: int) -> int:
    """``B0 = floor(L log2 3) + 1``, the least ``B`` with ``2^B > 3^L``, computed exactly.
    Double precision is not enough: at ``L = 137 528 045 312``, ``L log2 3`` is within
    ``1.3e-12`` of an integer and ``math.floor(L * LOG2_3) + 1`` is off by one."""
    if L <= 20000:
        return (3**L).bit_length()
    with localcontext() as ctx:
        ctx.prec = 90
        x = Decimal(L) * (Decimal(3).ln() / Decimal(2).ln())
        f = x.to_integral_value(rounding=ROUND_FLOOR)
        if min(x - f, f + 1 - x) < Decimal("1e-40"):
            raise ArithmeticError("L log2 3 is too close to an integer for 90 digits")
        return int(f) + 1


def size_exponent(L: int, B: int) -> float:
    """``tau = -log2(2^(B/L) - 3)``: by Lemma 14 every member of a loop is at most
    ``2^(sigma + tau)`` and the smallest is at most ``2^tau``.  Computed with 90 digits through
    ``2^(B/L) - 3 = 3 (exp(Lambda / L) - 1)``, ``Lambda = B log 2 - L log 3``, without forming
    ``2^B`` or ``3^L``, so it works at any length."""
    with localcontext() as ctx:
        ctx.prec = 90
        ln2 = Decimal(2).ln()
        lam = Decimal(B) * ln2 - Decimal(L) * Decimal(3).ln()
        if lam <= 0:
            raise ValueError("need 2^B > 3^L")
        v = 3 * ((lam / Decimal(L)).exp() - 1)
        return float(-(v.ln() / ln2))


def size_exponent_bound(L: int, B: int) -> float:
    """Upper bound for ``size_exponent`` that needs no computation with ``d``:
    ``2^(B/L) - 3 > 3 Lambda / L`` with ``Lambda = B log 2 - L log 3``.  For
    ``B = smallest_B(L)`` Rhin's bound ``Lambda >= B^(-13.3)`` gives
    ``log2(L/3) + 13.3 log2 B``; for larger ``B``, ``Lambda > log 2`` gives ``log2(L / (3 log 2))``."""
    if B == smallest_B(L):
        return math.log2(L / 3) + 13.3 * math.log2(B)
    return math.log2(L / (3 * math.log(2)))


def window_suffices(L: int, B: int, j: int, s: int) -> bool:
    """Exact integer test of ``floor(jB/L) >= s + tau``: with ``N = floor(jB/L) - s`` it reads
    ``2^(-N) <= 2^(B/L) - 3``, that is ``(3 * 2^N + 1)^L <= 2^(B + NL)``.  For moderate ``L``."""
    N = (j * B) // L - s
    return N >= 0 and (3 * 2**N + 1) ** L <= 2 ** (B + N * L)


def swap_span(k: int) -> int:
    """Displacement span after ``k`` swaps of a balanced word of 1s and 2s: ``s <= isqrt(2k) + 1``.
    Displacements are 1-Lipschitz along the word, so a corner ``t`` steps up costs at least
    ``t^2`` swaps; ``u^2 + v^2 <= k`` gives ``u + v <= isqrt(2k)``."""
    return math.isqrt(2 * k) + 1


def repeat_excludes(w: tuple[int, ...] | list[int]) -> bool:
    """Theorem 4 applied to ``w`` with the exact size exponent: True when the stretch found by
    ``longest_repeat`` has weight ``X >= sigma + tau``, which no loop of ``3n+1`` can have.
    Sufficient, not necessary: a shorter repeated stretch can be heavier than the longest."""
    L, B = len(w), sum(w)
    _, X, _, _ = longest_repeat(w)
    return X >= float(height_spread(w)) + size_exponent(L, B)


def moved_corner_window(L: int, B: int, s: int, exact: bool = False) -> int:
    """Least ``j`` with ``floor(jB/L) >= s + tau``: the length of stretch whose repetition
    Corollary 16 needs when the corner displacements span ``s - 1`` steps.  ``tau`` is the
    bound of ``size_exponent_bound`` (or the exact value when ``exact``)."""
    need = s + (size_exponent(L, B) + 1e-9 if exact else size_exponent_bound(L, B))
    j = max(1, math.floor(need * L / B) - 1)
    while (j * B) // L < need:
        j += 1
    return j


def max_moved_corners(L: int, B: int, s: int = 3, exact: bool = False) -> int:
    """Corollary 16: largest ``k`` such that a word differing from a balanced word in ``k``
    corners, with displacements spanning ``s - 1`` steps, cannot be a loop: the largest ``k``
    with ``(k + 1)(j + 1) < L`` for ``j = moved_corner_window``.  ``-1`` if even ``k = 0`` fails."""
    j = moved_corner_window(L, B, s, exact)
    return (L - 1) // (j + 1) - 1


def moved_corner_reach(L: int, s: int = 3) -> float:
    """Explicit form valid for every ``B``: ``k`` moved corners are excluded whenever
    ``k + 1 < L / Psi`` with ``Psi = 2 + (s + 1 + log2(L/3) + 13.3 log2(L log2 3 + 1)) / log2 3``.
    Returns ``L / Psi``."""
    psi = 2 + (s + 1 + math.log2(L / 3) + 13.3 * math.log2(L * LOG2_3 + 1)) / LOG2_3
    return L / psi


# ----------------------------------------------------------------------------- local repeats


def heights(w: tuple[int, ...] | list[int]) -> list[int]:
    """``h_p = D'_p - min D'``: the height of corner ``p`` above the lowest level, in level
    units (``h_p / L`` halvings).  By Lemma 14 the member at corner ``p`` of a loop of ``3n+1``
    is at most ``2^(tau + h_p/L)``: low corners carry small members.  In the staircase drawing
    the low corners are the ones that reach highest against the line."""
    D = generalized_levels(w)
    lo = min(D)
    return [x - lo for x in D]


def least_size_exponent(L: int, B: int, q: int = 1) -> int:
    """Least whole ``N >= 0`` with ``(3 * 2^N + q)^L <= 2^(N L + B)``, that is
    ``N >= tau + log2 q``: the size test ``hN`` of ``lean/Collatz/Repeat.lean``.  Exact integer
    arithmetic, for moderate ``L``."""
    if 2**B <= 3**L:
        raise ValueError("need 2^B > 3^L")
    N = 0
    while (3 * 2**N + q) ** L > 2 ** (N * L + B):
        N += 1
    return N


def local_repeat(
    w: tuple[int, ...] | list[int], q: int = 1, local: bool = True
) -> tuple[int, int, int, int] | None:
    """Theorem 5 applied to ``w``: ``(p, r, j, X)`` such that the stretches of length ``j`` at the
    different positions ``p`` and ``r`` are equal, with weight ``X``, and

        (X + 1) L >= N L + max(h_p, h_r),        N = least_size_exponent(L, B, q).

    No loop of ``3n+q`` has such a pair (``Cycle.repeat_theorem_local`` in Lean, read
    contrapositively).  ``None`` if no pair qualifies.  With ``local=False`` the height of the
    two starting corners is replaced by the full spread ``max D' - min D'``, which is the test
    of Theorem 4.  Exact; cost about ``L^2`` times the longest repeat."""
    w = tuple(w)
    L, B = len(w), sum(w)
    N = least_size_exponent(L, B, q)
    h = heights(w)
    spread = max(h)
    ww = w + w
    pre = [0]
    for x in ww:
        pre.append(pre[-1] + x)
    for j in range(1, L):
        groups: dict[tuple[int, ...], list[int]] = {}
        for p in range(L):
            groups.setdefault(ww[p : p + j], []).append(p)
        any_repeat = False
        for members in groups.values():
            if len(members) < 2:
                continue
            any_repeat = True
            a, b = sorted(members, key=lambda t: h[t])[:2]  # the two lowest starting corners
            X = pre[a + j] - pre[a]
            if (X + 1) * L >= N * L + (max(h[a], h[b]) if local else spread):
                return min(a, b), max(a, b), j, X
        if not any_repeat:
            return None
    return None


def low_stretch_window(L: int, B: int, u: int = 0, exact: bool = False) -> int:
    """Least ``j`` with ``floor(jB/L) >= u + tau``: the length of stretch whose repetition
    Corollary 21 needs when the staircase rises at most ``u`` steps above the balanced one.
    ``tau`` is the bound of ``size_exponent_bound`` (or the exact value when ``exact``)."""
    return moved_corner_window(L, B, u, exact)


def low_stretch_length(L: int, B: int, u: int = 0, exact: bool = False) -> int:
    """Corollary 21: a word whose staircase stays at most ``u`` steps above a balanced one and
    agrees with it on this many consecutive letters, ``2j + 1`` with ``j = low_stretch_window``,
    is not a loop, provided ``2j + 2 <= L``.  The agreement is along ``2j + 2`` consecutive
    corners.  This many letters suffice; fewer may do."""
    return 2 * low_stretch_window(L, B, u, exact) + 1


def touching_stretch(
    w: tuple[int, ...] | list[int], c: tuple[int, ...] | list[int], j: int, u: int = 0
) -> int | None:
    """Hypothesis of Corollary 21.  With ``m_p = X_p(w) - X_p(c)`` the displacement of corner
    ``p`` of ``w`` above the corner of ``c``: a corner ``p0`` such that ``m`` is constant on the
    ``2j + 2`` corners ``p0, ..., p0 + 2j + 1`` (read cyclically) and ``m_p <= m_p0 + u`` at every
    corner; the first one met when scanning from position 0.  ``None`` if there is none, and
    always ``None`` when ``2j + 2 > L``.  ``w`` and ``c`` must have the same length and sum."""
    w, c = tuple(w), tuple(c)
    L = len(w)
    if len(c) != L or sum(c) != sum(w):
        raise ValueError("w and c must have the same length and sum")
    if 2 * j + 2 > L:
        return None
    m, d = [], 0
    for x, y in zip(w, c):
        m.append(d)
        d += x - y
    top = max(m)
    run = 0  # number of consecutive equal letters ending at the current position
    for t in range(2 * L):
        run = run + 1 if w[t % L] == c[t % L] else 0
        if run >= 2 * j + 1:
            p0 = (t - 2 * j) % L
            if top <= m[p0] + u:
                return p0
    return None


def max_lowered_corners(L: int, B: int, u: int = 0, exact: bool = False) -> int:
    """Corollary 22: the largest ``k`` such that a word differing from a balanced word in ``k``
    corners, each moved any number of steps down and at most ``u`` steps up, cannot be a loop:
    the largest ``k`` with ``k (2j + 2) < L`` for ``j = low_stretch_window``."""
    return (L - 1) // (2 * low_stretch_window(L, B, u, exact) + 2)


def heaviest_repeat(w: tuple[int, ...] | list[int]) -> int:
    """The largest weight of a stretch that starts at two different cyclic positions (0 if
    all letters differ).  This, not the longest repeat, is what Theorem 4 compares with
    ``sigma + tau``.  Positions are grouped by their stretch of length ``j`` and the groups are
    refined one letter at a time, so the cost is ``L`` times the length of the longest repeat."""
    w = tuple(w)
    L = len(w)
    ids = [0] * L
    weight = [0] * L
    best = 0
    for j in range(1, L):
        key: dict[tuple[int, int], int] = {}
        new = [0] * L
        for p in range(L):
            x = w[(p + j - 1) % L]
            new[p] = key.setdefault((ids[p], x), len(key))
            weight[p] += x
        count = [0] * len(key)
        for p in range(L):
            count[new[p]] += 1
        repeated = False
        for p in range(L):
            if count[new[p]] > 1:
                repeated = True
                if weight[p] > best:
                    best = weight[p]
        if not repeated:
            break
        ids = new
    return best
