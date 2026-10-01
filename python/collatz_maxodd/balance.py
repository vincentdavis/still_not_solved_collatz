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
