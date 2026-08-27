"""The Syracuse (odd-step) map ``S_q`` and its backward maps.

Setting (matches ``docs/GROUND_TRUTH.md``)::

    S_q(n) = (3n + q) / 2^b,    b = v2(3n + q) >= 1,    n odd, q odd, 3 does not divide q

``S_q`` sends positive odds to positive odds.  A *cycle* is a closed orbit of
odd numbers; ``L`` is the number of odd elements, ``M`` the largest odd element,
``B`` the total number of halvings around the cycle.  Classical Collatz is ``q = 1``.

Backward from ``M`` we write ``y_0 = M, y_1, y_2, ...`` with
``3*y_j + q = 2^{b_j} * y_{j-1}`` and ``B_k = b_1 + ... + b_k``.

Everything in this module is exact integer arithmetic.  Nothing here is
conjectural: these are the definitions plus the *predecessor lemma* below, which
is elementary.

Predecessor lemma (LEMMA-U)
---------------------------
Fix ``q`` odd with ``3 | q`` false, and let ``p > 0`` be odd.

* (T0) If ``3 | p`` then ``p`` has **no** odd ``S_q``-predecessor, hence lies on
  no ``S_q``-cycle.  Proof: ``3y + q = 2^b p`` reduced mod 3 gives ``q = 0``.
* Otherwise the odd predecessors of ``p`` are exactly
  ``y_b = (2^b * p - q) / 3`` for ``b >= 1`` with ``b == beta_p (mod 2)`` and
  ``2^b * p > q``, where ``beta_p = 1`` if ``p == -q (mod 3)`` and ``beta_p = 0``
  if ``p == q (mod 3)``.  Each such ``y_b`` is automatically odd, and ``y_b`` is
  strictly increasing in ``b``.
* Every odd ``p`` with ``3 | p`` false has **at most one** odd predecessor
  strictly below itself, for every ``q`` -- no hypothesis relating ``p`` and
  ``q``.  Proof: ``y_b < p`` iff ``q/p < 2^b < 3 + q/p``, a window of additive
  length 3; two powers of two of the same parity differ by ``3 * 2^b >= 6 > 3``.
* If moreover ``p >= q`` the window is ``(<= 1, <= 4)``, so the only candidate is
  ``b = 1``: there is exactly one smaller predecessor ``(2p - q)/3`` when
  ``p == -q (mod 3)`` and none when ``p == q (mod 3)``.

Prior art: this is textbook folklore.  ``T0`` is stated verbatim by Kaneda,
*Fibonacci Quart.* 53(2) (2015), 168-174, and is why Tao's Syracuse map is
defined on the odds coprime to 3.  The inverse map ``(2^n a - d)/3`` is Kaneda's
``g_d``.  Do not present any of this as new.
"""

from __future__ import annotations

from dataclasses import dataclass

__all__ = [
    "v2",
    "check_q",
    "is_admissible_odd",
    "syracuse",
    "syracuse_with_exponent",
    "forward_orbit",
    "forward_exponents",
    "predecessor_parity",
    "odd_predecessors",
    "predecessor_at",
    "smaller_predecessor",
    "count_predecessors_below",
    "BackStep",
]


def v2(n: int) -> int:
    """2-adic valuation of a nonzero integer."""
    if n == 0:
        raise ValueError("v2(0) is undefined")
    return (n & -n).bit_length() - 1


def check_q(q: int) -> None:
    """Raise unless ``q`` is a legal offset: **positive**, odd, not divisible by 3.

    * ``q`` odd keeps ``S_q`` well defined on odds.
    * ``3 | q`` false is what makes T0 (and the whole 3-adic story) work.
    * ``q > 0`` is required by **every** theorem in this package, not just for
      tidiness.  T1's proof is ``2^b >= 3 + q/M > 3``; T5, T6 and the floor rule
      need ``c_k > 0``; T7 needs ``c_L > 0``; the 2-adic sieve needs ``d_j > 0``.
      All of those fail for ``q < 0``, and for ``q < 0`` the map does not even
      keep positive odds positive (``S_{-7}(1) = -1``).  Rather than return
      silently wrong answers, negative ``q`` is rejected here.
    """
    if q % 2 == 0:
        raise ValueError(f"q must be odd, got {q}")
    if q % 3 == 0:
        raise ValueError(f"q must not be divisible by 3, got {q}")
    if q <= 0:
        raise ValueError(
            f"q must be positive, got {q}; every claim in this package "
            "(T1, T5, T6, T7 and both sieves) assumes q > 0"
        )


def is_admissible_odd(n: int) -> bool:
    """True iff ``n`` is a positive odd number that is not a multiple of 3.

    By T0 every element of every ``S_q``-cycle satisfies this.
    """
    return n > 0 and n % 2 == 1 and n % 3 != 0


def syracuse_with_exponent(n: int, q: int = 1) -> tuple[int, int]:
    """Return ``(S_q(n), b)`` with ``b = v2(3n + q)``.

    ``q`` is deliberately **not** validated here -- this is the inner loop of
    :func:`~collatz_maxodd.cycles.find_cycles` and is called millions of times.
    Callers that take ``q`` from the outside must run :func:`check_q` first.
    For ``q <= 0`` the value returned is arithmetically correct but meaningless
    for this package: ``S_q`` no longer maps positive odds to positive odds
    (``S_{-7}(1) = -1``) and every theorem here assumes ``q > 0``.
    """
    if n % 2 == 0:
        raise ValueError(f"S_q is defined on odd numbers, got {n}")
    t = 3 * n + q
    if t == 0:
        raise ValueError(f"3n + q vanishes for n={n}, q={q}")
    b = v2(t)
    return t >> b, b


def syracuse(n: int, q: int = 1) -> int:
    """The odd step ``S_q(n) = (3n + q) / 2^{v2(3n+q)}``."""
    return syracuse_with_exponent(n, q)[0]


def forward_orbit(n: int, q: int = 1, steps: int = 10) -> list[int]:
    """``[n, S_q(n), S_q^2(n), ...]`` with ``steps`` applications (length ``steps+1``)."""
    out = [n]
    x = n
    for _ in range(steps):
        x = syracuse(x, q)
        out.append(x)
    return out


def forward_exponents(n: int, q: int = 1, steps: int = 10) -> list[int]:
    """The forward halving vector ``[a_1, ..., a_steps]``, ``a_j = v2(3*x_{j-1} + q)``."""
    out: list[int] = []
    x = n
    for _ in range(steps):
        x, a = syracuse_with_exponent(x, q)
        out.append(a)
    return out


def predecessor_parity(p: int, q: int = 1) -> int | None:
    """Parity class of ``b`` for which ``(2^b p - q)/3`` is an integer.

    Returns ``1`` if admissible ``b`` must be odd, ``0`` if they must be even, and
    ``None`` if ``3 | p`` (no odd predecessors at all -- this is T0).
    """
    check_q(q)
    if p % 3 == 0:
        return None
    # Integrality needs 2^b * p == q (mod 3), i.e. (-1)^b * p == q (mod 3).
    return 1 if (p + q) % 3 == 0 else 0


def predecessor_at(p: int, b: int, q: int = 1) -> int | None:
    """The odd predecessor of ``p`` using ``b`` halvings, or ``None`` if there is none.

    ``y = (2^b p - q)/3``; valid when it is a positive integer.  ``y`` is then
    automatically odd, and ``v2(3y + q) == b`` automatically (because ``p`` is odd).
    """
    if b < 1:
        raise ValueError("b must be >= 1")
    t = (1 << b) * p - q
    if t <= 0 or t % 3 != 0:
        return None
    return t // 3


def odd_predecessors(p: int, q: int = 1, max_b: int = 32) -> list[tuple[int, int]]:
    """All ``(b, y_b)`` with ``1 <= b <= max_b`` and ``y_b`` a positive odd predecessor.

    The ``b`` values form a single parity class (``predecessor_parity``) and
    ``y_b`` is strictly increasing in ``b``.
    """
    check_q(q)
    out: list[tuple[int, int]] = []
    for b in range(1, max_b + 1):
        y = predecessor_at(p, b, q)
        if y is not None:
            out.append((b, y))
    return out


def smaller_predecessor(p: int, q: int = 1) -> tuple[int, int] | None:
    """The unique odd predecessor ``y < p``, as ``(b, y)``; ``None`` if there is none.

    By LEMMA-U(d) there is **at most one**, for every ``q`` and every odd ``p > 0``
    -- no hypothesis relating ``p`` and ``q`` is needed.  The search window is
    ``q/p < 2^b < 3 + q/p``, so only ``b`` with ``2^b <= 3 + q`` can qualify.
    """
    check_q(q)
    if p % 3 == 0:
        return None
    found: tuple[int, int] | None = None
    b = 1
    while (1 << b) * p < 3 * p + q:  # y_b < p  <=>  2^b * p < 3p + q
        y = predecessor_at(p, b, q)
        if y is not None:
            if found is not None:  # pragma: no cover - contradicts LEMMA-U
                raise AssertionError(
                    f"LEMMA-U violated: p={p}, q={q} has two smaller predecessors"
                )
            found = (b, y)
        b += 1
    return found


def count_predecessors_below(p: int, bound: int, q: int = 1) -> int:
    """``#{odd predecessors y of p with 0 < y <= bound}``.

    Closed form (LEMMA-U(c)): the number of ``b >= 1`` with ``b == beta_p (mod 2)``
    and ``q < 2^b * p <= 3*bound + q``.  Roughly ``0.5 * log2(3*bound/p)``.
    """
    check_q(q)
    beta = predecessor_parity(p, q)
    if beta is None:
        return 0
    hi = 3 * bound + q
    n = 0
    b = 1 if beta == 1 else 2
    while (1 << b) * p <= hi:
        if (1 << b) * p > q:
            n += 1
        b += 2
    return n


@dataclass(frozen=True, slots=True)
class BackStep:
    """One backward hop ``y_{j-1} -> y_j`` with ``3*y_j + q = 2^{b_j} * y_{j-1}``."""

    b: int
    y: int
