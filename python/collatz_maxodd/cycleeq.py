"""The cycle equation and the ``2^B / 3^L`` Diophantine condition.

Three exact identities for an ``S_q``-cycle with maximum ``M``, ``L`` odd
elements and ``B`` halvings:

1. **Cycle equation (T7).**  ``M * (2^B - 3^L) = c_L``, where ``c_L`` is the
   backward constant of the full loop.  Equivalently, forwards from ``M``,
   ``M * (2^B - 3^L) = d_L = q * sum_{j=1..L} 3^{L-j} * 2^{A_{j-1}}``.
   Since ``c_L > 0`` this forces ``2^B > 3^L`` and ``B/L > log2 3``.
   This is **Boehm & Sontacchi**, *Atti Accad. Naz. Lincei* 64 (1978) 260-264;
   see also Lagarias, *Amer. Math. Monthly* 92 (1985) 3-23.  It is already
   formalised in Lean (ccchallenge.org).  Not new.

2. **Product identity.**  ``prod_{j} (3 + q/z_j) = 2^B`` over the cycle
   elements ``z_j``.  Immediate from ``3 z_{j-1} + q = 2^{a_j} z_j`` and
   ``prod z_{j-1} = prod z_j``.

3. **Crandall-type squeeze.**  From 2 and ``m <= z_j <= M``,
   ``L * log2(3 + q/M)  <=  B  <=  L * log2(3 + q/m)``, so

       0  <  B/L - log2 3  <=  log2(1 + q/(3m)).

   With a verified no-cycle bound ``m > X_0`` this pins ``B/L`` to a rational
   approximation of ``log2 3`` of quality ``~ q/(3 m ln 2)``, and the theory of
   best approximations then forces ``L`` to be large.  The device is
   **Crandall**, *Math. Comp.* 32 (1978) 1281-1292; the modern quantitative
   versions (Steiner 1977, Simons 2005, Simons-de Weger 2005, Eliahou 1993,
   Hercher 2023) use Baker's theorem and are far stronger than what this module
   computes.  Do not present the number produced here as a new bound.

Current published inputs (for the report), with the chain stated exactly:
Barina, *J. Supercomputing* 81 (2025) art. 810, verifies Collatz convergence
for all ``n < 2^71 = 2048 * 2^60`` (the figure IN THE PAPER; the page dates
that milestone 2025-01-15); his project page (pcbarina.fit.vutbr.cz, retrieved
2026-08) reports ``2075 * 2^60`` as its current limit, which is not in print.
Hercher, *JIS* 26 (2023) Art. 23.3.5: no ``m``-cycles
with ``m <= 91`` (Thm 23, unconditional at his ``X_0 = 695 * 2^60``), and
``K > 1.375e11`` odd elements *conditional on* ``X_0 >= 1536 * 2^60 = 3*2^69``
(Cor. 29) — a condition Barina's paper discharges, so the length bound is now
unconditional.  Either Barina figure discharges it; this module keeps the two
distinct.  The exact-rational re-run of Hercher's ladder at the 2025 bound
lives in :mod:`collatz_maxodd.hercher`.
"""

from __future__ import annotations

from decimal import Decimal, getcontext
from fractions import Fraction
from functools import lru_cache

from .backtree import c_constant
from .cycles import Cycle

__all__ = [
    "cycle_constant",
    "forward_constant",
    "check_cycle_equation",
    "product_identity",
    "ratio_window",
    "log2_3",
    "log2_3_cf",
    "log2_3_convergents",
    "best_upper_approximations",
    "min_B_for_L",
    "length_admissible",
    "smallest_admissible_length",
    "BARINA_2025_LIMIT",
    "BARINA_2025_PAPER_LIMIT",
]

#: Barina's PROJECT-PAGE figure (pcbarina.fit.vutbr.cz, current limit as
#: retrieved 2026-08): convergence verified for all n < 2075 * 2^60.  Not in print — the published
#: paper stops at :data:`BARINA_2025_PAPER_LIMIT`.  Kept as this module's
#: working limit for the *report* only; anything labeled a theorem should cite
#: the paper figure.
BARINA_2025_LIMIT = 2075 * 2**60

#: The figure in Barina's published paper (J. Supercomputing 81 (2025) 810):
#: convergence verified for all n < 2^71 = 2048 * 2^60.
BARINA_2025_PAPER_LIMIT = 2**71


def cycle_constant(cycle: Cycle) -> int:
    """``c_L`` for the full backward loop of ``cycle`` (starting at ``M``)."""
    return c_constant(cycle.backward_halvings, cycle.q)


def forward_constant(cycle: Cycle) -> int:
    """``d_L = q * sum_{j=1..L} 3^{L-j} 2^{A_{j-1}}`` for the forward loop from ``M``."""
    q, L = cycle.q, cycle.L
    total = 0
    a_partial = 0
    for j in range(1, L + 1):
        total += 3 ** (L - j) * (1 << a_partial)
        a_partial += cycle.forward_halvings[j - 1]
    return q * total


def check_cycle_equation(cycle: Cycle) -> bool:
    """``M * (2^B - 3^L) == c_L == d_L``, and ``2^B > 3^L`` (T7)."""
    lhs = cycle.M * ((1 << cycle.B) - 3**cycle.L)
    return (
        (1 << cycle.B) > 3**cycle.L
        and lhs == cycle_constant(cycle)
        and lhs == forward_constant(cycle)
    )


def product_identity(cycle: Cycle) -> bool:
    """``prod_j (3 + q/z_j) == 2^B`` exactly, over the rationals."""
    prod = Fraction(1)
    for z in cycle.elements:
        prod *= 3 + Fraction(cycle.q, z)
    return prod == Fraction(1 << cycle.B)


def ratio_window(cycle: Cycle) -> tuple[Fraction, Fraction]:
    """``(3 + q/M, 3 + q/m)``: the exact bracket for the geometric mean ``2^{B/L}``.

    Guaranteed: ``(3 + q/M)^L <= 2^B <= (3 + q/m)^L``.
    """
    return (
        3 + Fraction(cycle.q, cycle.M),
        3 + Fraction(cycle.q, cycle.min_element),
    )


# --------------------------------------------------------------------------
# continued fraction of log2(3)
# --------------------------------------------------------------------------


@lru_cache(maxsize=None)
def log2_3(prec: int = 200) -> Decimal:
    """``log2(3)`` to ``prec`` significant decimal digits.

    Computed as ``ln(3)/ln(2)`` in :mod:`decimal` at ``prec + 20`` guard digits.
    ``log2 3`` is irrational (indeed transcendental by Gelfond-Schneider), so the
    continued fraction below never terminates; the ``prec`` digits are what
    bounds how many terms are trustworthy.
    """
    ctx = getcontext().copy()
    ctx.prec = prec + 25
    three = Decimal(3)
    two = Decimal(2)
    val = ctx.divide(three.ln(context=ctx), two.ln(context=ctx))
    return +val


@lru_cache(maxsize=None)
def log2_3_cf(n: int = 20, prec: int = 200) -> tuple[int, ...]:
    """First ``n`` continued-fraction terms of ``log2 3``.

    Known start: ``[1; 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, ...]``.
    Terms are reliable while the convergent denominators stay far below
    ``10^prec``; ``n <= 30`` at the default precision is comfortable, and
    :func:`log2_3_convergents` cross-checks the early ones exactly.
    """
    ctx = getcontext().copy()
    ctx.prec = prec + 25
    x = log2_3(prec)
    terms: list[int] = []
    for _ in range(n):
        a = int(x.to_integral_value(rounding="ROUND_FLOOR"))
        terms.append(a)
        frac = x - a
        if frac == 0:  # pragma: no cover - log2 3 is irrational
            break
        x = ctx.divide(Decimal(1), frac)
    return tuple(terms)


@lru_cache(maxsize=None)
def log2_3_convergents(n: int = 20, prec: int = 200) -> tuple[tuple[int, int], ...]:
    """Convergents ``(p_k, q_k)`` of ``log2 3``, ``k = 0 .. n-1``.

    Even ``k`` lie below ``log2 3``, odd ``k`` above.  Starts
    ``1/1, 2/1, 3/2, 8/5, 19/12, 65/41, 84/53, 485/306, 1054/665, ...``.
    """
    terms = log2_3_cf(n, prec)
    out: list[tuple[int, int]] = []
    pm1, pm2 = 1, 0
    qm1, qm2 = 0, 1
    for a in terms:
        p = a * pm1 + pm2
        q = a * qm1 + qm2
        out.append((p, q))
        pm2, pm1 = pm1, p
        qm2, qm1 = qm1, q
    return tuple(out)


@lru_cache(maxsize=None)
def best_upper_approximations(
    n: int = 24, prec: int = 200
) -> tuple[tuple[int, int], ...]:
    """Rationals ``p/q > log2 3`` that beat every smaller denominator, by ``q``.

    Generated from the convergents and semiconvergents
    ``(p_{k-1} + i*p_k) / (q_{k-1} + i*q_k)``, which is the standard complete
    candidate set for one-sided best approximations; the running record filter
    then keeps exactly the best ones.  Starts ``2/1, 8/5, 65/41, 485/306, ...``.

    These denominators are the only candidates for the cycle length ``L`` in
    :func:`smallest_admissible_length`: if some ``L`` satisfies the squeeze then
    so does the best upper approximation with denominator ``<= L``.
    """
    conv = log2_3_convergents(n, prec)
    terms = log2_3_cf(n, prec)
    alpha = log2_3(prec)
    cands: set[tuple[int, int]] = set()
    for k in range(1, len(conv)):
        p_prev, q_prev = conv[k - 1]
        p_k, q_k = conv[k]
        cands.add((p_k, q_k))
        a_next = terms[k + 1] if k + 1 < len(terms) else 1
        for i in range(0, a_next + 1):
            cands.add((p_prev + i * p_k, q_prev + i * q_k))
    upper = sorted(
        (pq for pq in cands if pq[1] > 0 and Decimal(pq[0]) / Decimal(pq[1]) > alpha),
        key=lambda pq: pq[1],
    )
    out: list[tuple[int, int]] = []
    best: Decimal | None = None
    ctx = getcontext().copy()
    ctx.prec = prec
    for p, q in upper:
        gap = ctx.subtract(ctx.divide(Decimal(p), Decimal(q)), alpha)
        if best is None or gap < best:
            best = gap
            out.append((p, q))
    return tuple(out)


# --------------------------------------------------------------------------
# implied lower bounds on cycle length
# --------------------------------------------------------------------------


def min_B_for_L(L: int) -> int:
    """Smallest ``B`` with ``2^B > 3^L`` (i.e. ``floor(L*log2 3) + 1``), exactly."""
    if L < 1:
        raise ValueError("L must be >= 1")
    return (3**L).bit_length()


def length_admissible(L: int, min_element: int, q: int = 1) -> bool:
    """Exact integer test of the Crandall squeeze for a candidate length ``L``.

    A cycle with ``L`` odd elements, all ``>= min_element``, needs some ``B`` with
    ``3^L < 2^B <= (3 + q/min_element)^L``.  In integers, with ``m = min_element``
    and ``B`` minimal::

        2^B * m^L  <=  (3m + q)^L

    Feasible only for very small ``L`` (it fails for every ``L`` once ``m`` is
    large), so this is a brute-force check for modest ``L``.
    """
    if min_element < 1:
        raise ValueError("min_element must be >= 1")
    B = min_B_for_L(L)
    return (1 << B) * min_element**L <= (3 * min_element + q) ** L


def smallest_admissible_length(
    min_element: int, q: int = 1, *, terms: int = 30, prec: int = 300
) -> tuple[int, int, Decimal]:
    """Smallest cycle length ``L`` not excluded by the Crandall squeeze.

    Returns ``(L, B, margin)`` where ``margin = eps - (B/L - log2 3) > 0`` is how
    much room is left, and ``eps = log2(1 + q/(3*min_element))``.

    Interpretation: any ``S_q``-cycle all of whose elements exceed
    ``min_element`` has at least ``L`` odd elements.  This is the *elementary*
    continued-fraction bound only.  The published state of the art for ``q = 1``
    (Hercher 2023, using Baker's theorem and heavy computation) is much stronger;
    do not quote this number as a new record.

    Raises ``ValueError`` if no candidate within ``terms`` CF terms qualifies --
    increase ``terms``.
    """
    ctx = getcontext().copy()
    ctx.prec = prec
    alpha = log2_3(prec)
    eps = ctx.ln(1 + ctx.divide(Decimal(q), Decimal(3 * min_element))) / ctx.ln(
        Decimal(2)
    )
    for p, L in best_upper_approximations(terms, prec):
        gap = ctx.subtract(ctx.divide(Decimal(p), Decimal(L)), alpha)
        if gap <= eps:
            return L, p, +(eps - gap)
    raise ValueError(
        f"no admissible length found within {terms} continued-fraction terms; "
        "increase `terms`"
    )


def cf_record_depths(max_k: int) -> list[int]:
    """Depths ``k`` where ``frac(k * log2 3)`` hits a record minimum.

    These are the depths where the T6 exponent budget ``floor(k*log2 3)`` is
    tightest -- convergent and semiconvergent denominators of ``log2 3``
    (``1, 2, 7, 12, 53, 359, 665, ...``).  Computed exactly with integers:
    ``frac(k*log2 3) = log2(3^k / 2^{floor(k log2 3)})``, and comparing two such
    values is comparing ``3^{k1} * 2^{e2}`` with ``3^{k2} * 2^{e1}``.
    """
    out: list[int] = []
    best: tuple[int, int] | None = None  # (3^k, 2^e) representing 3^k / 2^e in [1,2)
    for k in range(1, max_k + 1):
        e = (3**k).bit_length() - 1
        num, den = 3**k, 1 << e
        if best is None or num * best[1] < best[0] * den:
            best = (num, den)
            out.append(k)
    return out


def summarise_cycle(cycle: Cycle) -> dict[str, object]:
    """Everything T7 has to say about one concrete cycle."""
    return {
        "q": cycle.q,
        "L": cycle.L,
        "M": cycle.M,
        "min": cycle.min_element,
        "B": cycle.B,
        "c_L": cycle_constant(cycle),
        "2^B - 3^L": (1 << cycle.B) - 3**cycle.L,
        "cycle_equation": check_cycle_equation(cycle),
        "product_identity": product_identity(cycle),
        "B/L": Fraction(cycle.B, cycle.L),
    }


__all__ += ["cf_record_depths", "summarise_cycle"]
