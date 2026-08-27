"""Residue sieves on the largest odd element ``M`` of an ``S_q``-cycle.

Two independent sieves, both derived from the single fact that **every element
of the cycle is <= M**:

* **3-adic (backward).**  Walk backwards from ``M``.  Every ``y_j`` must be a
  positive odd integer ``<= M`` with ``3 | y_j`` false (T0).  Integrality of
  ``y_k = (2^{B_k} M - c_k)/3^k`` pins ``M`` modulo ``3^k``; the T0 test on the
  last element removes one lift, giving a condition modulo ``3^{k+1}``.
* **2-adic (forward).**  Walk forwards from ``M``.  Every ``x_j = (3^j M + d_j)/2^{A_j}``
  must be ``<= M``, i.e. ``M * (2^{A_j} - 3^j) >= d_j`` with ``d_j > 0``.  So
  ``2^{A_j} > 3^j``, i.e. ``A_j >= ceil(j * log2 3)``, is forced for **every**
  positive ``M`` -- no large-``M`` hypothesis (if ``2^{A_j} < 3^j`` then
  ``x_j = (3^j M + d_j)/2^{A_j} > 3^j M / 2^{A_j} > M`` outright).
  ``j = 1`` is exactly T1.

Named consequences for ``q = 1`` (all elementary; see the honesty note below):

===== ============================================ =========================
 id    statement                                    hypotheses
===== ============================================ =========================
 T1    ``M = 1 (mod 4)``                            none (M is a cycle max)
 T2    ``b_1 = 1``, so ``M = 2 (mod 3)``            ``M > q``
 T3    ``M = 5 (mod 12)``                           ``M > q``
 T4    ``M = 17 or 29 (mod 36)``                    ``M > q``
 T8    ``M != 9 (mod 16)``                          none (M is a cycle max)
 T8'   with T3: ``M = 5, 17, 29 (mod 48)``          ``M > q`` (inherited from T3)
===== ============================================ =========================

``M >= q`` is **not** enough for T2: ``M = q`` is a fixed point (``3q + q = 4q``,
so ``L = 1`` and ``b_1 = 2``) and then ``3 | 2M - q = q`` is false.  The
hypothesis has to be the strict ``M > q``.

General ``q`` forms: ``M = q (mod 4)``; ``M = 2q (mod 3)``; ``M = 5q (mod 12)``;
``M != 5q (mod 9)``.  These are homogeneous of degree 1 in ``q``, forced by the
scaling ``(M, q) -> (lam*M, lam*q)``.

**T4 does NOT recurse on its own.**  Applying T0 backwards repeatedly, with no
size condition, saturates immediately: the surviving set stays exactly
``M = 2, 8 (mod 9)`` lifted, at every depth, because 2 has order 6 mod 9 so a
legal ``b_{j+1}`` always exists.  Every further 3-adic gain comes from the size
bound ``y_k <= M`` (T6), not from T0.  The ground-truth doc's "Recurses to higher
powers of 3" is misleading and is contradicted by
:func:`surviving_residues_mod3_no_size`.

**Honesty note.**  None of this is new.  T0 is stated verbatim by Kaneda (2015)
and is why Tao's Syracuse map lives on the odds coprime to 3; T1 is Brox's
(*Acta Arith.* 92 (2000)) "descending" condition and the local-max structure of
Simons-de Weger (2005); the backward/forward exponent-vector sieve is the
standard Eliahou / Simons-de Weger / Terras machinery.  T3, T4, T5 and the
mod-16 refinement are one-line corollaries of that folklore that I could not
find written verbatim -- the weakest possible form of novelty.  Do not present
any of it as a result.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache

from .backtree import admissible_halving_vectors, backward_chains, c_constant
from .syracuse import check_q, syracuse_with_exponent

__all__ = [
    "Verdict",
    "t1_ok",
    "t2_residue_ok",
    "t3_ok",
    "t4_ok",
    "t8_ok",
    "surviving_residues_mod3",
    "surviving_residues_mod3_no_size",
    "surviving_residues_mod2",
    "combined_surviving_density",
    "can_be_max_odd",
]


# --------------------------------------------------------------------------
# named residue predicates (all q-general)
# --------------------------------------------------------------------------


def t1_ok(m: int, q: int = 1) -> bool:
    """T1: ``4 | 3M + q``, equivalently ``M = q (mod 4)``.

    Hypotheses: none beyond "``M`` is the maximum of an ``S_q``-cycle".
    Proof: ``S_q(M) <= M`` gives ``2^b >= 3 + q/M > 3`` hence ``b >= 2``.
    The ground-truth doc's ``M > q`` hypothesis is superfluous; in fact ``M < q``
    gives the *stronger* conclusion ``8 | 3M + q``.
    """
    return (3 * m + q) % 4 == 0


def t2_residue_ok(m: int, q: int = 1) -> bool:
    """T2 residue consequence: ``3 | 2M - q``, i.e. ``M = 2q (mod 3)``.

    Hypothesis: ``M > q``, strictly (then ``L >= 2`` and ``b_1 = 1``).  ``M >= q``
    is **not** enough: ``M = q`` is a fixed point with ``b_1 = 2``, and there
    ``2M - q = q`` is never divisible by 3.  Not implied by ``b_1 = 1`` alone
    -- the converse of T2 is false.
    """
    return (2 * m - q) % 3 == 0


def t3_ok(m: int, q: int = 1) -> bool:
    """T3: ``M = 5q (mod 12)``.  Hypothesis: ``M > q``.  (CRT of T1 and T2.)"""
    return m % 12 == (5 * q) % 12


def t4_ok(m: int, q: int = 1) -> bool:
    """T4: ``M != 5q (mod 9)``; with T3 this is ``M = 17q or 29q (mod 36)``.

    Hypothesis: ``M > q``.  Proof: ``y_1 = (2M - q)/3`` is on the cycle, so
    ``3 | y_1`` is false by T0, and ``3 | y_1`` iff ``2M = q (mod 9)``.
    Tight: cycles with ``M < q`` or ``L = 1`` do hit ``M = 5q (mod 9)``
    (e.g. ``q = 119``, cycle ``19 -> 11 -> 19``).
    """
    return m % 9 != (5 * q) % 9


def t8_ok(m: int, q: int = 1) -> bool:
    """T8 (``q = 1`` only): ``M != 9 (mod 16)``, hence ``M = 1, 5, 13 (mod 16)``.

    Hypotheses: none.  Proof for ``q = 1``: ``M = 16s + 9`` gives ``3M + 1 = 4(12s+7)``
    so ``x_1 = 12s + 7`` exactly, then ``3 x_1 + 1 = 2(18s + 11)`` so
    ``x_2 = 18s + 11 > 16s + 9 = M`` for every ``s >= 0``, contradicting maximality.

    For ``q != 1`` this exact argument does not carry over; use
    :func:`surviving_residues_mod2`, which redoes the computation for the given
    ``q``.
    """
    if q != 1:
        raise ValueError("t8_ok is proved only for q = 1; use surviving_residues_mod2")
    return m % 16 != 9


# --------------------------------------------------------------------------
# 3-adic sieve (backward)
# --------------------------------------------------------------------------


@lru_cache(maxsize=None)
def surviving_residues_mod3(depth: int, q: int = 1) -> tuple[int, tuple[int, ...]]:
    """Surviving residues of ``M`` modulo ``3^{depth+1}``, large-``M`` regime.

    Returns ``(modulus, sorted residues)``.

    Method.  For each T6-admissible backward halving vector (floor rule; see
    :func:`~collatz_maxodd.backtree.admissible_halving_vectors`) the chain is
    integral iff ``3^depth | 2^{B_k} M - c_k``, and the T0 test on the *last*
    element removes exactly one of the three lifts modulo ``3^{depth+1}``.  The
    intermediate T0 tests are automatic: ``y_j = (3 y_{j+1} + q)/2^{b_{j+1}}``
    is ``= q * 2^{-b} != 0 (mod 3)``.  Likewise integrality at level ``depth``
    implies it at every earlier level (2 is a 3-adic unit).  So each vector
    contributes exactly 2 classes, and survivors are their union.

    Validity: the floor rule is used for admissibility, so this is the
    ``M > floor_rule_safe_M(depth)`` statement (``M > 17344`` covers
    ``depth <= 19`` for ``q = 1``; see :func:`~collatz_maxodd.backtree.floor_rule_threshold`
    for the table and for why nothing is claimed beyond that).  Use
    :func:`can_be_max_odd` for an exact, unconditional test on a specific ``M``.

    Fixtures (``q = 1``): depth 1 -> ``{2, 8} (mod 9)``, which together with
    ``M = 1 (mod 4)`` is exactly T4's ``M = 17, 29 (mod 36)``.
    """
    check_q(q)
    if depth < 1:
        raise ValueError("depth must be >= 1")
    modulus = 3 ** (depth + 1)
    lower = 3**depth
    surv: set[int] = set()
    for bs in admissible_halving_vectors(depth, q):
        bk = sum(bs)
        ck = c_constant(bs, q)
        inv = pow(pow(2, bk, modulus), -1, modulus)
        killed = ck % modulus * inv % modulus  # the lift with 3 | y_k
        base = killed % lower
        for t in range(3):
            r = base + t * lower
            if r != killed:
                surv.add(r)
    return modulus, tuple(sorted(surv))


@lru_cache(maxsize=None)
def surviving_residues_mod3_no_size(
    depth: int, q: int = 1
) -> tuple[int, tuple[int, ...]]:
    """The same backward 3-adic sieve with T0 + T2 only -- **no** ``y_k <= M`` bound.

    ``b_1 = 1`` is imposed (T2, valid for ``M > q``); every later ``b_j`` is left
    free.  The result **saturates immediately**: the answer is always
    ``2 * 3^{depth-1}`` classes out of ``3^{depth+1}``, density ``2/9``, i.e.
    exactly the lift of ``M = 2q (mod 3)``, ``M != 5q (mod 9)``.

    Reason: with ``y_{j-1}`` a unit mod ``3^m``, the reachable set
    ``{(2^b y_{j-1} - q)/3}`` is *all* of ``Z/3^{m-1}`` -- 2 is a primitive root
    mod ``3^m``, so the admissible multipliers ``2^b`` fill an entire coset of the
    index-2 subgroup, and ``(u y - q)/3`` sweeps everything as ``u`` does.

    This is the concrete refutation of the ground-truth doc's "T4 recurses to
    higher powers of 3": *no* extra 3-adic information comes from T0 alone.
    Every further gain in :func:`surviving_residues_mod3` comes from the size
    bound ``y_k <= M``.

    Cost is ``O(3^{2*depth})``; intended for small depths (<= 6).
    """
    check_q(q)
    if depth < 1:
        raise ValueError("depth must be >= 1")
    modulus = 3 ** (depth + 1)
    surv: set[int] = set()
    for r in range(modulus):
        if r % 3 == 0:
            continue
        t = 2 * r - q  # b_1 = 1
        if t % 3 != 0:
            continue
        y1 = (t // 3) % (modulus // 3)
        if _free_chain_exists(y1, modulus // 3, depth - 1, q):
            surv.add(r)
    return modulus, tuple(sorted(surv))


def _free_chain_exists(y: int, mod: int, k: int, q: int) -> bool:
    """Is there a size-unconstrained backward continuation of ``k`` more steps?

    ``y`` is known modulo ``mod = 3^m``; each step divides the precision by 3.
    ``b`` is swept over a full period of 2 modulo ``mod`` (``2 * 3^{m-1}``).
    """
    if y % 3 == 0:
        return False
    if k == 0:
        return True
    nmod = mod // 3
    period = 2 * (mod // 3) if mod > 1 else 1
    for b in range(1, period + 1):
        t = (pow(2, b, mod) * y - q) % mod
        if t % 3 != 0:
            continue
        if _free_chain_exists((t // 3) % nmod, nmod, k - 1, q):
            return True
    return False


# --------------------------------------------------------------------------
# 2-adic sieve (forward)
# --------------------------------------------------------------------------


@lru_cache(maxsize=None)
def surviving_residues_mod2(a: int, q: int = 1) -> tuple[int, tuple[int, ...]]:
    """Surviving odd residues of ``M`` modulo ``2^a``.

    A class ``r`` is killed when knowledge of ``M mod 2^a`` alone already forces
    ``A_j < ceil(j * log2 3)`` for some ``j``, i.e. forces ``x_j > M``.

    **The kills are unconditional** (for ``q > 0``), not a large-``M`` statement:
    ``x_j 2^{A_j} = 3^j M + d_j`` with ``d_j > 0``, so ``2^{A_j} < 3^j`` gives
    ``x_j > M`` for every positive ``M``.  What is *not* unconditional is the
    converse: a surviving class need not contain any cycle maximum.

    ``q = 1`` fixtures: ``a = 2 -> {1}`` (this is T1), ``a = 3 -> {1, 5}``,
    ``a = 4 -> {1, 5, 13}`` (this is T8, the mod-16 refinement).  The sieve then
    saturates: its limiting density is ``0.2863153965...`` of the odd numbers,
    i.e. it is worth 1.80 bits and no more, however deep you go.
    """
    check_q(q)
    if a < 1:
        raise ValueError("a must be >= 1")
    modulus = 1 << a
    return modulus, tuple(r for r in range(1, modulus, 2) if _mod2_class_survives(r, a, q))


def _mod2_class_survives(r: int, a: int, q: int) -> bool:
    """True unless ``M = r (mod 2^a)`` already forces some ``x_j > M``."""
    cur, bits = r, a
    total = 0
    j = 0
    while bits >= 1:
        t = (3 * cur + q) % (1 << bits)
        if t == 0:
            return True  # v2 not determined by this many bits: undecided -> survives
        v = (t & -t).bit_length() - 1
        total += v
        j += 1
        if (1 << total) <= 3**j:  # 2^{A_j} < 3^j  =>  x_j > M, for every M > 0
            return False
        cur = ((3 * cur + q) >> v) % (1 << (bits - v))
        bits -= v
    return True


# --------------------------------------------------------------------------
# combination
# --------------------------------------------------------------------------


@lru_cache(maxsize=None)
def combined_residues(depth: int, a: int, q: int = 1) -> tuple[int, tuple[int, ...]]:
    """CRT of the two sieves: surviving ``M`` modulo ``4^... := 2^a * 3^{depth+1}``.

    ``q = 1`` landmarks reproduced by this function:

    * ``depth=1, a=2`` -> ``M = 17, 29 (mod 36)``            -- T4
    * ``depth=2, a=2`` -> ``M = 17, 29, 53, 101 (mod 108)``
    * ``depth=3, a=2`` -> ``M = 101, 125, 161, 233, 269, 317 (mod 324)``
    * ``depth=1, a=4`` -> ``M = 17, 29, 53, 65, 101, 125 (mod 144)``
    """
    m3, s3 = surviving_residues_mod3(depth, q)
    m2, s2 = surviving_residues_mod2(a, q)
    modulus = m2 * m3
    inv = pow(m3, -1, m2)
    out = sorted(
        (r3 + m3 * ((r2 - r3) * inv % m2)) % modulus for r3 in s3 for r2 in s2
    )
    return modulus, tuple(out)


def combined_surviving_density(depth: int, a: int, q: int = 1) -> float:
    """Joint density among **odd** ``M`` of surviving both sieves (CRT, coprime moduli).

    Caveat, stated in full: the product is exact as a statement about residue
    classes surviving two independently defined sieves.  It is a joint statement
    about an actual cycle only when ``L`` is large enough that the ``depth``
    backward elements and the forward elements used are distinct cycle elements.
    For a hypothetical large cycle that is harmless; for a short cycle the two
    sieves are not independent constraints.
    """
    m3, s3 = surviving_residues_mod3(depth, q)
    _, s2 = surviving_residues_mod2(a, q)
    return (len(s3) / m3) * (len(s2) / (1 << (a - 1)))


# --------------------------------------------------------------------------
# exact, unconditional test on one M
# --------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class Verdict:
    """Result of :func:`can_be_max_odd`.  Truthy iff ``M`` survives."""

    ok: bool
    reason: str | None = None

    def __bool__(self) -> bool:
        return self.ok


def can_be_max_odd(
    m: int,
    q: int = 1,
    depth: int | None = None,
    *,
    back_depth: int = 4,
    forward_depth: int = 4,
) -> Verdict:
    """Can ``m`` be the largest odd element of an ``S_q``-cycle?

    Returns a :class:`Verdict`, which is truthy/falsy as a ``bool``;
    ``verdict.reason`` is a string explaining a ``False``.  Passing ``depth``
    sets both ``back_depth`` and ``forward_depth``.

    Every test used is **exact and unconditional** -- no large-``M`` assumption,
    no assumption that ``b_1 = 1``:

    1. ``m`` positive odd with ``3 | m`` false (T0).
    2. Forward: ``x_j <= m`` and ``3 | x_j`` false for ``j <= forward_depth``.
       ``j = 1`` is T1.
    3. Backward: some chain ``y_1, ..., y_{back_depth}`` of positive odd integers
       ``<= m``, none divisible by 3, exists (T6 + T0).

    A ``True`` verdict means only "not excluded at this depth".
    """
    check_q(q)
    if depth is not None:
        back_depth = forward_depth = depth
    if m <= 0 or m % 2 == 0:
        return Verdict(False, f"M = {m} is not a positive odd number")
    if m % 3 == 0:
        return Verdict(False, f"T0: 3 divides M = {m}, so M has no odd predecessor")

    x = m
    for j in range(1, forward_depth + 1):
        x, aj = syracuse_with_exponent(x, q)
        if x > m:
            extra = " (this is T1: v2(3M+q) = 1)" if j == 1 and aj == 1 else ""
            return Verdict(
                False,
                f"forward: x_{j} = {x} > M = {m} (a_{j} = {aj}), "
                f"so M is not the cycle maximum{extra}",
            )
        if x % 3 == 0:  # pragma: no cover - impossible, S_q never hits 3Z
            return Verdict(False, f"T0: forward element x_{j} = {x} is divisible by 3")

    if back_depth > 0:
        for _ in backward_chains(m, q, back_depth):
            break
        else:
            return Verdict(
                False,
                f"T6/T0 backward: no chain y_1..y_{back_depth} of odd numbers <= M "
                f"avoiding multiples of 3 exists below M = {m}",
            )
    return Verdict(True)
