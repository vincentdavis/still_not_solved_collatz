"""Hercher's m-cycle elimination ladder, re-run with Barina's 2025 bound.

WHAT THIS MODULE IS.  An exact-rational reimplementation of the elimination
pipeline of C. Hercher, "There are no Collatz m-cycles with m <= 91", *J.
Integer Seq.* 26 (2023), Art. 23.3.5 (https://cs.uwaterloo.ca/journals/JIS/
VOL26/Hercher/hercher5.pdf), with every inequality certified by directed
rounding — no floats anywhere.  The pipeline consumes exactly the
(2,3)-specific magnitude inputs that docs/FILTER.md test E demands: the
continued fraction of ``log2(3)``, the verified convergence bound ``X_0``, and
positivity (``2^B > 3^L``, T7).

THE INGREDIENTS, with their sources pinned:

* **Theorem 16** (Hercher; after Eliahou 1993).  For an m-cycle with ``K`` odd
  and ``L`` even elements, ``delta < (K+L)/K < delta + (1/(3 K ln 2)) * sum_i
  T(n_i)``, where ``delta = log2(3)`` and ``T(n_i)`` sums reciprocals of the
  odd elements of ascent ``i``.
* **Corollary 17**: ``sum_i T(n_i) <= (97/54) * m / X_0``.
* **Theorem 21**: the ``m_2`` bootstrap.  If ``m_2 <= m`` satisfies
  ``((delta^{m_2}-1)/(delta-1)) * log2((162/97) X_0) <= (m_2/m) K``, then with
  ``v = (m_2/m) K (delta-1)/(delta^{m_2}-1)`` the window shrinks to
  ``(1/(3 K ln 2)) * ((97(m-m_2)+73)/(54 X_0) + 3/(2^v-1) +
  3(m_2-1)/((2^v-1)^delta))`` — with the better first terms ``3/X_0`` for
  ``m_2 = m-1`` and ``0`` for ``m_2 = m``.
* **Theorem 27**: ``sum_i T(n_i) <= K * (3/4) / X_0``, K-free window
  ``(1/(4 ln 2)) / X_0``.  Per Remark 31 this scales with ``X_0`` (its case
  analysis needs only ``X_0 > 765``), unlike Corollaries 19/24/29, which are
  frozen at their published ``X_0``.
* **Lemma 22** (classical): every fraction in an open interval has denominator
  at least that of the *simplest* fraction in the interval — computed here by
  the exact Stern-Brocot walk, on a rational interval that *encloses*
  ``(delta, delta + width)``.
* **Simons & de Weger**, "Theoretical and computational bounds for m-cycles of
  the 3n+1 problem", v1.44 (2010), Theorem 3 (updating *Acta Arith.* 117
  (2005) 51-70): no m-cycles for ``m <= 75``; for ``m = 76, 77`` only listed
  solutions with ``x_min < 4.3e19`` (dead against any ``X_0`` beyond that);
  ``K > 1.1173e17`` for ``78 <= m <= 90``; and for ``91 <= m <= 515619``
  the bracket ``7.5311e11 < K < 1.4784 * m * delta^m``.  The upper bound is
  the single place Baker's theorem enters.
* **Hercher, Corollary 24 / Table 1**: valid starting bounds, e.g. any m-cycle
  with ``m <= 98`` has ``K > 7.76e19`` (proved at ``X_0 = 695 * 2^60``; lower
  bounds only improve with ``X_0``).
* **X_0**: Barina, *J. Supercomputing* 81 (2025) art. 810 verifies convergence
  below ``2^71 = 2048 * 2^60`` (the *published* figure; the page dates that
  milestone 2025-01-15).  The project page (https://pcbarina.fit.vutbr.cz/,
  retrieved 2026-08) reports ``2075 * 2^60`` as its current limit.  The two
  are distinguished everywhere below; headline results use the published one.

WHAT IS NEW HERE (and what is not).  Nothing in the mathematics is new: every
theorem is Hercher's or Simons-de Weger's, and Remark 25/31 of Hercher's paper
explicitly predicts that better ``X_0`` values push the ladder further.  What
this module adds is the *execution* of that prediction with the 2025 bound —
``X_0`` grew by a factor ``2048/695 = 2.95`` since publication — plus a
regression harness that first reproduces the paper's own printed iterates at
``X_0 = 695 * 2^60`` before touching the new value.  Results appear in
docs/GROUND_TRUTH.md §7 ("The Hercher ladder, re-run"); the honest failure
mode of any run is recorded next to the claim it fails.

Everything decision-bearing is an inequality between exact rationals; where a
transcendental quantity appears (``log2 3``, ``ln 2``, ``2^v``, ``x^delta``)
it is replaced by a certified rational bound in the direction that WEAKENS the
conclusion, so a "dead" verdict here is a theorem modulo the cited inputs.
"""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
from typing import NamedTuple

__all__ = [
    "BARINA_PAPER_X0",
    "BARINA_PAGE_X0",
    "HERCHER_PUBLICATION_X0",
    "log2_bounds",
    "delta_bounds",
    "ln2_bounds",
    "simplest_in_open",
    "min_denominator_beyond",
    "window_width",
    "ladder",
    "eliminate",
    "eliminate_all",
    "allm_bound",
    "rung_table",
    "required_x0_for_next_m",
]

#: X_0 at Hercher's publication (his Definition 4): Barina 2021/2023 frontier.
HERCHER_PUBLICATION_X0 = 695 * 2**60
#: The figure in Barina's *published* 2025 paper (J. Supercomputing 81:810).
BARINA_PAPER_X0 = 2048 * 2**60  # = 2^71
#: The figure on Barina's project page (current limit, retrieved 2026-08).
#: Not in print — the paper's own figure is BARINA_PAPER_X0.
BARINA_PAGE_X0 = 2075 * 2**60

#: S&dW 2010 Thm 3: K < 1.4784 * m * delta^m for 91 <= m <= 515619.
SDW_CEILING_COEFF = Fraction(14784, 10000)
SDW_CEILING_RANGE = (91, 515619)
#: S&dW 2010 Thm 3: K > 7.5311e11 for 91 <= m <= 515619 (Hercher quotes 7e11).
SDW_LOWER_K_91_PLUS = 753_110_000_000
#: Hercher Cor. 24 / Table 1 rows usable as starting lower bounds (m <= key).
#: Lower bounds on K only — they remain valid as X_0 grows (Remark 31).
COR24_STARTS = (
    (98, 77_600_000_000_000_000_000),
    (117, 27_400_000_000_000_000_000),
    (276, 4_680_000_000_000_000_000),
    (3079, 397_000_000_000_000_000),
    (12055, 130_000_000_000_000_000),
    (948_987, 4_300_000_000_000_000),
    (1_140_000, 3_810_000_000_000_000),
)


# --------------------------------------------------------------------------
# certified transcendental bounds
# --------------------------------------------------------------------------


def log2_bounds(x: Fraction | int, fbits: int = 320) -> tuple[Fraction, Fraction]:
    """Certified rational bracket ``lo <= log2(x) <= hi`` with ``hi - lo``
    at most about ``2^(1-fbits)``.

    Binary-digit extraction with interval fixed-point arithmetic: scale ``x``
    into ``[1, 2)``, then repeatedly square, keeping a lower channel rounded
    down and an upper channel rounded up; every digit the two channels agree
    on is a true binary digit of the fractional part.  Soundness does not
    depend on how many digits are produced — the returned bracket is valid
    whenever the loop stops.
    """
    x = Fraction(x)
    if x <= 0:
        raise ValueError("x must be positive")
    e, y = 0, x
    while y >= 2:
        y /= 2
        e += 1
    while y < 1:
        y *= 2
        e -= 1
    assert 1 <= y < 2
    P = fbits + 64
    one, two = 1 << P, 2 << P
    ylo = (y.numerator << P) // y.denominator
    yhi = -((-(y.numerator << P)) // y.denominator)
    f, t = 0, 0
    while t < fbits:
        ylo = (ylo * ylo) >> P
        yhi = -((-(yhi * yhi)) >> P)
        d_lo, d_hi = ylo >= two, yhi >= two
        if d_lo != d_hi:
            break
        f, t = 2 * f + d_lo, t + 1
        if d_lo:
            ylo >>= 1
            yhi = -((-yhi) >> 1)
        if yhi >= (one << 2):  # pragma: no cover - defensive; cannot occur
            break
    scale = Fraction(1, 1 << t)
    return e + f * scale, e + (f + 1) * scale


@lru_cache(maxsize=None)
def delta_bounds(fbits: int = 320) -> tuple[Fraction, Fraction]:
    """``delta = log2(3)``, bracketed to ``2^(1-fbits)``."""
    return log2_bounds(3, fbits)


@lru_cache(maxsize=None)
def ln2_bounds(terms: int = 80) -> tuple[Fraction, Fraction]:
    """``ln 2 = 2 atanh(1/3)``, bracketed by a partial sum and its tail bound.

    ``atanh(1/3) = sum_{n>=0} 3^-(2n+1)/(2n+1)``; the dropped tail is below
    ``(9/8) * 3^-(2N+1)/(2N+1)`` by the geometric bound.
    """
    s = Fraction(0)
    for n in range(terms):
        s += Fraction(1, (2 * n + 1) * 3 ** (2 * n + 1))
    tail = Fraction(9, 8) * Fraction(1, (2 * terms + 1) * 3 ** (2 * terms + 1))
    return 2 * s, 2 * (s + tail)


def _pow2_lower(v: Fraction) -> Fraction:
    """A rational lower bound for ``2^v``, ``v >= 0``: ``2^floor(v) * (1 + f ln2)``.

    Clamped at ``2^600`` — still a valid lower bound for any larger ``v``, and
    it keeps a runaway ladder iterate from materializing ``2^(10^29)``.
    """
    if v >= 600:
        return Fraction(2) ** 600
    n = v.numerator // v.denominator
    frac = v - n
    return Fraction(2) ** n * (1 + frac * ln2_bounds()[0])


def _rpow_lower(x: Fraction, exp_lo: Fraction) -> Fraction:
    """A rational lower bound for ``x^e`` with ``x > 1``, ``e >= exp_lo > 0``:
    ``2^floor(e_lo * log2_lo(x))``.

    ``x > 1`` is load-bearing: for ``x < 1`` the direction FLIPS (log2 x < 0),
    so it is asserted rather than assumed — the audit showed the bad case is
    reachable through ``window_width`` only at absurd ``X0 <= 3``, which the
    ``X0 > 765`` gate now excludes, but the certification should not hang on
    that chain silently."""
    if x <= 1:
        raise ValueError("_rpow_lower needs x > 1; the bound flips below 1")
    lx = log2_bounds(x, 96)[0]
    e = (exp_lo * lx).numerator // (exp_lo * lx).denominator
    return Fraction(2) ** e


# --------------------------------------------------------------------------
# Lemma 22: the simplest fraction in an open interval, exactly
# --------------------------------------------------------------------------


def simplest_in_open(a: Fraction, b: Fraction) -> Fraction:
    """A smallest-denominator fraction in the open interval ``(a, b)``.

    Exact Stern-Brocot / continued-fraction walk; ``0 <= a < b`` required.
    Every rational in ``(a, b)`` has denominator ``>=`` the result's — this is
    Hercher's Lemma 22 in executable form (and the classical "simplest
    rational" algorithm).  Minimality is exercised against brute force in the
    tests.  (Not always unique: an interval containing two integers has many
    denominator-1 members; the intervals this module builds never do.)
    """
    if not 0 <= a < b:
        raise ValueError("need 0 <= a < b")
    ia = a.numerator // a.denominator
    cand = Fraction(ia + 1)
    if a < cand < b:
        return cand
    fa, fb = a - ia, b - ia
    if fa == 0:
        # (0, fb): the simplest is 1/ceil-ish — smallest q with 1/q < fb
        q = fb.denominator // fb.numerator + 1
        return ia + Fraction(1, q)
    inner = simplest_in_open(1 / fb, 1 / fa)
    return ia + 1 / inner


def min_denominator_beyond(width: Fraction, fbits: int = 320) -> tuple[int, Fraction]:
    """Lemma 22 applied to the window ``(delta, delta + width)``.

    Returns ``(q, f)``: the simplest fraction ``f`` in a rational interval
    that ENCLOSES the true window — ``(delta_lo, delta_hi + width)`` — and its
    denominator ``q``.  Every fraction in the true window lies in the
    enclosure, so a cycle's ``(K+L)/K`` has reduced denominator ``>= q``,
    hence ``K >= q``.  Enclosure can only weaken the bound, never break it.
    """
    dlo, dhi = delta_bounds(fbits)
    f = simplest_in_open(dlo, dhi + width)
    return f.denominator, f


# --------------------------------------------------------------------------
# certified window widths
# --------------------------------------------------------------------------


class Width(NamedTuple):
    """A certified upper bound on the Theorem-16 window width, with provenance."""

    value: Fraction
    rule: str  # 'thm21(m2=..)' | 'cor17' | 'cor19' | 'thm27'
    m2: int


def _premised_m2(K: int, m: int, X0: int, fbits: int) -> int:
    """The largest ``m_2 <= m`` whose Theorem-21 premise is certified true.

    Premise: ``((delta^{m_2}-1)/(delta-1)) * log2((162/97) X_0) <= (m_2/m) K``,
    checked with upper bounds on the left (``delta_hi`` powers, ``log2`` upper)
    and the exact rational right — so a "yes" here implies the real premise.
    Returns 0 when none qualifies.
    """
    dlo, dhi = delta_bounds(fbits)
    l2hi = log2_bounds(Fraction(162 * X0, 97), 96)[1]
    pw = Fraction(1)
    best = 0
    for m2 in range(1, m + 1):
        pw *= dhi  # pw = delta_hi ^ m2
        lhs = (pw - 1) / (dlo - 1) * l2hi
        if lhs <= Fraction(m2, m) * K:
            best = m2
        else:
            break  # lhs grows geometrically, rhs linearly: no later m2 works
    return best


def window_width(
    K: int,
    m: int,
    X0: int,
    *,
    fbits: int = 320,
    allow_cor19: bool = False,
) -> Width:
    """The best certified window width available at lower bound ``K``.

    Minimum of Theorem 27 (K-free), Corollary 17, Theorem 21 with the largest
    premised ``m_2`` (using the sharper ``m_2 = m`` / ``m-1`` forms), and —
    only when ``allow_cor19`` and ``X0 >= 695*2^60`` — Corollary 19, whose
    constant ``7/5`` is frozen at the published ``X_0`` (Remark 31) and is
    used here solely to regress against Table 1.

    ``X0 > 765`` is required: Hercher's Remark 31 records that every
    X0-generic case analysis (Lemma 26 behind Theorem 27 included) needs it.
    Real inputs are ~10^21, so the gate only guards against nonsense calls —
    which, per the audit, are also the only calls that could reach
    ``_rpow_lower`` below 1.

    NOT monotone in ``X0`` in general: the Theorem-21 premise contains
    ``log2((162/97) X0)``, which GROWS with ``X0``, so the certified ``m_2``
    can DROP as ``X0`` rises and the width can jump up (demonstrated:
    at ``K = 7 941 964 418 702 608 664 581``, ``m = 99``, the width jumps by
    1.64x as ``X0`` crosses ~6090*2^60).  With ``m_2`` fixed it IS
    non-increasing in ``X0`` and in ``K`` — piecewise monotone only.
    """
    if X0 <= 765:
        raise ValueError("X0 > 765 required (Hercher Remark 31 side condition)")
    dlo, dhi = delta_bounds(fbits)
    ln2lo = ln2_bounds()[0]
    inv3ln2K = 1 / (3 * ln2lo * K)

    cands = [
        Width(Fraction(1, 4) / (ln2lo * X0), "thm27", 0),
        Width(Fraction(97 * m, 54 * X0) * inv3ln2K, "cor17", 0),
    ]
    if allow_cor19:
        if X0 < 695 * 2**60:
            raise ValueError("Corollary 19 requires X0 >= 695 * 2^60")
        cands.append(
            Width(
                Fraction(7 * m, 5 * 695 * 2**60) * inv3ln2K, "cor19", 0
            )
        )

    m2 = _premised_m2(K, m, X0, fbits)
    if m2 >= 1:
        v_lo = Fraction(m2, m) * K * (dlo - 1) / (dhi**m2 - 1)
        p2 = _pow2_lower(v_lo) - 1
        term2 = Fraction(3) / p2
        term3 = (
            Fraction(3 * (m2 - 1)) / _rpow_lower(p2, dlo) if m2 > 1 else Fraction(0)
        )
        if m2 == m:
            term1 = Fraction(0)
        elif m2 == m - 1:
            term1 = Fraction(3, X0)
        else:
            term1 = Fraction(97 * (m - m2) + 73, 54 * X0)
        cands.append(Width((term1 + term2 + term3) * inv3ln2K, "thm21", m2))

    best = min(cands, key=lambda w: w.value)
    return best


# --------------------------------------------------------------------------
# the ladder
# --------------------------------------------------------------------------


class Rung(NamedTuple):
    """One ladder iterate: the rule and m_2 used, the width, the new K bound."""

    m2: int
    rule: str
    width: Fraction
    K: int


def sdw_ceiling(m: int, fbits: int = 320) -> Fraction:
    """Certified UPPER bound for S&dW's ceiling ``1.4784 * m * delta^m``.

    Valid for ``91 <= m <= 515619`` (their Theorem 3(d)); raises outside.
    """
    lo, hi = SDW_CEILING_RANGE
    if not lo <= m <= hi:
        raise ValueError(f"S&dW ceiling only imported for {lo} <= m <= {hi}")
    return SDW_CEILING_COEFF * m * delta_bounds(fbits)[1] ** m


def ladder(
    m: int,
    X0: int,
    K_start: int,
    *,
    max_iter: int = 60,
    fbits: int = 320,
    allow_cor19: bool = False,
    stop_at: Fraction | None = None,
) -> list[Rung]:
    """Iterate width -> Lemma 22 -> new K until the bound stops improving.

    Every rung is a theorem: "an m-cycle (exactly ``m`` minima) with all
    elements above ``X0`` has ``K >=`` this rung", given ``K > K_start``.
    (``>=``, not ``>``: Lemma 22 bounds the REDUCED denominator of
    ``(K+L)/K``, and ``K`` is a multiple of it — equality is possible when
    ``gcd(K, L) = 1``.  ``eliminate`` only needs ``>=``: its contradiction is
    ``K >= rung > ceiling_upper >= true ceiling > K``.)
    ``stop_at`` (normally the S&dW ceiling) halts the climb once crossed —
    further rungs would be vacuous for a dead ``m``.
    """
    out: list[Rung] = []
    K = K_start
    for _ in range(max_iter):
        if stop_at is not None and K > stop_at:
            break
        w = window_width(K, m, X0, fbits=fbits, allow_cor19=allow_cor19)
        q, _f = min_denominator_beyond(w.value, fbits)
        if q <= K:
            break
        out.append(Rung(w.m2, w.rule, w.value, q))
        K = q
    return out


class Verdict(NamedTuple):
    """Elimination outcome for one ``m``."""

    m: int
    dead: bool
    K_final: int
    ceiling: Fraction
    rungs: tuple[Rung, ...]


def _start_for(m: int) -> int:
    """The best imported starting lower bound on K for exactly-``m`` cycles.

    The S&dW bracket row holds only for ``91 <= m <= 515619`` — both ends
    checked (the audit caught a version that ignored the upper end; it was
    masked by ``sdw_ceiling`` raising first, but latent for direct callers).
    """
    best = SDW_LOWER_K_91_PLUS if SDW_CEILING_RANGE[0] <= m <= SDW_CEILING_RANGE[1] else 0
    for bound_m, k in COR24_STARTS:
        if m <= bound_m and k > best:
            best = k
    if best == 0:
        raise ValueError(f"no imported starting bound covers m = {m}")
    return best


def eliminate(m: int, X0: int, *, fbits: int = 320) -> Verdict:
    """Run the ladder for exactly-``m`` cycles and compare with S&dW's ceiling.

    ``dead=True`` is the theorem "there is no m-cycle with exactly ``m``
    minima", modulo the imported inputs (S&dW Thm 3, Hercher Thm 16/21/27 +
    Cor 24, and convergence verified below ``X0``).
    """
    K0 = _start_for(m)
    ceil_up = sdw_ceiling(m, fbits)
    rungs = ladder(m, X0, K0, fbits=fbits, stop_at=ceil_up)
    K = rungs[-1].K if rungs else K0
    return Verdict(m, Fraction(K) > ceil_up, K, ceil_up, tuple(rungs))


def eliminate_all(X0: int, m_from: int = 92, *, fbits: int = 320) -> list[Verdict]:
    """Climb ``m = m_from, m_from+1, ...`` until the first survivor.

    Returns the verdicts including the first ``dead=False`` one.  The largest
    ``dead`` entry is the new ``M*``: no m-cycles with ``m <= M*`` (using
    Hercher's own ``m <= 91`` below ``m_from``).
    """
    out: list[Verdict] = []
    m = m_from
    while True:
        v = eliminate(m, X0, fbits=fbits)
        out.append(v)
        if not v.dead:
            return out
        m += 1


# --------------------------------------------------------------------------
# the m-free bound and the rung table
# --------------------------------------------------------------------------


def allm_bound(X0: int, fbits: int = 320) -> tuple[int, Fraction, Fraction]:
    """The X_0-scalable, m-free bound: Theorem 27's window + Lemma 22.

    Returns ``(K, f, width)``: every nontrivial cycle (any ``m``) has ``K >=
    K`` odd elements.  This is the honest scalable analog of Hercher's
    Corollary 29 — Cor 29 itself certifies more (``K > 1.375e11`` once ``X_0
    >= 1536*2^60``) via a frozen five-week C++ case analysis this module does
    not reproduce.
    """
    w = Fraction(1, 4) / (ln2_bounds()[0] * X0)
    q, f = min_denominator_beyond(w, fbits)
    return q, f, w


def rung_table(max_denominator: int = 10**25, fbits: int = 320) -> list[dict]:
    """The ladder's rungs: best upper approximations of ``delta`` by denominator.

    Walks Lemma 22 outward: each rung is the simplest fraction strictly between
    ``delta`` and the previous rung.  For each rung ``f = p/q`` the entry
    records the window width at which the all-m bound reaches ``q`` (namely
    ``width < f_prev - delta``) and the ``X_0`` Theorem 27 would need for it,
    in units of ``2^60`` — the "verification cost of the next theorem".
    """
    dlo, dhi = delta_bounds(fbits)
    ln2lo, ln2hi = ln2_bounds()
    rungs: list[dict] = []
    hi = dhi + 1
    prev: Fraction | None = None
    while True:
        f = simplest_in_open(dlo, hi)
        q = f.denominator
        if prev is not None:
            # to *reach* rung q (K >= q), the window must exclude prev:
            # width <= prev - delta; X0 >= (1/(4 ln2)) / (prev - delta_hi)
            gap_lo = prev - dhi
            x0_needed = Fraction(1, 4) / (ln2lo * gap_lo)
            rungs.append(
                {
                    "K": q,
                    "fraction": f,
                    "max_width": gap_lo,
                    "x0_needed": x0_needed,
                    "x0_needed_2p60": x0_needed / 2**60,
                }
            )
        if q > max_denominator:
            return rungs
        prev, hi = f, f


def required_x0_for_next_m(
    m: int,
    *,
    lo_units: int = 1,
    hi_units: int = 10**7,
    fbits: int = 320,
    certify: bool = False,
) -> int:
    """The smallest ``X_0`` (in units of ``2^60``) at which ``eliminate(m)``
    succeeds — the verification cost at which THIS pipeline pushes the
    theorem one more ``m``.  Two honesty limits, both audit-taught:

    * **This is the certified pipeline's threshold, not a necessity claim
      about mathematics.**  Sharper arithmetic or program-grade constants
      (Cor. 29-style case analysis) eliminate the same ``m`` at smaller
      ``X_0`` — an uncertified sharp evaluation of the very same theorems
      puts m = 92 near ``1.5e4 * 2^60`` against this function's 15905.
    * **Binary search alone does not certify minimality**, because the
      verdict is only piecewise monotone in ``X_0`` (see ``window_width``:
      the Theorem-21 premise's ``log2`` term grows with ``X_0``).  The search
      finds a candidate; ``certify=True`` then re-runs ``eliminate`` at EVERY
      integer ``u`` below it (exhaustive, slow — minutes for m = 92) and
      raises if any smaller ``u`` already succeeds.  An exhaustive scan for
      m = 92 over ``u <= 17500`` found the verdict flip exactly once, at
      15905, so the default remains fast search + spot checks in the tests.
    """
    if eliminate(m, hi_units * 2**60, fbits=fbits).dead is False:
        raise ValueError(f"m={m} not eliminated even at X0 = {hi_units}*2^60")
    lo, hi = lo_units, hi_units
    while lo < hi:
        mid = (lo + hi) // 2
        if eliminate(m, mid * 2**60, fbits=fbits).dead:
            hi = mid
        else:
            lo = mid + 1
    if certify:
        for u in range(max(lo_units, 766 // 2**60 + 1), lo):
            if eliminate(m, u * 2**60, fbits=fbits).dead:
                raise AssertionError(
                    f"non-monotone flip: m={m} already eliminated at u={u} < {lo}"
                )
    return lo
