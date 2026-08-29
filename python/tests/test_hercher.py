"""The Hercher ladder: regression against the paper, then the 2025 re-run.

REGRESSION FIRST (the module's contract): at Hercher's own ``X_0 = 695·2^60``
the pipeline must reproduce his printed Theorem-23 iterates *exactly* — the
``m_2`` sequence 47, 67, 77, 82, 86, 88, 91 and every K rung — before any new
``X_0`` is trusted.  Two independent published computations are also used as
fixtures: Simons–de Weger's m = 76/77 candidate K values (their Theorem 3(c))
must appear among the rung denominators, and Hercher's Remark 28 threshold
``2836·2^60`` must reproduce from the rung table.

THE 2025 RESULT (the honest one — the referee's predicted fallback, not the
bet): Barina's published ``X_0 = 2^71`` does NOT eliminate m = 92.  The ladder
stalls at ``K >= 2.0563×10^20`` against a ceiling of ``3.43×10^20``; this
pipeline's threshold for m = 92 is ``X_0 = 15905·2^60 ≈ 1.83×10^22`` (a
pipeline threshold, not a necessity theorem — sharper arithmetic crosses near
``1.5×10^4·2^60``).  What the new ``X_0`` does buy is four strictly improved
Table-1 rows (see ``test_new_rows``).
"""

from __future__ import annotations

from fractions import Fraction

import pytest

from collatz_maxodd.hercher import (
    BARINA_PAGE_X0,
    BARINA_PAPER_X0,
    HERCHER_PUBLICATION_X0,
    allm_bound,
    delta_bounds,
    eliminate,
    ladder,
    ln2_bounds,
    min_denominator_beyond,
    required_x0_for_next_m,
    rung_table,
    sdw_ceiling,
    simplest_in_open,
    window_width,
)

# Hercher, Theorem 23: the printed ladder at X_0 = 695·2^60, start K > 7e11.
HERCHER_M2_SEQUENCE = [47, 67, 77, 82, 86, 88, 91]
HERCHER_PRINTED_WIDTHS = [6.9e-32, 5.1e-36, 4.1e-38, 2.3e-39, 2.3e-40, 5.3e-41, 1.11e-43]
LADDER_RUNGS = [
    5_267_319_278_509_397,            # printed 5.2e15
    397_560_349_370_386_783,          # printed 3.97e17
    4_640_282_259_296_926_456,        # printed 4.64e18
    27_444_133_206_411_171_953,       # printed 2.74e19
    77_692_117_359_936_589_403,       # printed 7.76e19
    205_632_218_873_398_596_256,      # printed 2.05e20
    7_941_964_418_702_608_664_581,    # printed 7.94e21
]

# Simons–de Weger 2010, Theorem 3(c): the K values of the only possible
# m = 76, 77 cycles.  Best-approximation denominators, computed by them with
# lattice reduction — they must appear among this module's rungs.
SDW_76_77_K = [
    117_972_833_293_231_014,
    124_207_383_220_472_977,
    130_441_933_147_714_940,
]


# ---------------------------------------------------------------------------
# certified primitives
# ---------------------------------------------------------------------------


def test_delta_bracket_against_integer_power_facts():
    """The log2(3) bracket must respect exact 2^p vs 3^q comparisons."""
    dlo, dhi = delta_bounds()
    assert dhi - dlo < Fraction(1, 2**300)
    # 65/41 is an upper best approximation: 2^65 > 3^41, so delta < 65/41
    assert 2**65 > 3**41 and dhi < Fraction(65, 41)
    # 84/53 is a lower one: 2^84 < 3^53, so delta > 84/53
    assert 2**84 < 3**53 and dlo > Fraction(84, 53)


def test_ln2_bracket():
    lo, hi = ln2_bounds()
    assert Fraction(693147, 10**6) < lo < hi < Fraction(693148, 10**6)


def test_simplest_in_open_fixed_cases():
    assert simplest_in_open(Fraction(1, 3), Fraction(1, 2)) == Fraction(2, 5)
    assert simplest_in_open(Fraction(3, 2), Fraction(5, 2)) == Fraction(2)
    assert simplest_in_open(Fraction(0), Fraction(1, 7)) == Fraction(1, 8)


def test_simplest_in_open_brute_force_minimality():
    """No fraction with a smaller denominator fits in the interval."""
    import random

    rng = random.Random(7)
    for _ in range(60):
        a = Fraction(rng.randint(0, 90), rng.randint(1, 30))
        b = a + Fraction(rng.randint(1, 9), rng.randint(10, 30))
        f = simplest_in_open(a, b)
        assert a < f < b
        for q in range(1, f.denominator):
            lo = a.numerator * q // a.denominator
            hi = b.numerator * q // b.denominator + 1
            for p in range(lo, hi + 1):
                assert not (a < Fraction(p, q) < b), (a, b, f, p, q)


# ---------------------------------------------------------------------------
# the regression: Hercher's printed ladder, exactly
# ---------------------------------------------------------------------------


@pytest.fixture(scope="module")
def hercher_ladder():
    return ladder(
        91, HERCHER_PUBLICATION_X0, 700_000_000_000, stop_at=sdw_ceiling(91)
    )


def test_regression_m2_sequence(hercher_ladder):
    assert [r.m2 for r in hercher_ladder] == HERCHER_M2_SEQUENCE


def test_regression_rungs_exact(hercher_ladder):
    assert [r.K for r in hercher_ladder] == LADDER_RUNGS


def test_regression_widths_match_printed(hercher_ladder):
    """Our widths are certified UPPER bounds; they must sit within 30% above
    Hercher's printed (rounded, uncertified) values and never below 90%."""
    for rung, printed in zip(hercher_ladder, HERCHER_PRINTED_WIDTHS):
        ratio = float(rung.width) / printed
        assert 0.9 <= ratio <= 1.3, (rung, printed, ratio)


def test_regression_kills_m_91(hercher_ladder):
    """The final rung beats the S&dW ceiling: no m-cycles with m <= 91
    (Hercher's Main Theorem), reproduced end to end in exact arithmetic."""
    assert hercher_ladder[-1].K > sdw_ceiling(91)
    assert eliminate(91, HERCHER_PUBLICATION_X0).dead


def test_sdw_76_77_candidates_are_rungs():
    """S&dW's lattice-reduction K values for m = 76/77 appear verbatim among
    the best-approximation denominators — two teams, one number."""
    ks = {r["K"] for r in rung_table(10**18)}
    for k in SDW_76_77_K:
        assert k in ks


# ---------------------------------------------------------------------------
# the 2025 re-run
# ---------------------------------------------------------------------------


def test_m92_survives_barina_2025():
    """The honest headline: X_0 = 2^71 does NOT eliminate m = 92.

    The ladder stalls one rung short: to certify m_2 = 92 the premise needs
    K >= 3.093e20 (exactly 309 300 189 283 732 030 081 — an audit caught the
    hand-rounded 3.07e20 that dropped the 162/97 factor), but the best
    reachable rung is 2.0563e20, and at m_2 = 91 the X_0 term of the width
    (~3.15/X_0) cannot get under the next rung's gap (6.245e-43).  So
    Hercher's m <= 91 stands, and the stall value is itself a theorem: any
    92-cycle has K >= 2.0563×10^20.
    """
    v = eliminate(92, BARINA_PAPER_X0)
    assert not v.dead
    assert v.K_final == 205_632_218_873_398_596_256
    assert v.K_final < v.ceiling
    # the website figure does not change the verdict
    assert not eliminate(92, BARINA_PAGE_X0).dead


def test_m92_improvement_is_barina_driven():
    """At Hercher's X_0 the m = 92 ladder stalls a full rung lower — the
    2.65× gain is the new verification bound at work, not our arithmetic."""
    assert (
        eliminate(92, HERCHER_PUBLICATION_X0).K_final
        == 77_692_117_359_936_589_403
    )


def test_new_rows():
    """Four strictly improved Table-1 rows at X_0 = 2^71 (published values:
    m<=98 -> 7.76e19, m<=117 -> 2.74e19, m<=276 -> 4.68e18)."""
    # m <= 100: K > 2.0563e20  (was m <= 98: 7.76e19)
    for m in (92, 100):
        assert eliminate(m, BARINA_PAPER_X0).K_final == 205_632_218_873_398_596_256
    # m <= 124: K > 7.7692e19  (was m <= 117: 2.74e19)
    for m in (101, 124):
        assert eliminate(m, BARINA_PAPER_X0).K_final == 77_692_117_359_936_589_403
    # m <= 187: K > 2.7444e19  (the 2.74e19 band stretches 117 -> 187)
    for m in (125, 187):
        assert eliminate(m, BARINA_PAPER_X0).K_final == 27_444_133_206_411_171_953
    # 188..276: the ladder adds nothing over the published 4.68e18 start
    assert eliminate(188, BARINA_PAPER_X0).K_final == 4_680_000_000_000_000_000
    # the fourth improved row: 277 <= m (checked to 400): K > 4.6403e18,
    # where the published table has only 3.97e17 (its m <= 3079 row)
    for m in (277, 400):
        assert eliminate(m, BARINA_PAPER_X0).K_final == 4_640_282_259_296_926_456
    assert eliminate(277, HERCHER_PUBLICATION_X0).K_final != 4_640_282_259_296_926_456


def test_m92_verification_cost():
    """This pipeline eliminates m = 92 exactly from X_0 = 15905·2^60 up.

    Scoped claims only (both audit-taught): (a) it is the CERTIFIED
    pipeline's threshold, not a necessity theorem — uncertified sharp
    evaluation of the same theorems crosses near 1.5e4·2^60; (b) the verdict
    is only piecewise monotone in X_0, so minimality is certified by the
    ``certify`` scan (windowed here; an exhaustive scan to u = 17500 found
    the single flip at 15905), not by binary search alone."""
    u = required_x0_for_next_m(92)
    assert u == 15905
    assert eliminate(92, u * 2**60).dead
    assert not eliminate(92, (u - 1) * 2**60).dead
    # certify-scan a window below the threshold: no earlier dead island
    assert required_x0_for_next_m(92, lo_units=15800, certify=True) == 15905
    # spot checks across the domain, including the premise-flip region ~407
    for uu in (407, 408, 1_000, 10_000):
        assert not eliminate(92, uu * 2**60).dead
    for uu in (20_000, 10**6):
        assert eliminate(92, uu * 2**60).dead


def test_m92_premise_threshold_exact():
    """The Thm-21 premise first certifies m_2 = 92 at
    K = 309 300 189 283 732 030 081 ~ 3.093e20 (X_0 = 2^71) — above the
    2.0563e20 stall rung and below the 3.43e20 ceiling, which is exactly why
    m = 92 deadlocks."""
    from collatz_maxodd.hercher import _premised_m2

    K = 309_300_189_283_732_030_081
    assert _premised_m2(K, 92, BARINA_PAPER_X0, 320) == 92
    assert _premised_m2(K - 1, 92, BARINA_PAPER_X0, 320) == 91


def test_window_width_not_monotone_in_x0():
    """The audit's counterexample, kept as a regression: the Thm-21 premise
    contains log2((162/97) X_0), which GROWS with X_0, so the certified m_2
    can drop and the width can JUMP as X_0 rises.  This is why binary search
    alone cannot certify required_x0_for_next_m's minimality."""
    K, m = 7_941_964_418_702_608_664_581, 99
    x0 = 7_021_099_234_927_433_994_869
    w_lo = window_width(K, m, x0)
    w_hi = window_width(K, m, x0 + 1)
    assert w_hi.m2 < w_lo.m2
    assert w_hi.value > w_lo.value


# ---------------------------------------------------------------------------
# the m-free bound and the rung economics
# ---------------------------------------------------------------------------


def test_allm_bound_reproduces_hercher_last_row():
    """Theorem 27 + Lemma 22 at any current X_0 gives K >= 72 057 431 991 —
    Hercher's 'for all m' Table-1 row, digit for digit (and the same rung the
    repo's elementary Crandall squeeze lands on)."""
    for x0 in (HERCHER_PUBLICATION_X0, BARINA_PAPER_X0, BARINA_PAGE_X0):
        q, _f, _w = allm_bound(x0)
        assert q == 72_057_431_991


def test_remark_28_threshold_reproduces():
    """The next all-m rung is K >= 137 528 045 312 (Hercher's '1.375e11'),
    and the X_0 it demands at the 3/4 constant is 2836·2^60 after rounding up
    — exactly Remark 28.  Barina's 2^71 = 2048·2^60 is short of it, which is
    why Corollary 29's frozen C++ certificate (condition X_0 >= 1536·2^60,
    met) remains the only unconditional route to K > 1.375e11 today."""
    rung = next(r for r in rung_table(10**12) if r["K"] > 137_400_000_000)
    assert rung["K"] == 137_528_045_312
    units = rung["x0_needed_2p60"]
    assert 2835 < units < 2836
    assert BARINA_PAPER_X0 < Fraction(2836) * 2**60 / 1  # short of the rung
    assert 1536 * 2**60 <= BARINA_PAPER_X0  # Cor 29's condition is met


def test_window_width_is_monotone_in_k():
    """Widths shrink (weakly) in K — the direction the ladder relies on.
    (In X_0 they are only PIECEWISE monotone: see
    test_window_width_not_monotone_in_x0.)"""
    w1 = window_width(10**15, 92, BARINA_PAPER_X0).value
    w2 = window_width(10**16, 92, BARINA_PAPER_X0).value
    assert w2 <= w1


def test_enclosure_never_strengthens():
    """min_denominator_beyond uses an ENCLOSING interval: widening the window
    can only lower (weaken) the reported K, never raise it."""
    q1, _ = min_denominator_beyond(Fraction(1, 10**32))
    q2, _ = min_denominator_beyond(Fraction(2, 10**32))
    assert q2 <= q1
