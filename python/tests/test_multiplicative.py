"""The multiplicative ledger (web/multiplicative.html, docs/LEDGER.md §6): the numbers the page shows."""

from __future__ import annotations

from decimal import Decimal, getcontext

from collatz_maxodd.cycleeq import best_upper_approximations, log2_3, smallest_admissible_length


def test_log_form_of_the_product_identity(census):
    """B = L*log2(3) + sum log2(1 + q/(3 n_i)) around every cycle, to 40 digits."""
    getcontext().prec = 60
    alpha = log2_3(60)
    ln2 = Decimal(2).ln()
    for c in census:
        corr = sum((1 + Decimal(c.q) / Decimal(3 * n)).ln() / ln2 for n in c.elements)
        assert abs(Decimal(c.B) - Decimal(c.L) * alpha - corr) < Decimal(10) ** -40, c


def test_best_upper_approximations_are_the_records_by_brute_force():
    getcontext().prec = 80
    alpha = log2_3(80)
    records, best = [], None
    for q in range(1, 3001):
        p = int((alpha * q).to_integral_value(rounding="ROUND_FLOOR")) + 1
        gap = Decimal(p) / Decimal(q) - alpha
        if best is None or gap < best:
            best, _ = gap, records.append((p, q))
    assert records == [pq for pq in best_upper_approximations(70, 300) if pq[1] <= 3000]


def test_length_bounds_quoted_on_the_page():
    """Members above 2^k force these (L, B); k = 40 reproduces Eliahou's 17 087 915 as B."""
    want = {
        40: (10781274, 17087915),
        60: (397573379, 630138897),
        68: (72057431991, 114208327604),
        71: (72057431991, 114208327604),
        100: (3332857981044265, 5282454920184382),
    }
    for k, (L, B) in want.items():
        got_L, got_B, margin = smallest_admissible_length(2**k, 1, terms=70, prec=320)
        assert (got_L, got_B) == (L, B) and margin > 0, k
    # Barina's project-page figure gives the same convergent as the printed 2^71
    assert smallest_admissible_length(2075 * 2**60, 1, terms=70, prec=320)[:2] == (72057431991, 114208327604)


def test_hercher_floor_is_the_next_rung_of_the_staircase():
    """Cor. 29's L >= 137 528 045 312 is the best upper approximation right after the squeeze's 72 057 431 991."""
    b = best_upper_approximations(70, 300)
    i = [q for _, q in b].index(72057431991)
    assert b[i] == (114208327604, 72057431991)
    assert b[i + 1] == (217976794617, 137528045312)


def test_circuit_chart_constants_match_hercher_module():
    """The (m, K) chart's inputs are hercher.py's imported Simons-de Weger and Hercher constants."""
    from collatz_maxodd import hercher as h

    assert h.SDW_LOWER_K_91_PLUS == 753_110_000_000 and h.SDW_CEILING_RANGE == (91, 515619)
    assert float(h.SDW_CEILING_COEFF) == 1.4784
    assert dict(h.COR24_STARTS)[98] == 7.76e19 and dict(h.COR24_STARTS)[117] == 2.74e19
    assert dict(h.COR24_STARTS)[276] == 4.68e18 and dict(h.COR24_STARTS)[3079] == 3.97e17
    assert 3.43e20 < float(h.sdw_ceiling(92)) < 3.44e20 and 2.14e20 < float(h.sdw_ceiling(91)) < 2.15e20
    assert h.allm_bound(2**71)[0] == 72057431991
