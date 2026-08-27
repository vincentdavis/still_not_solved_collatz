"""Three complete tests for 'M is not a cycle maximum', and their relative cost.

The mathematical content is in lean/Collatz/Equivalence.lean; these tests pin
that the three agree, that none of them wrongly eliminates a REAL cycle
maximum, and that the backward test is the cheapest.
"""

from __future__ import annotations

import pytest

from collatz_maxodd.certify import (
    backward_depth,
    certify_range,
    forward_exceeds,
    forward_to_one,
    residue_table,
)

CAP = 300


def test_three_tests_agree_on_q1():
    """For q=1 every odd number below the verified range is refutable, by all three."""
    for M in range(3, 8000, 2):
        assert forward_to_one(M)[0]
        assert forward_exceeds(M)[0]
        assert backward_depth(M, cap=CAP)[0] < CAP


@pytest.mark.parametrize("q,M", [(5, 49), (5, 37), (7, 11), (11, 79), (37, 53)])
def test_real_cycle_maxima_are_not_eliminated(q, M):
    """The tests must FAIL to refute a genuine cycle maximum -- otherwise they
    would be refuting a true statement.  This is the non-vacuity guard."""
    d, _ = backward_depth(M, q=q, cap=CAP)
    assert d >= CAP, f"backward test wrongly eliminated the real cycle max {M} for q={q}"


def test_backward_is_the_cheapest_complete_test():
    rng = range(10 ** 6 + 1, 10 ** 6 + 40001, 2)
    w_one = sum(forward_to_one(M)[1] for M in rng)
    w_exc = sum(forward_exceeds(M)[1] for M in rng)
    w_bwd = sum(backward_depth(M, cap=CAP)[1] for M in rng)
    assert w_bwd < w_exc < w_one
    assert w_one / w_bwd > 10, f"expected a large margin, got {w_one/w_bwd:.1f}x"


def test_forward_exceeds_matches_the_2adic_saturation_density():
    """About 1 - 0.2863 = 71.4% of odds are refuted by 'the orbit exceeds M'."""
    rng = list(range(10 ** 6 + 1, 10 ** 6 + 40001, 2))
    quick = sum(1 for M in rng if forward_exceeds(M)[1] < forward_to_one(M)[1])
    frac = quick / len(rng)
    assert 0.69 < frac < 0.74, frac


def test_certify_range_and_its_sieve():
    r = certify_range(10 ** 6, 10 ** 6 + 100_000, depth=4, a=10)
    assert r["ok"] is True
    assert r["tested"] == 50_000
    assert r["sieve_kept"] < 0.03          # the table keeps under 3%
    assert r["max_depth"] < CAP


def test_residue_table_is_a_proper_subset():
    m3, s3, m2, s2 = residue_table(depth=4, a=10)
    assert 0 < len(s3) < m3 and 0 < len(s2) < m2
    # every survivor of the table must be odd and coprime to 3
    for M in range(3, 20000, 2):
        if (M % m3) in s3 and (M % m2) in s2:
            assert M % 3 != 0 and M % 2 == 1
