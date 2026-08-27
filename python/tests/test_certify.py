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


# ---------------------------------------------------------------------------
# Certifying whole residue classes
# ---------------------------------------------------------------------------

# The project's independently computed running_max (docs/GROUND_TRUTH.md 4a).
KNOWN_THRESHOLDS = {1: 1, 2: 1, 3: 9, 4: 9, 5: 86, 6: 86, 7: 86, 8: 86,
                    9: 86, 10: 381, 11: 381, 12: 381, 13: 538}

# a_k, from docs/DEATH_DEPTH.md -- reproduced here by a third route.
A_K = [1, 2, 3, 6, 10, 22, 50, 104, 254]


def test_closed_form_threshold_matches_the_projects_computation():
    from collatz_maxodd.certify import class_threshold
    for k, v in KNOWN_THRESHOLDS.items():
        assert class_threshold(k) == v, (k, class_threshold(k), v)


def test_alive_classes_reproduce_a_k():
    """A third independent route to the same sequence."""
    from collatz_maxodd.certify import class_coverage
    for k in range(1, 8):
        assert class_coverage(k)["alive"] == A_K[k - 1], k


def test_dead_classes_really_certify_real_numbers():
    """Every odd M above T_k in a DEAD class must have exact d(M) < k."""
    from collatz_maxodd.certify import class_is_certified, class_threshold
    from collatz_maxodd.deathdepth import death_depth
    for k in (3, 5, 6):
        mod, T = 3 ** k, class_threshold(k)
        dead = [r for r in range(mod) if class_is_certified(r, k)]
        assert dead, k
        for r in dead[:40]:
            for t in range(3):
                M = 10 ** 9 + t * 2 * mod
                M = M - (M % mod) + r
                if M % 2 == 0:
                    M += mod
                assert M > T
                assert death_depth(M) < k, (k, r, M, death_depth(M))


def test_alive_classes_are_non_empty_so_the_certificate_never_finishes():
    """a_k > 0 for every k -- the sieve can never certify everything, which is
    exactly what the equivalence theorem says must happen."""
    from collatz_maxodd.certify import class_coverage
    for k in range(1, 8):
        assert class_coverage(k)["alive"] > 0


def test_coverage_increases_but_stays_below_one():
    from collatz_maxodd.certify import class_coverage
    fr = [class_coverage(k)["certified_fraction"] for k in range(1, 8)]
    assert all(a < b for a, b in zip(fr, fr[1:]))
    assert fr[-1] < 1.0
