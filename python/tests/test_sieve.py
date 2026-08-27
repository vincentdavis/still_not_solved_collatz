"""Hard-coded fixtures for the sieves and the backward-prefix counts.

Every number here comes from the independent audit of the claims and is
reproduced by this package from scratch.
"""

from __future__ import annotations

import pytest

from collatz_maxodd.backtree import (
    admissible_halving_vectors,
    count_admissible_halving_vectors,
    floor_bound,
    floor_rule_threshold,
    size_admissible,
    y_value,
)
from collatz_maxodd.sieve import (
    can_be_max_odd,
    combined_residues,
    combined_surviving_density,
    surviving_residues_mod2,
    surviving_residues_mod3,
    surviving_residues_mod3_no_size,
)
from collatz_maxodd.syracuse import syracuse_with_exponent, v2

# --------------------------------------------------------------------------
# fixtures from the audit
# --------------------------------------------------------------------------

#: N(k) = # backward halving vectors with B_j <= floor(j*log2 3) for all j <= k.
#: The ground-truth doc lists 1, 2, 3, 7, 12; the audit extends it.
PREFIX_COUNTS = [
    1, 2, 3, 7, 12, 30, 85, 173, 476, 961,
    2652, 8045, 17637, 51033, 108950, 312455, 663535, 1900470,
]

#: Surviving M mod 3^(k+1), q = 1, large-M regime.
SURV3 = {
    1: (9, [2, 8]),
    2: (27, [2, 17, 20, 26]),
    3: (81, [20, 26, 44, 71, 74, 80]),
    4: (243, [20, 80, 107, 125, 152, 155, 161, 182, 188, 206, 233, 236, 242]),
    5: (729, [161, 182, 188, 206, 233, 242, 263, 350, 395, 404, 449, 479, 485,
              506, 593, 638, 647, 668, 674, 719, 722, 728]),
    6: (2187, [161, 182, 206, 233, 242, 263, 350, 395, 404, 449, 479, 485, 506,
               593, 638, 668, 674, 719, 722, 728, 890, 911, 917, 962, 971, 992,
               1079, 1133, 1235, 1322, 1367, 1376, 1403, 1457, 1619, 1640, 1646,
               1664, 1700, 1853, 1907, 1937, 1943, 2051, 2096, 2105, 2126, 2177,
               2180, 2186]),
}

#: |SURV3| for k = 1..12 (the audit's table).
SURV3_SIZES = [2, 4, 6, 13, 22, 50, 123, 254, 620, 1302, 3202, 8425]

#: Surviving odd M mod 2^a, q = 1, large-M regime.
SURV2 = {
    2: (4, [1]),
    3: (8, [1, 5]),
    4: (16, [1, 5, 13]),
    5: (32, [1, 5, 13, 17, 21, 29]),
    6: (64, [1, 5, 13, 17, 21, 29, 33, 37, 45, 49, 53, 61]),
    7: (128, [1, 5, 13, 17, 21, 29, 33, 37, 45, 49, 53, 61, 65, 69, 77, 81, 85,
              93, 101, 109, 113, 117]),
    8: (256, [1, 5, 13, 17, 21, 29, 33, 37, 45, 49, 53, 61, 65, 69, 77, 81, 85,
              93, 101, 109, 113, 117, 129, 133, 141, 145, 149, 157, 161, 165,
              173, 177, 181, 189, 193, 197, 205, 209, 213, 221, 229, 237, 241,
              245]),
}

#: |SURV2| for a = 2..12.
SURV2_SIZES = [1, 2, 3, 6, 12, 22, 44, 88, 169, 338, 646]

#: floor_rule_threshold(k) for q = 1, k = 1..10.
FLOOR_THRESHOLDS = {1: 1, 2: 1, 3: 9, 4: 7, 5: 86, 6: 23, 7: 22, 8: 82, 9: 62, 10: 381}


# --------------------------------------------------------------------------
# backward prefix counts
# --------------------------------------------------------------------------


def test_prefix_counts_match_fixture():
    got = [count_admissible_halving_vectors(k) for k in range(1, len(PREFIX_COUNTS) + 1)]
    assert got == PREFIX_COUNTS


def test_prefix_counts_agree_with_enumeration():
    """The DP count and the explicit enumeration agree."""
    for k in range(1, 11):
        vectors = list(admissible_halving_vectors(k))
        assert len(vectors) == count_admissible_halving_vectors(k) == PREFIX_COUNTS[k - 1]
        for bs in vectors:
            assert len(bs) == k and all(b >= 1 for b in bs)
            for j in range(1, k + 1):
                assert sum(bs[:j]) <= floor_bound(j)
        assert vectors[0][0] == 1  # b_1 = 1 falls out of the floor rule: that is T2


def test_floor_bound_is_exact():
    import math

    for k in range(1, 200):
        assert floor_bound(k) == math.floor(k * math.log2(3))


# --------------------------------------------------------------------------
# floor rule vs the exact inequality
# --------------------------------------------------------------------------


def test_floor_rule_thresholds_match_fixture():
    for k, v in FLOOR_THRESHOLDS.items():
        assert floor_rule_threshold(k, 1) == v, k


def test_floor_rule_threshold_is_a_genuine_threshold():
    """Above the threshold the exact test and the floor rule agree; at it, they don't."""
    for k in range(1, 8):
        thr = floor_rule_threshold(k, 1)
        # at M = thr some vector with B_k > floor(k log2 3) is still admissible
        exact_at = list(admissible_halving_vectors(k, 1, m=thr))
        assert any(sum(bs) > floor_bound(k) for bs in exact_at), k
        # just above it, none is
        exact_above = list(admissible_halving_vectors(k, 1, m=thr + 1))
        assert all(sum(bs) <= floor_bound(k) for bs in exact_above), k


def test_exact_and_symbolic_enumeration_agree_for_large_M():
    """For M above the running threshold, the exact T6 test == the floor rule."""
    from collatz_maxodd.backtree import floor_rule_safe_M

    safe = floor_rule_safe_M(7, 1)
    assert safe == 86
    for m in (safe + 1, 1001, 10**6 + 1):
        for k in range(1, 8):
            exact = {bs for bs in admissible_halving_vectors(k, 1, m=m)}
            symbolic = set(admissible_halving_vectors(k, 1))
            assert exact == symbolic, (m, k)


def test_size_admissible_matches_y_value():
    """size_admissible is exactly '0 < y_j <= M at every level', as rationals."""
    for m in (5, 27, 101, 12345):
        for bs in admissible_halving_vectors(4, 1, m=m):
            for j in range(1, 5):
                y = y_value(m, bs[:j], 1)
                assert 0 < y <= m
            assert size_admissible(m, bs, 1)


# --------------------------------------------------------------------------
# 3-adic sieve
# --------------------------------------------------------------------------


@pytest.mark.parametrize("k", sorted(SURV3))
def test_mod3_survivors_match_fixture(k: int):
    mod, surv = surviving_residues_mod3(k, 1)
    assert (mod, list(surv)) == SURV3[k]


def test_mod3_sizes():
    for k, expected in enumerate(SURV3_SIZES, start=1):
        mod, surv = surviving_residues_mod3(k, 1)
        assert mod == 3 ** (k + 1)
        assert len(surv) == expected, k


def test_mod3_is_nested():
    """Projection of depth k+1 survivors lands inside the depth k survivors."""
    for k in range(1, 8):
        m_lo, s_lo = surviving_residues_mod3(k, 1)
        _, s_hi = surviving_residues_mod3(k + 1, 1)
        assert {r % m_lo for r in s_hi} <= set(s_lo), k


def test_T4_is_the_depth_1_sieve():
    """depth 1 mod 9 = {2, 8}; CRT with M = 1 (mod 4) gives M = 17, 29 (mod 36)."""
    assert surviving_residues_mod3(1, 1) == (9, (2, 8))
    assert combined_residues(1, 2, 1) == (36, (17, 29))


def test_the_T4_recursion_claim_is_wrong():
    """T0 alone saturates at 2/9 density -- it does NOT recurse to higher 3-powers."""
    for k in range(1, 6):
        mod, surv = surviving_residues_mod3_no_size(k, 1)
        assert mod == 3 ** (k + 1)
        assert len(surv) == 2 * 3 ** (k - 1), k
        assert len(surv) / mod == pytest.approx(2 / 9)
        # it really is just "M = 2, 8 (mod 9)" lifted
        assert {r % 9 for r in surv} == {2, 8}
    # ...whereas WITH the size bound the density keeps falling
    dens = [len(surviving_residues_mod3(k, 1)[1]) / 3 ** (k + 1) for k in range(1, 9)]
    assert dens == sorted(dens, reverse=True)
    assert dens[-1] < 0.02


# --------------------------------------------------------------------------
# 2-adic sieve
# --------------------------------------------------------------------------


@pytest.mark.parametrize("a", sorted(SURV2))
def test_mod2_survivors_match_fixture(a: int):
    mod, surv = surviving_residues_mod2(a, 1)
    assert (mod, list(surv)) == SURV2[a]


def test_mod2_sizes_and_densities():
    for a, expected in enumerate(SURV2_SIZES, start=2):
        _, surv = surviving_residues_mod2(a, 1)
        assert len(surv) == expected, a
    dens = {a: len(surviving_residues_mod2(a, 1)[1]) / (1 << (a - 1)) for a in range(2, 13)}
    assert dens[2] == 0.5
    assert dens[4] == 0.375
    assert dens[7] == 0.34375
    assert dens[10] == 0.3300781250
    assert dens[12] == 0.3154296875


def test_mod2_kill_depths():
    """New classes are killed only at a in {ceil(j log2 3)}: 2, 4, 7, 10, 12, ..."""
    killed_at = []
    prev = {1}
    for a in range(2, 16):
        mod, surv = surviving_residues_mod2(a, 1)
        cur = set(surv)
        new = {r for r in range(1, mod, 2) if r not in cur and (r % (mod >> 1)) in prev}
        if new:
            killed_at.append(a)
        prev = cur
    assert killed_at == [2, 4, 7, 10, 12, 15]
    import math

    ceilings = {math.ceil(j * math.log2(3)) for j in range(1, 12)}
    assert set(killed_at) <= ceilings


def test_mod2_kills_are_UNCONDITIONAL_not_large_M():
    """A class killed by the 2-adic sieve contains no cycle maximum at ALL, however small.

    The kill condition is `2^{A_j} < 3^j`; since `x_j 2^{A_j} = 3^j M + d_j` with
    `d_j > 0`, that gives `x_j > 3^j M / 2^{A_j} > M` for *every* positive `M`.
    So unlike the 3-adic side there is no `floor_rule_threshold` here.  Checked
    against real orbits starting at the smallest members of each dead class.
    """
    for a in (2, 4, 6, 8):
        mod, surv = surviving_residues_mod2(a, 1)
        dead = [r for r in range(1, mod, 2) if r not in set(surv)]
        assert dead
        for r in dead:
            for m in range(r, r + 8 * mod, mod):  # the 8 smallest members, incl. tiny ones
                if m < 3 or m % 3 == 0:
                    continue
                x, exceeded = m, False
                for _ in range(a + 4):
                    x = syracuse_with_exponent(x, 1)[0]
                    if x > m:
                        exceeded = True
                        break
                assert exceeded, (a, r, m)


def test_T1_and_T8_are_the_first_two_kills():
    _, s2 = surviving_residues_mod2(2, 1)
    assert set(range(1, 4, 2)) - set(s2) == {3}  # T1: M = 3 (mod 4) dies
    _, s4 = surviving_residues_mod2(4, 1)
    assert set(s4) == {1, 5, 13}  # T8: M = 9 (mod 16) dies
    assert combined_residues(1, 4, 1)[0] == 144
    assert combined_residues(1, 4, 1)[1] == (17, 29, 53, 65, 101, 125)


# --------------------------------------------------------------------------
# combined
# --------------------------------------------------------------------------


def test_combined_landmarks():
    assert combined_residues(1, 2, 1) == (36, (17, 29))
    assert combined_residues(2, 2, 1) == (108, (17, 29, 53, 101))
    assert combined_residues(3, 2, 1) == (324, (101, 125, 161, 233, 269, 317))
    assert combined_residues(4, 2, 1)[0] == 972
    assert len(combined_residues(4, 2, 1)[1]) == 13
    assert combined_residues(2, 4, 1) == (
        432,
        (17, 29, 53, 101, 125, 161, 209, 245, 269, 317, 341, 353),
    )


def test_combined_density_matches_audit():
    assert combined_surviving_density(1, 2, 1) == pytest.approx(0.1111111111, abs=1e-9)
    assert combined_surviving_density(4, 6, 1) == pytest.approx(0.0200617284, abs=1e-9)
    assert combined_surviving_density(8, 12, 1) == pytest.approx(0.0040704741, abs=1e-9)


# --------------------------------------------------------------------------
# the sieves against real integers (no residue arithmetic)
# --------------------------------------------------------------------------


def test_mod3_sieve_predicts_real_backward_survival():
    """Honest check: run the exact integer backward DFS on real M and compare.

    Set equality with the predicted residue classes, for every depth 1..4.
    """
    from collatz_maxodd.backtree import backward_chains

    lo = 1_000_001  # comfortably above floor_rule_safe_M
    hi = lo + 20_000
    for k in range(1, 5):
        mod, surv = surviving_residues_mod3(k, 1)
        observed = set()
        for m in range(lo, hi, 2):
            if next(backward_chains(m, 1, k), None) is not None:
                observed.add(m % mod)
        assert observed == set(surv), k


def test_mod2_sieve_predicts_real_forward_survival():
    """Same for the forward side: exact integer orbit vs the mod-2^a classes."""
    lo = 1_000_001
    hi = lo + 20_000
    for a in (4, 6, 8):
        mod, surv = surviving_residues_mod2(a, 1)
        observed = set()
        for m in range(lo, hi, 2):
            x, total, ok = m, 0, True
            while True:
                x, step = syracuse_with_exponent(x, 1)
                total += step
                if total >= a:
                    break
                if x > m:
                    ok = False
                    break
            if ok:
                observed.add(m % mod)
        assert observed == set(surv), a


def test_can_be_max_odd_is_exact_and_unconditional():
    """The per-M test never contradicts a real cycle, and gives reasons otherwise."""
    from collatz_maxodd.cycles import find_cycles

    # No real cycle maximum is ever excluded.
    for q in (5, 7, 17, 23, 37, 119):
        for c in find_cycles(q, 3000):
            v = can_be_max_odd(c.M, q, back_depth=min(6, c.L), forward_depth=min(6, c.L))
            assert v, (c, v.reason)

    # Small q=1 exclusions, with the reason naming the right mechanism.
    assert "T0" in can_be_max_odd(9, 1).reason
    assert "T1" in can_be_max_odd(7, 1).reason
    assert "backward" in can_be_max_odd(13, 1).reason
    assert v2(3 * 13 + 1) == 3  # 13 passes T1 (13 = 1 mod 4) but dies in the backward tree


#: The 29 odd M <= 20000 that survive depth-8 backward + 40-step forward screening
#: for q = 1.  They are NOT cycle maxima -- the sieve simply cannot see that.
SURVIVORS_20K = [
    917, 1457, 2693, 3077, 3149, 4373, 4769, 4853, 5777, 6965,
    7229, 8261, 8657, 8909, 10853, 10925, 11117, 13061, 13121, 13517,
    13841, 14741, 15173, 16301, 16949, 17729, 18629, 19889, 19925,
]


def test_the_sieve_does_NOT_settle_small_cases():
    """The honest negative result: the sieve leaves survivors, and they are false.

    29 odd M <= 20000 pass depth-8 backward screening AND keep their forward orbit
    below M for 40 steps.  Every one of them nonetheless reaches 1, so none is a
    cycle maximum.  The sieve is a necessary condition only -- it never proves
    that an M IS a cycle maximum, and it does not even resolve M <= 20000.
    """
    survivors = [
        m
        for m in range(3, 20_001, 2)
        if can_be_max_odd(m, 1, back_depth=8, forward_depth=40)
    ]
    assert survivors == SURVIVORS_20K

    # every survivor is a false positive: its orbit reaches 1
    for m in survivors:
        x, steps = m, 0
        while x != 1 and steps < 2000:
            x = syracuse_with_exponent(x, 1)[0]
            steps += 1
        assert x == 1, m

    # deeper screening removes some but not all of them
    deeper = [m for m in survivors if can_be_max_odd(m, 1, back_depth=12, forward_depth=60)]
    assert 0 < len(deeper) <= len(survivors)


def test_survivors_lie_in_the_predicted_residue_classes():
    """Consistency: every survivor satisfies T3, T4 and the depth-3 mod-324 sieve."""
    mod, classes = combined_residues(3, 4, 1)
    for m in SURVIVORS_20K:
        assert m % 12 == 5  # T3
        assert m % 36 in (17, 29)  # T4
        assert m % 16 in (1, 5, 13)  # T8
        assert m % mod in classes


def test_can_be_max_odd_depth_shorthand():
    """`depth` sets both directions; the Verdict is usable as a plain bool."""
    v = can_be_max_odd(7, 1, depth=3)
    assert bool(v) is False and isinstance(v.reason, str)
    assert can_be_max_odd(917, 1, depth=6)
    assert not can_be_max_odd(917, 1, depth=20)
