"""T0-T7 checked against EVERY cycle in the census, with the audited hypotheses.

The hypotheses attached here are the audited ones, which differ from
``docs/GROUND_TRUTH.md`` in three places (see ``test_edge_cases.py`` for the
witnesses):

* T1 needs **no** hypothesis at all -- not ``M > q``.
* T2/T3/T4 need ``M > q``; the doc's extra ``L >= 2`` is redundant, because
  ``M = q`` forces ``L = 1`` and ``L = 1`` forces ``M <= q``.
* T5 needs the **size** condition ``M > 11q/7``; the doc's ``L >= 3`` is neither
  necessary nor sufficient.
"""

from __future__ import annotations

from fractions import Fraction

from collatz_maxodd.backtree import c_constant, floor_bound
from collatz_maxodd.cycleeq import (
    check_cycle_equation,
    cycle_constant,
    forward_constant,
    product_identity,
    ratio_window,
)
from collatz_maxodd.cycles import Cycle
from collatz_maxodd.sieve import t1_ok, t2_residue_ok, t3_ok, t4_ok, t8_ok
from collatz_maxodd.syracuse import smaller_predecessor, syracuse_with_exponent


def test_census_is_substantial(census: list[Cycle], multi, big_M):
    assert len(census) > 1500
    assert len(multi) > 1000
    assert len(big_M) > 1000
    assert sum(1 for c in census if c.M < c.q) > 200  # the interesting corner
    assert sum(1 for c in census if c.L == 1) > 200


def test_cycles_are_genuine(census: list[Cycle]):
    """Sanity: every reported cycle really closes under S_q, and M really is the max."""
    for c in census:
        for j, z in enumerate(c.elements):
            nxt, a = syracuse_with_exponent(z, c.q)
            assert nxt == c.elements[(j + 1) % c.L]
            assert a == c.forward_halvings[j]
        assert c.M == max(c.elements)
        assert c.B == sum(c.forward_halvings)
        assert len(set(c.elements)) == c.L


# --------------------------------------------------------------------- T0


def test_T0_every_cycle_element_is_coprime_to_3(census: list[Cycle]):
    """T0.  Hypotheses: q odd, 3 does not divide q.  Nothing else."""
    for c in census:
        assert all(z % 3 for z in c.elements), c


# --------------------------------------------------------------------- T1


def test_T1_holds_with_no_hypothesis(census: list[Cycle]):
    """T1: 4 | 3M + q for EVERY cycle maximum, including M < q and L = 1."""
    for c in census:
        assert (3 * c.M + c.q) % 4 == 0, c
        assert t1_ok(c.M, c.q)
        assert c.M % 4 == c.q % 4
        assert c.forward_halvings[0] >= 2  # a_1 = v2(3M + q) >= 2


def test_T1_q1_specialisation(census: list[Cycle]):
    for c in census:
        if c.q == 1:
            assert c.M % 4 == 1


def test_T1_refinements_by_size(census: list[Cycle]):
    """M < q gives the STRICTLY STRONGER 8 | 3M+q; M = q gives v2 = 2 exactly."""
    small = [c for c in census if c.M < c.q]
    equal = [c for c in census if c.M == c.q]
    assert small and equal
    for c in small:
        assert (3 * c.M + c.q) % 8 == 0, c
    for c in equal:
        assert c.forward_halvings[0] == 2, c


# ----------------------------------------------------------------- FP / T2


def test_FP_fixed_points_have_M_at_most_q(census: list[Cycle]):
    """L = 1  =>  n(2^b - 3) = q  =>  M <= q.  Hence M > q  =>  L >= 2."""
    for c in census:
        if c.L == 1:
            b = c.forward_halvings[0]
            assert c.M * ((1 << b) - 3) == c.q
            assert c.M <= c.q
        if c.M > c.q:
            assert c.L >= 2


def test_M_equals_q_forces_fixed_point(census: list[Cycle]):
    """3M + q = 4q when M = q, and v2(4q) = 2, so S_q(M) = M.  So M = q => L = 1."""
    for c in census:
        if c.M == c.q:
            assert c.L == 1


def test_T2_b1_is_one_when_M_exceeds_q(big_M: list[Cycle]):
    """T2.  Hypothesis: M > q (which already implies L >= 2)."""
    for c in big_M:
        assert c.b1 == 1, c
        assert c.y(1) == (2 * c.M - c.q) // 3
        assert (2 * c.M - c.q) % 3 == 0
        assert t2_residue_ok(c.M, c.q)
        assert c.M % 3 == (2 * c.q) % 3


def test_T2_uniqueness_needs_no_size_hypothesis(multi: list[Cycle]):
    """The predecessor of M below M is unique for EVERY cycle with L >= 2 (LEMMA-U).

    Only the identification 'it is the b = 1 one' needs M >= q.
    """
    for c in multi:
        got = smaller_predecessor(c.M, c.q)
        assert got is not None, c
        assert got[1] == c.y(1) and got[0] == c.b1, c


def test_T2_hypothesis_must_be_STRICT(census: list[Cycle]):
    """`M >= q` is NOT a valid hypothesis for T2 -- only the strict `M > q` is.

    At `M = q` the cycle is the fixed point `S_q(q) = q` with `b_1 = 2`, and
    `2M - q = q` is never divisible by 3.  So both halves of T2 fail there.
    """
    at = [c for c in census if c.M == c.q]
    assert at, "expected M = q fixed points in the census"
    for c in at:
        assert c.L == 1 and c.b1 == 2
        assert not t2_residue_ok(c.M, c.q)  # 3 | 2M - q = q is false
        assert c.M % 3 != (2 * c.q) % 3
    # ...while every M > q cycle satisfies it
    for c in census:
        if c.M > c.q:
            assert c.b1 == 1 and t2_residue_ok(c.M, c.q)


def test_T2_converse_is_false(census: list[Cycle]):
    """b_1 = 1 does NOT imply M > q: there are cycles with M < q and b_1 = 1."""
    witnesses = [c for c in census if c.M < c.q and c.b1 == 1]
    assert witnesses, "expected cycles with M < q yet b_1 = 1"
    assert any(c.q == 11 and c.elements == (7, 1) for c in witnesses)


# --------------------------------------------------------------------- T3


def test_T3(big_M: list[Cycle]):
    """T3: M = 5q (mod 12).  Hypothesis: M > q."""
    for c in big_M:
        assert c.M % 12 == (5 * c.q) % 12, c
        assert t3_ok(c.M, c.q)
        if c.q == 1:
            assert c.M % 12 == 5


# --------------------------------------------------------------------- T4


def test_T4(big_M: list[Cycle]):
    """T4: M != 5q (mod 9), i.e. M = 17q or 29q (mod 36).  Hypothesis: M > q."""
    for c in big_M:
        assert c.M % 9 != (5 * c.q) % 9, c
        assert t4_ok(c.M, c.q)
        assert c.M % 36 in {(17 * c.q) % 36, (29 * c.q) % 36}, c
        # the mechanism: y_1 is on the cycle, so 3 does not divide it
        assert c.y(1) % 3 != 0


def test_T4_hypothesis_is_tight(census: list[Cycle]):
    """Cycles that DO satisfy M = 5q (mod 9) exist -- all with M < q or L = 1."""
    bad = [c for c in census if c.M % 9 == (5 * c.q) % 9]
    assert bad, "expected witnesses violating T4's conclusion"
    for c in bad:
        assert c.M < c.q or c.L == 1, c
    assert any(c.q == 119 and c.M == 19 and c.L == 2 for c in bad)


def test_T4_both_surviving_classes_occur(big_M: list[Cycle]):
    """Non-vacuity: both 17q and 29q (mod 36) really happen."""
    at17 = sum(1 for c in big_M if c.M % 36 == (17 * c.q) % 36)
    at29 = sum(1 for c in big_M if c.M % 36 == (29 * c.q) % 36)
    assert at17 > 100 and at29 > 100, (at17, at29)
    assert at17 + at29 == len(big_M)
    # q = 1 contributes nothing: it has no cycle with M > 1.  That IS the conjecture.
    assert [c for c in big_M if c.q == 1] == []


# --------------------------------------------------------------------- T5


def test_T5_exact_inequality(big_M: list[Cycle]):
    """The exact T5 inequality M(2^{1+b_2} - 9) <= (2^{b_2}+3) q, for every M > q."""
    for c in big_M:
        if c.L < 2:
            continue
        b2 = c.b(2)
        assert c.M * ((1 << (1 + b2)) - 9) <= ((1 << b2) + 3) * c.q, c


def test_T5_sharp_size_hypothesis(census: list[Cycle]):
    """CORRECTED T5: M > 11q/7  =>  b_2 <= 2.  No length hypothesis at all."""
    tested = 0
    for c in census:
        if 7 * c.M > 11 * c.q:
            assert c.b(2) <= 2, c
            tested += 1
    assert tested > 900


def test_T5_threshold_is_sharp(census: list[Cycle]):
    """7M = 11q exactly admits b_2 = 3 -- the threshold cannot be relaxed."""
    at = [c for c in census if 7 * c.M == 11 * c.q]
    assert at, "expected cycles sitting exactly on the 11q/7 threshold"
    for c in at:
        assert c.b(2) == 3, c
    assert any(c.q == 7 and c.M == 11 for c in at)


def test_T5_q1_statement_is_vacuous_but_true(census: list[Cycle]):
    """q = 1, M >= 3: b_2 <= 2.  Vacuous -- {1} is the only known q=1 cycle."""
    q1 = [c for c in census if c.q == 1]
    assert [c.elements for c in q1] == [(1,)]
    for c in q1:
        if c.M >= 3:  # pragma: no cover - vacuous unless the conjecture fails
            assert c.b(2) <= 2


# --------------------------------------------------------------------- T6


def test_T6_exact_equivalence(census: list[Cycle]):
    """T6: y_k <= M  <=>  M(2^{B_k} - 3^k) <= c_k, for every cycle and every depth."""
    for c in census:
        bs: list[int] = []
        for k in range(1, min(3 * c.L, 24) + 1):
            bs.append(c.b(k))
            B = sum(bs)
            ck = c_constant(bs, c.q)
            yk = c.y(k)
            # closed form
            assert (1 << B) * c.M - ck == 3**k * yk, (c, k)
            assert (yk <= c.M) == (c.M * ((1 << B) - 3**k) <= ck), (c, k)
            assert yk <= c.M  # every backward element is a cycle element


def test_T6_floor_rule_is_NOT_unconditional(census: list[Cycle]):
    """The refuted row: B_k <= floor(k log2 3) fails on real small cycles."""
    from collatz_maxodd.cycles import find_cycles

    (c,) = [x for x in find_cycles(5, 60) if x.elements == (49, 19, 31)]
    assert c.L == 3 and c.q == 5
    b3 = [c.b(1), c.b(2), c.b(3)]
    assert sum(b3) == 5 > floor_bound(3) == 4, b3
    # and it is not an isolated accident
    violators = [
        c
        for c in census
        for k in [3]
        if c.L >= k and sum(c.b(j) for j in range(1, k + 1)) > floor_bound(k)
    ]
    assert len(violators) > 5


# --------------------------------------------------------------------- T7


def test_T7_cycle_equation(census: list[Cycle]):
    """M(2^B - 3^L) = c_L = d_L > 0, hence 2^B > 3^L and B/L > log2 3."""
    for c in census:
        assert check_cycle_equation(c), c
        assert cycle_constant(c) == forward_constant(c) > 0
        assert (1 << c.B) > 3**c.L
        assert Fraction(c.B, c.L) > Fraction(1054, 665)  # a convergent below log2 3
        assert product_identity(c), c


def test_T7_ratio_window(census: list[Cycle]):
    """(3 + q/M)^L <= 2^B <= (3 + q/m)^L, exactly, over the rationals."""
    for c in census:
        lo, hi = ratio_window(c)
        assert lo**c.L <= Fraction(1 << c.B) <= hi**c.L, c


# --------------------------------------------------------------------- T8


def test_T8_mod16(census: list[Cycle]):
    """T8 (q=1): M != 9 (mod 16), so M = 1, 5, 13 (mod 16).  No hypothesis."""
    for c in census:
        if c.q == 1:
            assert t8_ok(c.M, 1)
            assert c.M % 16 in (1, 5, 13)


def test_T8_proof_is_constructive():
    """M = 16s+9 (q=1) forces x_1 = 12s+7 and x_2 = 18s+11 > M, for every s >= 0."""
    for s in range(0, 400):
        m = 16 * s + 9
        x1, a1 = syracuse_with_exponent(m, 1)
        assert a1 == 2 and x1 == 12 * s + 7
        x2, a2 = syracuse_with_exponent(x1, 1)
        assert a2 == 1 and x2 == 18 * s + 11
        assert x2 > m
