"""The map itself and the predecessor lemma (LEMMA-U), checked exhaustively."""

from __future__ import annotations

import pytest

from collatz_maxodd.syracuse import (
    count_predecessors_below,
    forward_exponents,
    odd_predecessors,
    predecessor_at,
    predecessor_parity,
    smaller_predecessor,
    syracuse,
    syracuse_with_exponent,
    v2,
)

QS = [q for q in range(1, 200, 2) if q % 3]


def test_v2():
    assert [v2(n) for n in (1, 2, 4, 6, 8, 12, 96)] == [0, 1, 2, 1, 3, 2, 5]
    with pytest.raises(ValueError):
        v2(0)


def test_step_basic():
    assert syracuse_with_exponent(1, 1) == (1, 2)
    assert syracuse_with_exponent(7, 1) == (11, 1)
    assert syracuse_with_exponent(11, 1) == (17, 1)
    assert syracuse_with_exponent(5, 1) == (1, 4)
    # the user's seed observation: 3*7+1 = 22 -> next odd is 11 > 7
    assert syracuse(7, 1) == 11 > 7
    # ...and 7 -> 11 shows the user's stated *reason* for excluding 11 is wrong:
    # you do NOT need a bigger odd to reach 11.  11 is excluded by T1 instead.
    assert 7 < 11 and syracuse(7, 1) == 11


def test_step_rejects_even_and_bad_q():
    with pytest.raises(ValueError):
        syracuse(4, 1)
    for bad in (2, 3, 9, 6):
        with pytest.raises(ValueError):
            predecessor_parity(5, bad)


#: q values that must be rejected everywhere: even, divisible by 3, or non-positive.
BAD_QS = [0, 2, 3, 4, 6, 9, 12, -1, -2, -3, -5, -6, -7, -9]


@pytest.mark.parametrize("q", BAD_QS)
def test_every_public_entry_point_rejects_illegal_q(q: int):
    """Even q, 3 | q and q <= 0 are all rejected -- not silently mis-answered.

    q <= 0 matters as much as the other two: for q < 0 the map does not keep
    positive odds positive (S_{-7}(1) = -1), and T1/T5/T6/T7 and both sieves all
    rest on q > 0 (via 2^b >= 3 + q/M > 3, c_k > 0, d_j > 0).  Before this was
    checked, `surviving_residues_mod2(4, -1)` happily returned `(3, 11, 15)`.
    """
    import collatz_maxodd as C

    entries = [
        (C.check_q, (q,)),
        (C.find_cycles, (q, 50)),
        (C.can_be_max_odd, (101, q)),
        (C.surviving_residues_mod3, (2, q)),
        (C.surviving_residues_mod3_no_size, (2, q)),
        (C.surviving_residues_mod2, (4, q)),
        (C.combined_residues, (2, 4, q)),
        (C.floor_rule_threshold, (3, q)),
        (C.floor_rule_safe_M, (3, q)),
        (C.smaller_predecessor, (101, q)),
        (C.count_predecessors_below, (101, 500, q)),
        (C.odd_predecessors, (101, q)),
        (C.predecessor_parity, (101, q)),
    ]
    for fn, args in entries:
        with pytest.raises(ValueError):
            fn(*args)
    # generators only validate when first advanced
    for fn, args in [
        (C.admissible_halving_vectors, (3, q)),
        (C.backward_chains, (101, q, 2)),
    ]:
        with pytest.raises(ValueError):
            next(fn(*args))


def test_find_cycles_multi_skips_illegal_q_silently():
    """find_cycles_multi is the one documented place that filters instead of raising."""
    from collatz_maxodd.cycles import find_cycles, find_cycles_multi

    assert find_cycles_multi([-5, 0, 2, 3, 6, 5], 200) == find_cycles(5, 200)


def test_forward_exponents_match_orbit():
    assert forward_exponents(27, 1, 5) == [1, 2, 1, 1, 1]
    assert forward_exponents(1, 1, 3) == [2, 2, 2]


@pytest.mark.parametrize("q", QS[:12])
def test_predecessors_are_odd_and_map_back(q: int):
    """Every y_b produced is odd, positive, and really maps to p (LEMMA-U(b))."""
    for p in range(1, 400, 2):
        for b, y in odd_predecessors(p, q, max_b=14):
            assert y > 0 and y % 2 == 1
            assert syracuse_with_exponent(y, q) == (p, b)


@pytest.mark.parametrize("q", QS[:12])
def test_parity_of_b_is_forced(q: int):
    """T0 and the forced parity class of b."""
    for p in range(1, 400, 2):
        beta = predecessor_parity(p, q)
        if p % 3 == 0:
            assert beta is None
            # T0: an odd multiple of 3 has NO odd predecessor at all
            assert odd_predecessors(p, q, max_b=20) == []
            continue
        bs = [b for b, _ in odd_predecessors(p, q, max_b=20)]
        assert all(b % 2 == beta for b in bs)
        # y_b strictly increasing in b
        ys = [y for _, y in odd_predecessors(p, q, max_b=20)]
        assert ys == sorted(ys) and len(set(ys)) == len(ys)


def test_lemma_u_at_most_one_smaller_predecessor():
    """LEMMA-U(d), exhaustively: at most one odd predecessor strictly below p.

    No hypothesis relating p and q is needed -- in particular it holds for p < q.
    """
    checked = 0
    for q in QS:
        for p in range(1, 1000, 2):
            brute = [
                y
                for b in range(1, 40)
                if (y := predecessor_at(p, b, q)) is not None and y < p
            ]
            assert len(brute) <= 1, (q, p, brute)
            got = smaller_predecessor(p, q)
            assert (got[1] if got else None) == (brute[0] if brute else None)
            checked += 1
    assert checked == len(QS) * 500


def test_lemma_u_refinement_for_p_at_least_q():
    """For p >= q the smaller predecessor is the b=1 one, and exists iff p = -q (mod 3)."""
    for q in QS:
        for p in range(q, q + 600, 2):
            if p % 2 == 0 or p % 3 == 0:
                continue
            got = smaller_predecessor(p, q)
            if (p + q) % 3 == 0:  # p = -q (mod 3)
                assert got is not None
                assert got[0] == 1 and got[1] == (2 * p - q) // 3
            else:
                assert got is None


def test_predecessor_count_formula():
    """LEMMA-U(c): the closed-form count matches brute force."""
    for q in QS[:10]:
        for p in range(1, 200, 2):
            for bound in (p, 3 * p, 50 * p):
                brute = sum(
                    1
                    for b in range(1, 60)
                    if (y := predecessor_at(p, b, q)) is not None and y <= bound
                )
                assert count_predecessors_below(p, bound, q) == brute, (q, p, bound)
