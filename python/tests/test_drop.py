"""Witnesses for docs/DROP.md: the drop function ``f(n) = n - S(n)`` on odd ``n``.

Every number quoted on ``web/drop.html`` is pinned here.  The 3n+q census (conftest)
is a harness only: every headline is about q = 1.
"""

from __future__ import annotations

from collections import Counter

import pytest

from collatz_maxodd.cycles import find_cycles
from collatz_maxodd.drop import (
    cycle_drops,
    drop,
    drop_fiber,
    drop_multiplicity,
    drop_with_exponent,
    height_class,
    multiplicity_witness,
    rise_fall_totals,
    sources_at_height,
    trajectory_drops,
    two_pow_minus_3,
)
from collatz_maxodd.syracuse import syracuse_with_exponent

N = 1 << 16


def brute_fibers(q: int, bound: int) -> dict[int, list[int]]:
    fib: dict[int, list[int]] = {}
    for n in range(1, bound, 2):
        fib.setdefault(drop(n, q), []).append(n)
    return fib


# ---------------------------------------------------------------------------
# D1: parity and sign
# ---------------------------------------------------------------------------


def test_d1_parity_and_sign() -> None:
    for n in range(1, N, 2):
        d, x = drop_with_exponent(n)
        assert d % 2 == 0
        assert (d < 0) == (x == 1) == (n % 4 == 3)
        assert (d == 0) == (n == 1)
        assert (d > 0) == (n % 4 == 1 and n > 1)
        if x >= 2:
            assert 4 * d >= n - 1


def test_closed_form() -> None:
    for n in range(1, N, 2):
        d, x = drop_with_exponent(n)
        assert d << x == (two_pow_minus_3(x)) * n - 1


# ---------------------------------------------------------------------------
# D2: height classes
# ---------------------------------------------------------------------------

#: (x, 2^x - 3, first source n0, first drop d0): the table on the page
HEIGHT_TABLE = [
    (1, -1, 3, -2), (2, 1, 1, 0), (3, 5, 13, 8), (4, 13, 5, 4), (5, 29, 53, 48), (6, 61, 21, 20),
    (7, 125, 213, 208), (8, 253, 85, 84), (9, 509, 853, 848), (10, 1021, 341, 340),
    (11, 2045, 3413, 3408), (12, 4093, 1365, 1364),
]


def test_d2_height_classes_against_brute_force() -> None:
    bound = 1 << 20
    by_x: dict[int, list[int]] = {}
    for n in range(1, bound, 2):
        by_x.setdefault(syracuse_with_exponent(n)[1], []).append(n)
    for x in range(1, 15):
        h = height_class(x)
        assert h.n_step == 1 << (x + 1) and h.d_step == 2 * two_pow_minus_3(x)
        want = by_x[x]
        got = [n for n, _, _ in sources_at_height(x, len(want))]
        assert got == want
        assert [d for _, _, d in sources_at_height(x, len(want))] == [drop(n) for n in want]
        assert [s for _, s, _ in sources_at_height(x, len(want))] == [syracuse_with_exponent(n)[0] for n in want]


def test_d2_table_on_the_page() -> None:
    for x, m, n0, d0 in HEIGHT_TABLE:
        h = height_class(x)
        assert (two_pow_minus_3(x), h.n0, h.d0) == (m, n0, d0)
        assert drop(n0) == d0 and drop_with_exponent(n0)[1] == x


def test_d2_general_q() -> None:
    for q in (5, 7, 11, 13, 17):
        by_x: dict[int, list[int]] = {}
        for n in range(1, N, 2):
            by_x.setdefault(syracuse_with_exponent(n, q)[1], []).append(n)
        for x in range(1, 10):
            want = by_x[x]
            assert [n for n, _, _ in sources_at_height(x, len(want), q)] == want


# ---------------------------------------------------------------------------
# D3: fibers
# ---------------------------------------------------------------------------


def test_d3_fiber_formula_matches_brute_force() -> None:
    # n = s + d <= 4d + 1 for d > 0, and n = -2d - 1 for d < 0: below 2^17 the brute-force
    # fibers are complete for |d| <= 2^14.
    fib = brute_fibers(1, 1 << 17)
    for d in range(-(1 << 14), (1 << 14) + 1):
        assert drop_fiber(d) == fib.get(d, [])


def test_d3_negative_zero() -> None:
    for d in range(-2, -5000, -2):
        assert drop_fiber(d) == [-2 * d - 1]
    assert drop_fiber(0) == [1]
    assert drop_fiber(3) == [] and drop_fiber(-7) == []


def test_d3_multiplicity_is_a_divisor_count() -> None:
    for d in range(2, 20001, 2):
        divisors = 0
        x = 2
        while two_pow_minus_3(x) <= 3 * d + 1:
            if (3 * d + 1) % two_pow_minus_3(x) == 0:
                divisors += 1
            x += 1
        assert drop_multiplicity(d) == divisors >= 1


def test_d3_general_q() -> None:
    for q in (5, 7, 11):
        fib = brute_fibers(q, 1 << 16)
        for d in range(-(1 << 13), (1 << 13) + 1):
            assert drop_fiber(d, q) == fib.get(d, [])


#: the first drop with k sources, and the distribution of sources over even d <= 10^5
FIRST_WITH_K = {1: 2, 2: 4, 3: 48, 4: 628, 5: 15708, 6: 958208}
DISTRIBUTION_1E5 = {1: 34806, 2: 13313, 3: 1774, 4: 104, 5: 3}


def test_d3_records() -> None:
    assert drop_fiber(628) == [693, 773, 1005, 2513]
    assert [drop_with_exponent(n)[1] for n in (2513, 1005, 773, 693)] == [2, 3, 4, 5]
    assert all(drop(n) == 628 for n in drop_fiber(628))
    for k, d in FIRST_WITH_K.items():
        assert drop_multiplicity(d) == k
    first: dict[int, int] = {}
    for d in range(2, 20000, 2):
        first.setdefault(drop_multiplicity(d), d)
    assert first == {k: d for k, d in FIRST_WITH_K.items() if d < 20000}


def test_d3_distribution() -> None:
    assert Counter(drop_multiplicity(d) for d in range(2, 100001, 2)) == DISTRIBUTION_1E5


# ---------------------------------------------------------------------------
# D4: unbounded multiplicity
# ---------------------------------------------------------------------------


def test_d4_witnesses() -> None:
    assert multiplicity_witness(7) == 958208
    for x_max in range(2, 11):
        d = multiplicity_witness(x_max)
        assert d % 2 == 0
        assert all((3 * d + 1) % two_pow_minus_3(x) == 0 for x in range(2, x_max + 1))
        assert drop_multiplicity(d) >= x_max - 1
    assert drop_multiplicity(958208) == 6
    for q in (5, 7):
        d = multiplicity_witness(6, q)
        assert drop_multiplicity(d, q) >= 5


# ---------------------------------------------------------------------------
# D5: telescoping, trajectories, cycles
# ---------------------------------------------------------------------------

#: (n, odd steps, rises, rise total, fall total, largest drop, most negative drop)
TRAJECTORIES = [
    (27, 41, 24, 5396, 5422, 2500, -1026),
    (97, 43, 24, 5436, 5532, 2500, -1026),
    (871, 65, 38, 79006, 79876, 38796, -21222),
    (6171, 96, 54, 578412, 584582, 203208, -108378),
    (77031, 129, 76, 17387672, 17464702, 4569378, -2437002),
    (837799, 195, 114, 2606145054, 2606982852, 968419458, -330553842),
]


def test_d5_telescoping() -> None:
    for n in range(1, 20001, 2):
        steps = trajectory_drops(n)
        assert sum(st.d for st in steps) == n - 1
        assert all(st.s == nxt.n for st, nxt in zip(steps, steps[1:]))
    assert trajectory_drops(1) == []


def test_d5_trajectory_table() -> None:
    for n, L, rises, rt, ft, big, small in TRAJECTORIES:
        steps = trajectory_drops(n)
        assert len(steps) == L
        assert sum(1 for st in steps if st.x == 1) == rises
        assert rise_fall_totals(steps) == (rt, ft)
        assert ft - rt == n - 1
        assert max(st.d for st in steps) == big and min(st.d for st in steps) == small


def test_d5_cycles_balance(census) -> None:
    for c in census:
        steps = cycle_drops(c.elements, c.q)
        assert sum(st.d for st in steps) == 0
        r, f = rise_fall_totals(steps)
        assert r == f
        assert all(st.s == nxt.n for st, nxt in zip(steps, steps[1:] + steps[:1]))
    assert [c.elements for c in find_cycles(1, 1 << 16)] == [(1,)]
    assert cycle_drops((1,)) [0].d == 0


def test_d5_one_lap_for_general_q() -> None:
    for c in find_cycles(5, 5000):
        steps = trajectory_drops(c.elements[0], 5)
        assert [st.n for st in steps] == list(c.elements)


# ---------------------------------------------------------------------------
# the 2-cycle equation in drop coordinates (a special case of Steiner 1977)
# ---------------------------------------------------------------------------


def test_no_two_cycle_in_drop_coordinates() -> None:
    # a rise a -> b = a + (a+1)/2 followed by a fall b -> a means d = (a+1)/2, a = 2d - 1,
    # b = 3d - 1 and S(3d - 1) = 2d - 1, i.e. d (2^{x+1} - 9) = 2^x - 2: no solution.
    for x in range(1, 61):
        num, den = (1 << x) - 2, (1 << (x + 1)) - 9
        assert den == 0 or num % den != 0 or num // den <= 0
    for d in range(2, 100001, 2):
        assert drop(3 * d - 1) != d


# ---------------------------------------------------------------------------
# zero-sum combinations (page section 4)
# ---------------------------------------------------------------------------

from collatz_maxodd.drop import (  # noqa: E402
    can_be_min_odd,
    is_chain,
    max_gate_ok,
    min_gate_ok,
    zero_sum_sets,
)


#: (bound, size, zero-sum sets, chains) as quoted on the page
ZERO_SUM_COUNTS = [(400, 2, 83, 0), (10_000, 2, 2109, 0), (120, 3, 383, 0), (400, 3, 4701, 0), (60, 4, 511, 0), (100, 4, 2737, 0)]


def test_zero_sum_counts() -> None:
    for bound, k, want, chains in ZERO_SUM_COUNTS:
        zs = zero_sum_sets(bound, k)
        assert len(zs) == want
        assert sum(1 for c in zs if is_chain(c)) == chains
    # the ledger page's 408 triples below 120 count 1 as a member: 383 + the 25 pairs below 120
    assert len(zero_sum_sets(120, 2)) == 25 and 383 + 25 == 408


def test_zero_sum_pairs_are_rise_source_plus_a_source_of_d() -> None:
    zs = zero_sum_sets(10_000, 2)
    for pair in zs:
        rise = [n for n in pair if drop(n) < 0]
        assert len(rise) == 1
        d = -drop(rise[0])
        fall = pair[1] if pair[0] == rise[0] else pair[0]
        assert rise[0] == 2 * d - 1 and fall in drop_fiber(d)
    falls = sum(1 for b in range(5, 10_000, 4) if drop(b) <= (10_000 - 1) // 2)
    assert falls == len(zs) == 2109


def test_zero_sum_family_every_size() -> None:
    for k in range(2, 60):
        rises = [4 * i - 1 for i in range(1, k)]
        square = (2 * k - 1) ** 2
        assert [drop(n) for n in rises] == [-2 * i for i in range(1, k)]
        assert drop_with_exponent(square) == (k * (k - 1), 2)
        members = tuple(rises + [square])
        assert len(set(members)) == k and sum(drop(n) for n in members) == 0
        assert not is_chain(members)


def test_chain_iff_cycle_on_the_census(census) -> None:
    for c in census:
        if c.q == 1:
            continue
        # a lap of any census cycle is a chain of its own map; the q=1 chain test rejects it
        assert sum(st.d for st in cycle_drops(c.elements, c.q)) == 0
    assert is_chain((1,))
    assert not is_chain((3, 9)) and not is_chain((3, 7, 25))


# ---------------------------------------------------------------------------
# the gates at both ends on zero-sum sets (page section 4, docs/DROP.md Z5)
# ---------------------------------------------------------------------------

#: gated zero-sum counts, as quoted on the page: (bound, size) -> {depth: count}
GATED_COUNTS = {
    (400, 2): {1: 11, 2: 4, 3: 1, 4: 1, 6: 0},
    (10_000, 2): {1: 277, 2: 93, 3: 35, 4: 18, 6: 7},
    (120, 3): {1: 11, 2: 5, 3: 2, 4: 0, 6: 0},
    (400, 3): {1: 169, 2: 61, 3: 27, 4: 1, 6: 0},
    (60, 4): {1: 14, 2: 9, 3: 0, 4: 0, 6: 0},
    (100, 4): {1: 124, 2: 9, 3: 0, 4: 0, 6: 0},
}


def test_min_gate_depths() -> None:
    for m in range(3, 1 << 14, 2):
        assert can_be_min_odd(m, 1, 1) == (m % 4 == 3 and m % 3 != 0)
        if m > 5 and m % 3:
            assert can_be_min_odd(m, 1, 2) == (m % 4 == 3 and m % 16 != 3)
    assert min_gate_ok(1, 1, 8) and not min_gate_ok(3, 1, 2)
    assert min_gate_ok(7, 1, 3) and not min_gate_ok(7, 1, 4)  # 7 -> 11 -> 17 -> 13 -> 5
    # no backward half: predecessors above m avoiding multiples of 3 always exist
    for m in range(5, 3001, 2):
        if m % 3:
            b = 1 if m % 3 == 2 else 2
            preds = [((1 << bb) * m - 1) // 3 for bb in (b + 2, b + 4, b + 6)]
            assert all(p > m and syracuse_with_exponent(p)[0] == m for p in preds)
            assert any(p % 3 for p in preds)


def test_end_gates_on_the_census(census) -> None:
    for c in census:
        assert max_gate_ok(c.M, c.q, 6)
        assert min_gate_ok(min(c.elements), c.q, 6)


def test_gated_zero_sum_counts() -> None:
    for (bound, k), by_depth in GATED_COUNTS.items():
        for depth, want in by_depth.items():
            zs = zero_sum_sets(bound, k, gated=True, depth=depth)
            assert len(zs) == want
            assert not any(is_chain(t) for t in zs)
    assert zero_sum_sets(10_000, 2, gated=True, depth=4)[:5] == [(79, 161), (223, 449), (295, 593), (319, 641), (967, 1937)]
    assert zero_sum_sets(400, 3, gated=True, depth=4) == [(31, 47, 161)]
    assert [drop(n) for n in (31, 47, 161)] == [-16, -24, 40]


def test_gated_pairs() -> None:
    for a, b in zero_sum_sets(10_000, 2, gated=True, depth=1):
        d = drop(b)
        assert d > 0 and a == 2 * d - 1 and b == 4 * d + 1

    def first_d(depth: int) -> int:
        d = 2
        while not (max_gate_ok(4 * d + 1, 1, depth) and min_gate_ok(2 * d - 1, 1, depth)):
            d += 2
        return d

    assert [first_d(depth) for depth in range(1, 9)] == [4, 4, 40, 40, 112, 112, 592, 592]
    assert sum(1 for d in range(2, 200_000, 2) if max_gate_ok(4 * d + 1, 1, 8) and min_gate_ok(2 * d - 1, 1, 8)) == 128


def test_gate_survivor_shares() -> None:
    odds = range(3, 1 << 16, 2)

    def share(gate, depth: int) -> float:
        return round(sum(gate(m, 1, depth) for m in odds) / len(odds), 4)

    assert [share(min_gate_ok, depth) for depth in (1, 2, 4, 8)] == [0.3333, 0.25, 0.1354, 0.0597]
    assert [share(max_gate_ok, depth) for depth in (1, 2, 4, 8)] == [0.1111, 0.0556, 0.0183, 0.0041]
