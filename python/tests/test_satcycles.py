"""The SAT encoding of S_q-cycles agrees with exhaustive search on every box tested."""

from __future__ import annotations

import pytest

from collatz_maxodd.cycles import find_cycles
from collatz_maxodd.satcycles import (
    Cnf,
    adic3_gates,
    cnf_stats,
    encode,
    enumerate_cycles,
    enumerate_max_only,
    passes_gates,
    residue_automaton,
)

pysat = pytest.importorskip("pysat")


def expected(q: int, L: int, W: int) -> set[tuple[int, ...]]:
    return {c.elements for c in find_cycles(q, 2**W - 1) if c.L == L}


@pytest.mark.parametrize("q", [1, 5, 7, 11, 13, 17, 19, 23])
@pytest.mark.parametrize("W", [8, 12])
def test_sat_matches_search_small_boxes(q: int, W: int) -> None:
    for L in range(1, 7):
        found = {e for e, _ in enumerate_cycles(q, L, W)}
        assert found == expected(q, L, W), (q, L, W)


def test_gates_change_nothing() -> None:
    for q, L, W in [(5, 3, 8), (11, 8, 8), (13, 5, 12), (1, 1, 10), (1, 4, 12)]:
        assert enumerate_cycles(q, L, W, gates=True) == enumerate_cycles(q, L, W, gates=False)


def test_long_cycles_q5_and_q13() -> None:
    # the two 17-cycles of 3n+5 below 2^12, and the four 5-cycles of 3n+13
    assert {e for e, _ in enumerate_cycles(5, 17, 12)} == expected(5, 17, 12)
    assert len(expected(5, 17, 12)) == 2
    assert {e for e, _ in enumerate_cycles(13, 5, 12)} == expected(13, 5, 12)
    assert len(expected(13, 5, 12)) == 7


def test_q1_box_has_only_the_trivial_cycle() -> None:
    for L in range(1, 9):
        assert enumerate_cycles(1, L, 16) == ([((1,), (2,))] if L == 1 else [])


def test_halvings_are_reported_and_sizes_are_modest() -> None:
    cyc = enumerate_cycles(5, 3, 8)
    assert cyc == [((37, 29, 23), (2, 2, 1)), ((49, 19, 31), (3, 1, 1))]
    nv, ncl, nlit = cnf_stats(encode(1, 8, 20))
    assert nv < 6000 and ncl < 60000, (nv, ncl, nlit)


def test_residue_automaton_is_exact():
    from pysat.solvers import Solver

    W = 7
    for m in (3, 9, 27):
        for r in range(m):
            c = Cnf()
            bits = [c.var() for _ in range(W)]
            S = residue_automaton(c, bits, m)
            c.require(S[r])
            got = []
            with Solver(name="cd", bootstrap_with=c.clauses) as s:
                while s.solve():
                    model = {lit for lit in s.get_model() if lit > 0}
                    v = sum(1 << j for j in range(W) if bits[j] in model)
                    got.append(v)
                    s.add_clause([-bits[j] if (v >> j) & 1 else bits[j] for j in range(W)])
            assert sorted(got) == [v for v in range(2**W) if v % m == r], (m, r)


def test_adic3_gates_change_nothing_on_the_census_boxes():
    for q, L, W in [(5, 3, 8), (5, 17, 12), (7, 2, 8), (11, 8, 8), (13, 5, 12), (17, 18, 8), (19, 5, 8), (23, 2, 8)]:
        assert enumerate_cycles(q, L, W, gates3=3) == enumerate_cycles(q, L, W, gates3=0), (q, L, W)


def test_adic3_gates_are_the_documented_sets():
    g = adic3_gates(1, 3)
    assert g[0] == (1, 9, (2, 8))
    assert g[1] == (1, 27, (2, 17, 20, 26))
    assert g[2] == (9, 81, (20, 26, 44, 71, 74, 80))
    assert adic3_gates(1, 5)[4][:2] == (86, 729) and len(adic3_gates(1, 5)[4][2]) == 22
    assert adic3_gates(5, 2)[1] == (7, 27, (4, 10, 19, 22))  # 11*5/7 = 7.86 -> M > 7


def test_max_only_matches_arithmetic_filter():
    for q, W, d in [(1, 12, 5), (1, 10, 3), (5, 10, 3), (7, 9, 2), (1, 5, 5), (1, 4, 3)]:
        got = enumerate_max_only(q, W, gates=True, gates3=d)
        want = [n for n in range(1, 2**W, 2) if passes_gates(n, q, True, d)]
        assert got == want, (q, W, d, len(got), len(want))
    survivors = enumerate_max_only(1, 12, True, 5)
    assert 1 in survivors and len(survivors) < 2**11 * 0.03


def test_q1_ladder_with_full_gates_is_unsat_above_L1():
    for L in range(1, 7):
        assert enumerate_cycles(1, L, 16, gates3=5) == ([((1,), (2,))] if L == 1 else []), L
