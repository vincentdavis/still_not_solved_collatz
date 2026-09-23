"""The SAT encoding of S_q-cycles agrees with exhaustive search on every box tested."""

from __future__ import annotations

import pytest

from collatz_maxodd.cycles import find_cycles
from collatz_maxodd.satcycles import cnf_stats, encode, enumerate_cycles

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
