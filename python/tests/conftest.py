"""Shared fixtures: one exhaustive cycle census, reused by every theorem test."""

from __future__ import annotations

import pytest

from collatz_maxodd.cycles import Cycle, find_cycles, find_cycles_multi

#: q values searched: odd, not divisible by 3, up to Q_MAX.
Q_MAX = 999
#: every S_q-cycle with maximum odd element <= M_BOUND is found (see cycles.py).
M_BOUND = 20_000


@pytest.fixture(scope="session")
def census() -> list[Cycle]:
    """All S_q-cycles with M <= 20000 for every admissible q <= 999.

    Roughly 2100 cycles.  This is the empirical test bed: theorems are checked
    against *every* one of them, with the audited hypotheses attached.
    """
    qs = [q for q in range(1, Q_MAX + 1, 2) if q % 3]
    return find_cycles_multi(qs, M_BOUND)


@pytest.fixture(scope="session")
def multi(census: list[Cycle]) -> list[Cycle]:
    """The cycles with L >= 2 (i.e. not fixed points)."""
    return [c for c in census if c.L >= 2]


@pytest.fixture(scope="session")
def big_M(census: list[Cycle]) -> list[Cycle]:
    """The cycles with M > q -- the hypothesis of T2/T3/T4."""
    return [c for c in census if c.M > c.q]


def cycle_for(q: int, elements: tuple[int, ...]) -> Cycle:
    """Look up one specific documented cycle, or fail loudly."""
    for c in find_cycles(q, max(elements) + 1):
        if c.elements == elements:
            return c
    raise AssertionError(f"cycle {elements} not found for q={q}")
