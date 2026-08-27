"""The 3n+q cycle census, and the congruence every primitive cycle obeys.

These are the checks behind docs/CENSUS.md.  The point of the census is that
3n+q is the only place the Collatz cycle heuristic can be tested against a
world where cycles actually exist.
"""

from __future__ import annotations

from functools import reduce
from math import gcd

import pytest

from collatz_maxodd.census import (
    cycles_upto,
    exact_hits,
    primitive_cycles,
    satisfies_congruence,
    total_halvings,
)

ADMISSIBLE = [q for q in range(1, 400, 2) if q % 3]


def test_finds_the_cycles_quoted_throughout_the_project():
    assert [(L, M) for L, M, _ in primitive_cycles(5, 100)] == [(3, 49), (3, 37)]
    assert [(L, M) for L, M, _ in primitive_cycles(7, 50)] == [(2, 11)]
    assert [(L, M) for L, M, _ in primitive_cycles(1, 10_000)] == []
    # the cycle that refuted the "L >= 3" form of T5
    assert (3, 53) in [(L, M) for L, M, _ in primitive_cycles(37, 200)]


def test_trivial_fixed_point_is_found_but_is_not_primitive_nontrivial():
    assert (1, 1, [1]) in cycles_upto(1, 100)
    assert (1, 7, [7]) in cycles_upto(7, 100)


def test_congruence_theorem_on_a_full_census():
    """q | 2^B - 3^L for every primitive cycle.  The census is the evidence."""
    n = 0
    for q in ADMISSIBLE:
        for L, _M, el in primitive_cycles(q, 40 * q):
            n += 1
            assert satisfies_congruence(q, L, total_halvings(el, q)), (q, L, el)
    assert n > 200, f"census too small to be meaningful ({n} cycles)"


def test_primitivity_implies_every_element_coprime_to_q():
    """The lemma the theorem rests on: p | q divides all elements or none."""
    for q in ADMISSIBLE:
        for _L, _M, el in primitive_cycles(q, 40 * q):
            assert all(gcd(n, q) == 1 for n in el), (q, el)


def test_scaled_cycles_are_correctly_excluded_as_imprimitive():
    """q=25's {95,155,245} is 5x q=5's {19,31,49} and must not be counted."""
    allc = [el for _L, _M, el in cycles_upto(25, 300)]
    assert [95, 155, 245] in allc
    prim = [el for _L, _M, el in primitive_cycles(25, 300)]
    assert [95, 155, 245] not in prim
    assert reduce(gcd, [95, 155, 245], 25) == 5


def test_q1_has_exactly_one_exact_hit_and_it_is_the_trivial_cycle():
    """2^B - 3^L = 1 has only (L,B) = (1,2) for L >= 1, by an elementary mod-8
    argument -- which is why q=1 gets no burst of cycles."""
    assert exact_hits(1) == [(0, 1), (1, 2)]
    for L in range(2, 200):
        t = 3 ** L + 1
        assert t % 8 in (2, 4), L          # so 2^B = t forces B <= 2
        assert (1 << (t.bit_length() - 1)) != t


@pytest.mark.parametrize("q,expected", [(5, [(1, 3), (3, 5)]), (7, [(0, 3), (2, 4)]), (13, [(1, 4), (5, 8)]),
     (23, [(2, 5)]), (29, [(1, 5)]), (47, [(4, 7)])])
def test_exact_hits_small_q(q, expected):
    assert exact_hits(q, max_L=40) == expected


def test_exact_hit_q_carry_more_cycles():
    """The burst mechanism: q admitting 2^B - 3^L == q are cycle-rich."""
    hit, non = [], []
    for q in ADMISSIBLE:
        n = len(primitive_cycles(q, 40 * q))
        (hit if exact_hits(q, max_L=60) and q > 1 else non).append(n)
    assert sum(hit) / len(hit) > 1.5 * (sum(non) / len(non))


def test_counts_are_over_dispersed_not_poisson():
    """The heuristic assumes a q-independent Poisson rate.  It is not."""
    c = [len(primitive_cycles(q, 40 * q)) for q in ADMISSIBLE]
    mean = sum(c) / len(c)
    var = sum((x - mean) ** 2 for x in c) / len(c)
    assert var / mean > 2.0, f"var/mean = {var/mean:.2f}, expected clear over-dispersion"


def test_rejects_bad_q():
    for bad in (2, 3, 9, 0, -5):
        with pytest.raises(ValueError):
            cycles_upto(bad, 100)
