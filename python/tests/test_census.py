"""The 3n+q cycle census, and the congruence every primitive cycle obeys.

These are the checks behind docs/CENSUS.md.  The point of the census is that
3n+q is the only place the Collatz cycle heuristic can be tested against a
world where cycles actually exist.
"""

from __future__ import annotations

import json
import math
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]

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


# ---------------------------------------------------------------------------
# The theorems inside the census, as lean/Collatz/Census.lean states them.
#
# The census row of the accounting table bundled three theorems in with three
# measurements.  These are the theorems; the measurements (variance/mean, the
# tail-rate bracket, the box dimension) are not formalized and are not theorems.
# ---------------------------------------------------------------------------


def _halvings(q: int, el: list[int]) -> int:
    return total_halvings(el, q)


def test_q_divides_two_pow_B_minus_three_pow_L():
    """Collatz.Cycle.q_dvd_sub -- the census's arithmetic engine.

    Cycles do not scatter across q at random: q must divide one of the numbers
    2^B - 3^L, and those are sparse.  That is the mechanism behind the
    over-dispersion the census measures.
    """
    n = 0
    for q in [q for q in range(1, 600, 2) if q % 3]:
        for L, M, el in primitive_cycles(q, 40 * q):
            B = _halvings(q, el)
            assert (2 ** B - 3 ** L) % q == 0, (q, L, B)
            assert math.gcd(M, q) == 1          # primitivity => coprime maximum
            n += 1
    assert n > 500


def test_the_burst_identity():
    """Collatz.Cycle.burst: 2^B - 3^L = q  =>  M*q = c_L.

    An exact hit collapses the cycle equation, so every admissible halving
    vector of that (L, B) yields a candidate at once.
    """
    def cc(q, bs):
        c = 0
        for k, b in enumerate(bs):
            c = 2 ** b * c + 3 ** k * q
        return c

    from collatz_maxodd.syracuse import v2
    hits = 0
    for q in [q for q in range(1, 600, 2) if q % 3]:
        for L, M, el in primitive_cycles(q, 40 * q):
            B = _halvings(q, el)
            if 2 ** B - 3 ** L != q:
                continue
            # halving pattern read backwards from the maximum
            fwd, y = [], M
            for _ in range(L):
                b = v2(3 * y + q)
                fwd.append(b)
                y = (3 * y + q) >> b
            assert M * q == cc(q, list(reversed(fwd))), (q, L, B, M)
            hits += 1
    assert hits > 5


def test_q1_gets_exactly_one_burst():
    """Collatz.q1_burst: 2^B = 3^L + 1 with L >= 1 forces (L, B) = (1, 2).

    The mod-8 argument, checked: 3^L + 1 is 2 or 4 mod 8, never 0, so 2^B <= 4;
    and 3^L + 1 >= 10 for L >= 2.  No deep theorem needed -- which is exactly
    why q = 1 is unlike every other q in the census.
    """
    for L in range(1, 60):
        assert (3 ** L + 1) % 8 in (2, 4)       # never divisible by 8
    sols = [(L, B) for L in range(1, 200) for B in range(1, 350)
            if 2 ** B == 3 ** L + 1]
    assert sols == [(1, 2)]
    # and (1, 2) is the trivial cycle 1 -> 4 -> 2 -> 1
    assert 2 ** 2 == 3 ** 1 + 1


def test_a_k_matches_the_lean_residue_count():
    """Collatz.aa -- a_k as a count over residues mod 3^k.

    The Lean kernel checks a_1..a_4 = 1, 2, 3, 6 directly (k=5 exceeds Lean's
    default maxRecDepth, and set_option is banned).  This reimplements the same
    residue recursion and checks it against the package, further out.
    """
    from collatz_maxodd.deathdepth import surviving_residue_count

    def alive(y, B, j, d):
        if d == 0:
            return True
        if y % 3 == 0:
            return False
        b = 2 if y % 3 == 1 else 1
        while (1 << (B + b)) <= 3 ** (j + 1):
            num = (1 << b) * y - 1
            if num % 3 == 0 and alive(num // 3, B + b, j + 1, d - 1):
                return True
            b += 2
        return False

    counts = [sum(1 for r in range(3 ** k) if alive(r, 0, 0, k)) for k in range(1, 8)]
    assert counts[:4] == [1, 2, 3, 6]          # exactly what Lean's aa_1..aa_4 say
    assert counts == surviving_residue_count(7)
    assert all(c >= 1 for c in counts)         # aa_pos: the sieve never empties


def test_what_is_deliberately_not_formalized():
    """The rest of the census row: two measurements and one open question.

    Each is declined for a different reason, and the reasons matter:

    - over-dispersion IS a proposition about integers (no reals needed); the
      obstacle is infeasibility inside the kernel, not category.
    - "Poisson is rejected" is a modelling judgement, not a proposition.
    - the tail RATE is open -- separating the models needs k ~ 36.
    - the box dimension rests on an unresolved limit.
    """
    from collatz_maxodd.census import primitive_cycles as _pc

    counts = [sum(1 for _ in _pc(q, 100 * q))
              for q in [q for q in range(1, 200, 2) if q % 3]]
    n = len(counts)
    total = sum(counts)
    total_sq = sum(c * c for c in counts)
    # the statistic as a pure-integer inequality -- this is what Lean *could*
    # state; what it cannot do is reduce the census that produced the counts
    assert n * total_sq - total * total > n * total          # var/mean > 1
    # and it is sample-dependent: the census headline is 4.614 on q <= 1000
    mean = total / n
    var = total_sq / n - mean * mean
    assert 1.0 < var / mean < 4.614

    # the tail rate is an interval the project has not narrowed, and the two
    # candidate models sit on either side of the measured value
    tail = json.loads((ROOT / "web" / "asym.json").read_text())
    lo, hi = tail["bracket"]
    assert lo < hi and hi - lo > 0.01        # genuinely unresolved, not a value
    assert tail["k_decide"] > 30             # and out of computational reach

    # the box dimension is an estimate with an interval, not a theorem
    dim = json.loads((ROOT / "web" / "padic.json").read_text())["dimension"]
    assert dim["lo"] < dim["estimate_at_k24"] <= dim["hi"]
    assert 0 < dim["lo"] and dim["hi"] < 1
