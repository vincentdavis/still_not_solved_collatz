"""Witnesses for docs/LANDING.md: the landing form (s, x) of the odd step.

Every number the document labels COMPUTED without an explicit command is pinned
here (the two CITED densities of GROUND_TRUTH section 4b are not recomputed).
No novelty is claimed there; these tests are the exact-computation side of its
labels.
Conventions (docs/LANDING.md section 0): for odd n, ``x = v2(3n+q)`` and
``s = (3n+q)/2^x`` -- n is the *source*, s the *target*, x the *height*; the
source is recovered by ``n = (2^x s - q)/3``.  The 3n+q census (conftest) is a
harness only: every headline is about q = 1.
"""

from __future__ import annotations

import math
from fractions import Fraction
from itertools import combinations, product
from random import Random

import pytest

from collatz_maxodd.backtree import c_constant, floor_bound
from collatz_maxodd.cycleeq import cycle_constant
from collatz_maxodd.deathdepth import surviving_residue_count, surviving_residues
from collatz_maxodd.sieve import (
    surviving_residues_mod2,
    surviving_residues_mod3,
    surviving_residues_mod3_no_size,
)
from collatz_maxodd.syracuse import syracuse_with_exponent, v2
from collatz_maxodd.words import n_words, phi, words

# ---------------------------------------------------------------------------
# helpers (the definitions of the document, written out once)
# ---------------------------------------------------------------------------

#: dead column x0(s mod 9): the source (2^x s - 1)/3 is a multiple of 3 iff x = x0 (mod 6)
X0 = {1: 0, 2: 5, 4: 4, 5: 1, 7: 2, 8: 3}


def landing(n: int, q: int = 1) -> tuple[int, int]:
    """lambda(n) = (S_q(n), v2(3n+q))."""
    return syracuse_with_exponent(n, q)


def source(s: int, x: int, q: int = 1) -> int:
    """sigma(s, x) = (2^x s - q)/3 (exact division asserted by the caller)."""
    return ((1 << x) * s - q) // 3


def admissible(s: int, x: int, q: int = 1) -> bool:
    return s % 2 == 1 and s % 3 != 0 and x >= 1 and ((1 << x) * s - q) % 3 == 0 and (1 << x) * s > q


def landing_list(c) -> list[tuple[int, int]]:
    """The cycle as a cyclic list of landings (s_i, x_i) = lambda(n_i), s_i = n_{i+1}."""
    L = c.L
    return [(c.elements[(i + 1) % L], c.forward_halvings[i]) for i in range(L)]


# ---------------------------------------------------------------------------
# 0. objects and the bijection
# ---------------------------------------------------------------------------

def test_landing_map_is_a_bijection_onto_admissible_landings():
    """odd n < 10^5 <-> admissible (s, x): injective, admissible, inverted by sigma; ledger identities."""
    seen = set()
    for n in range(1, 100_000, 2):
        s, x = landing(n)
        assert (s, x) not in seen
        seen.add((s, x))
        assert s % 2 == 1 and s % 3 != 0 and x >= 1
        assert s % 3 == (1 if x % 2 == 0 else 2)          # s = (-1)^x (mod 3)
        assert source(s, x) == n                            # sigma(lambda(n)) = n
        assert 3 * n + 1 - s == s * ((1 << x) - 1)          # descent D(n) = s(2^x - 1)
        assert 3 * (2 * n + 1) == (1 << (x + 1)) * s + 1    # ascent 2n+1 = (2^{x+1}s + 1)/3
        assert (s > n) == (x == 1) or n == 1                # rise iff x = 1 (fixed cell (1,2) aside)
    assert len(seen) == 50_000


def test_every_admissible_landing_has_exactly_one_source():
    """399 996 admissible (s, x) with s <= 10^5, x <= 24 satisfy lambda(sigma(s, x)) = (s, x)."""
    count = 0
    for s in range(1, 100_001, 2):
        if s % 3 == 0:
            continue
        x0 = 1 if s % 3 == 2 else 2
        for x in range(x0, 25, 2):
            assert admissible(s, x)
            n = source(s, x)
            assert n % 2 == 1 and landing(n) == (s, x)
            count += 1
        # the other parity is never admissible
        assert not any(admissible(s, x) for x in range(3 - x0, 25, 2))
    assert count == 399_996


def test_landing_bijection_survives_on_the_3nq_harness():
    """General q: lambda_q, sigma_q are inverse on odd n < 20 000 for 33 admissible q <= 101 (harness only)."""
    qs = [q for q in range(5, 102, 2) if q % 3]
    assert len(qs) == 33
    for q in qs:
        for n in range(1, 20_000, 2):
            s, x = landing(n, q)
            assert s % 2 == 1 and ((1 << x) * s - q) % 3 == 0 and (1 << x) * s > q
            assert source(s, x, q) == n and 3 * n + q - s == s * ((1 << x) - 1)


# ---------------------------------------------------------------------------
# 1. a cycle in landing coordinates, the cycle equation, both ledgers
# ---------------------------------------------------------------------------

def test_cycles_chain_in_landing_coordinates_and_satisfy_the_cycle_equation(census):
    """2127 census cycles: chaining 3 s_{i-1} + q = 2^{x_i} s_i; 3^k y_k = 2^{B_k} M - c_k; M(2^B - 3^L) = c_L.

    Also the minimum gate (434/434 with m >= q, L >= 2: one halving out, m = q+2 (mod 4), 3 does not divide m)
    and the over-cap prefix of the harness cycle q = 47, M = 175, backward word (1,2,2,2), B_3 = 5 > 4.
    """
    assert len(census) == 2127
    height_one_into_M = min_gate = 0
    for c in census:
        q, L = c.q, c.L
        lands = landing_list(c)
        for i in range(L):
            s, x = lands[i]
            s_prev = lands[i - 1][0]
            assert 3 * s_prev + q == (1 << x) * s, c            # chaining condition
            assert admissible(s, x, q)
        bs = c.backward_halvings
        M = c.M
        for k in range(1, L + 1):
            B_k = sum(bs[:k])
            assert 3**k * c.y(k) == (1 << B_k) * M - c_constant(bs[:k], q), c
        assert M * ((1 << c.B) - 3**L) == c_constant(bs, q) == cycle_constant(c) > 0, c
        if M > q:
            assert c.b1 == 1, c                                  # T2: the landing into M has height 1
            height_one_into_M += 1
        m = c.min_element
        if L >= 2 and m >= q:                                    # minimum gate (LEDGER section 3, Minimum.lean m_step_one)
            i = c.elements.index(m)
            assert c.forward_halvings[i] == 1 and (m - q - 2) % 4 == 0 and m % 3, c
            min_gate += 1
    assert height_one_into_M == 1482 and min_gate == 434
    over_cap = [c for c in census if c.q == 47 and c.M == 175]
    assert len(over_cap) == 1 and over_cap[0].elements == (175, 143, 119, 101)
    assert over_cap[0].backward_halvings == (1, 2, 2, 2) and floor_bound(3) == 4
    assert sum(over_cap[0].backward_halvings[:3]) == 5 > floor_bound(3)
    assert 3 < Fraction(175, 47) < 4
    # B = f(L) + 1 is forced by L * delta(m) < 1 (LEDGER section 6) but does not force it back: 95 census cycles
    # have B = f(L) + 1 with L * delta(m) >= 1, delta(m) = log2(1 + q/(3m)); among them q = 7, M = 11, L = 2, B = 4
    delta = lambda c: c.L * math.log2(1 + Fraction(c.q, 3 * c.min_element))
    assert not any(c.B != floor_bound(c.L) + 1 for c in census if delta(c) < 1)
    converse_fails = [c for c in census if c.B == floor_bound(c.L) + 1 and delta(c) >= 1]
    assert len(converse_fails) == 95
    assert any(c.q == 7 and c.M == 11 and c.L == 2 and c.B == 4 and floor_bound(2) == 3 for c in converse_fails)


def test_additive_and_multiplicative_ledgers_in_landing_form(census):
    """sum s_i (2^{x_i} - 3) = L q  (rises weight -1, falls 1, 5, 13, ...);  2^B = prod (3 s_i + q)/s_i."""
    for c in census:
        q = c.q
        lands = landing_list(c)
        assert sum(s * ((1 << x) - 3) for s, x in lands) == c.L * q, c
        rises = sum(s for s, x in lands if x == 1)
        falls = sum(s * ((1 << x) - 3) for s, x in lands if x >= 2)
        assert q * c.L + rises == falls, c
        prod = Fraction(1)
        for s, _ in lands:
            prod *= Fraction(3 * s + q, s)
        assert prod == 1 << c.B, c


def test_fixed_cells_are_s_times_2x_minus_3_equals_q(census):
    """q = 1: the unique fixed cell is (1, 2).  q < 200: the 89 solutions of s(2^x - 3) = q are the L = 1 census cycles."""
    assert [(n, x) for n in range(1, 200_001, 2) for x in range(1, 20) if n * ((1 << x) - 3) == 1] == [(1, 2)]
    assert landing(1) == (1, 2) and source(1, 2) == 1 and 3 * 1 + 1 - 1 == 1 * (4 - 1)
    solutions = {(q, s, x) for q in range(1, 200, 2) if q % 3
                 for x in range(2, 13) for s in range(1, 4001, 2) if s * ((1 << x) - 3) == q}
    census_fixed = {(c.q, c.M, c.forward_halvings[0]) for c in census if c.q < 200 and c.L == 1}
    assert solutions == census_fixed and len(solutions) == 89


def test_balance_is_not_closure_in_landing_form():
    """odd n < 400: 83 zero-sum pairs, none product-balanced; 408 (n < 120) and 4784 (n < 400) zero-sum triples, none
    product-balanced (shifted or plain), none closed."""
    S = {n: landing(n)[0] for n in range(1, 400, 2)}
    net = {n: S[n] - n for n in S}
    pairs = [(a, b) for a, b in combinations(net, 2) if net[a] + net[b] == 0]
    assert len(pairs) == 83
    # L = 2: with equal sums, prod(3s+1) = prod(3n+1) is equivalent to s_a s_b = a b, and sum + product force closure
    for a, b in pairs:
        assert ((3 * S[a] + 1) * (3 * S[b] + 1) == (3 * a + 1) * (3 * b + 1)) == (S[a] * S[b] == a * b)
    assert not any(S[a] * S[b] == a * b for a, b in pairs)
    assert not any({S[a], S[b]} == {a, b} for a, b in pairs)
    for bound, count in ((120, 408), (400, 4784)):
        net3 = {n: net[n] for n in range(1, bound, 2)}
        triples = [t for t in combinations(net3, 3) if sum(net3[v] for v in t) == 0]
        assert len(triples) == count
        assert not any({S[a] for a in t} == set(t) for t in triples)
        assert not any(S[a] * S[b] * S[c] == a * b * c for a, b, c in triples)
        assert not any((3 * S[a] + 1) * (3 * S[b] + 1) * (3 * S[c] + 1) == (3 * a + 1) * (3 * b + 1) * (3 * c + 1)
                       for a, b, c in triples)


def test_unions_of_cycles_also_satisfy_sources_equal_targets(census):
    """The set condition {sources} = {targets} characterises unions of cycles, not single cycles (harness)."""
    by_q: dict[int, list] = {}
    for c in census:
        by_q.setdefault(c.q, []).append(c)
    for q, cs in by_q.items():
        for c in cs:
            members = set(c.elements)
            assert {s for s, _ in landing_list(c)} == members
        if len(cs) >= 2:
            union = set(cs[0].elements) | set(cs[1].elements)
            assert {landing(n, q)[0] for n in union} == union       # closed as a set, but two orbits
    # the document's example: q = 7, {7} u {11, 5}
    assert sorted(c.elements for c in by_q[7]) == [(7,), (11, 5)]
    assert {landing(n, 7)[0] for n in (7, 11, 5)} == {7, 11, 5} and landing(7, 7) == (7, 2)


# ---------------------------------------------------------------------------
# 2. what reachability excludes
# ---------------------------------------------------------------------------

def test_targets_are_never_multiples_of_3_and_smaller_source_is_unique():
    """T0 + Lemma U(d) in landing form: in-degree 0 iff 3 | s; from below exactly {x = 1} iff s = 2 (mod 3)."""
    targets = {landing(n)[0] for n in range(1, 200_001, 2)}
    assert all(s % 3 for s in targets)
    for s in range(1, 5001, 2):
        if s % 3 == 0:
            assert not any(admissible(s, x) for x in range(1, 30))
            continue
        below = [x for x in range(1, 30) if admissible(s, x) and source(s, x) < s]
        assert below == ([1] if s % 3 == 2 else [])
        if s % 3 == 2:
            assert source(s, 1) == (2 * s - 1) // 3


def test_leaf_rule_mod_9_by_mod_6():
    """Source dead (3 | n) iff 2^x s = 1 (mod 9) iff x = x0(s mod 9) (mod 6); row recursion y_{x+2} = 4 y_x + 1."""
    for s in range(1, 3000, 2):
        if s % 3 == 0:
            continue
        x0 = X0[s % 9]
        assert pow(2, x0, 9) * s % 9 == 1
        adm = [x for x in range(1, 61) if admissible(s, x)]
        assert adm == list(range(1 if s % 3 == 2 else 2, 61, 2))
        for x in adm:
            n = source(s, x)
            assert (n % 3 == 0) == ((1 << x) * s % 9 == 1) == (x % 6 == x0 % 6)
            if x + 2 in adm:
                assert source(s, x + 2) == 4 * n + 1
        # exactly one dead in every three consecutive admissible heights
        dead = [x for x in adm if (1 << x) * s % 9 == 1]
        for i in range(len(adm) - 2):
            assert sum(1 for x in adm[i:i + 3] if x in dead) == 1
    # first admissible source dead iff s = 5 (x = 1) or 7 (x = 2) mod 9  [x = 1 case is T4]
    for s in range(1, 3000, 2):
        if s % 3 == 0:
            continue
        x = 1 if s % 3 == 2 else 2
        assert (source(s, x) % 3 == 0) == (s % 9 in (5, 7))


def test_dead_source_counts():
    """s < 2000, x <= 30: 667 targets, 15 heights each, 5 dead each (10005 / 3335); 222 first-dead = {5, 7 mod 9}."""
    targets = [s for s in range(1, 2000, 2) if s % 3]
    assert len(targets) == 667
    total = dead = 0
    first_dead = []
    for s in targets:
        adm = [x for x in range(1, 31) if admissible(s, x)]
        d = [x for x in adm if source(s, x) % 3 == 0]
        assert len(adm) == 15 and len(d) == 5
        total += 15
        dead += 5
        if source(s, adm[0]) % 3 == 0:
            first_dead.append(s)
    assert (total, dead) == (10005, 3335)
    assert first_dead[:8] == [5, 7, 23, 25, 41, 43, 59, 61] and len(first_dead) == 222
    assert first_dead == [s for s in targets if s % 9 in (5, 7)]
    # among all odd n < 200 001: 33 333 = floor(100 000 / 3) dead sources
    assert sum(1 for n in range(1, 200_001, 2) if n % 3 == 0) == 33_333


def test_live_backward_chains_exist_at_every_depth():
    """Every s coprime to 3 has a greedy backward chain of length 12 avoiding 3Z; smallest live height <= 4."""
    for s in range(1, 2000, 2):
        if s % 3 == 0:
            continue
        y = s
        for _ in range(12):
            x = 1 if y % 3 == 2 else 2
            while source(y, x) % 3 == 0:
                x += 2
            assert x <= 4
            n = source(y, x)
            assert landing(n) == (y, x) and n % 3
            y = n
    # the example chain of the document
    chain = [5, 13, 17, 11, 7, 37, 49]
    assert all(landing(chain[i + 1])[0] == chain[i] for i in range(len(chain) - 1))


def test_no_size_sieve_saturates_at_density_two_ninths():
    """T0 + T2 without a size bound: 2 * 3^(d-1) classes mod 3^(d+1) = lift of {r = 2 mod 3, r != 5 mod 9}."""
    for d in range(1, 5):
        mod, surv = surviving_residues_mod3_no_size(d, 1)
        assert mod == 3 ** (d + 1) and len(surv) == 2 * 3 ** (d - 1)
        assert set(surv) == {r for r in range(mod) if r % 3 == 2 and r % 9 != 5}


def test_exclusion_tiers_below_100():
    """50 odd -> 33 rows (T0) -> 16 rise-entered (s = 2 mod 3) -> 10 rise from a row (s != 5 mod 9); 5 maximum candidates."""
    odd = list(range(1, 100, 2))
    rows = [s for s in odd if s % 3]
    rise = [s for s in rows if s % 3 == 2]
    rise_from_row = [s for s in rise if s % 9 != 5]
    assert (len(odd), len(rows), len(odd) - len(rows), len(rise), len(rise_from_row)) == (50, 33, 17, 16, 10)
    assert [s for s in rise if s % 9 == 5] == [5, 23, 41, 59, 77, 95]
    assert landing(3) == (5, 1)                                     # 5 is landed on by a rise -- from a dead source
    cand = [M for M in odd if M % 3 == 2 and M % 4 == 1 and M % 9 != 5]
    assert cand == [17, 29, 53, 65, 89]
    assert [M for M in cand if M % 16 != 9] == [17, 29, 53, 65]     # T8 removes 89


def test_what_the_size_bound_adds():
    """Exact-size survivors mod 3^(k+1): 2, 4, 6, 13, 22; magnitude-free a_k: 1, 2, 3, 6, 10, 22, 50, 104, 254, 538."""
    assert [len(surviving_residues_mod3(k, 1)[1]) for k in range(1, 6)] == [2, 4, 6, 13, 22]
    assert surviving_residue_count(10) == [1, 2, 3, 6, 10, 22, 50, 104, 254, 538]
    # heights inside the box M = 10^6 at a few targets: ~ 1/2 log2(3M/s) of the admissible parity
    M = 10**6
    box = {s: len([x for x in range(1, 40) if admissible(s, x) and source(s, x) <= M]) for s in (5, 101, 100_001)}
    assert box == {5: 10, 101: 7, 100_001: 2}
    # at the maximum itself the box is {x = 1} when M = 2 (mod 3) and empty when M = 1 (mod 3) (U(d); T2's kill)
    for M in (5, 17, 29, 53, 101, 1001, 10**6 + 1):
        assert M % 3 == 2
        assert [x for x in range(1, 40) if admissible(M, x) and source(M, x) <= M] == [1]
    for M in (7, 13, 25, 97, 1003, 10**6 + 3):
        assert M % 3 == 1
        assert [x for x in range(1, 40) if admissible(M, x) and source(M, x) <= M] == []


def test_forward_two_adic_sieve_in_landing_form():
    """E2': walking forward from M, 2^{A_j} < 3^j forces the j-th target above M; kills at a = 2 (T1), 4 (T8), 7 only."""
    sizes = []
    for a in range(2, 13):
        mod, surv = surviving_residues_mod2(a)
        assert mod == 1 << a
        sizes.append(len(surv))
        if a == 2:
            assert surv == (1,) and set(range(1, 4, 2)) - set(surv) == {3}          # T1: M = 3 (mod 4) dies
        else:
            pmod, psurv = surviving_residues_mod2(a - 1)
            lifted = {r for r in range(1, mod, 2) if r % pmod in psurv}
            killed = sorted(lifted - set(surv))
            expected = {4: [9], 7: [97, 125], 10: [109, 161, 337, 413, 641, 677, 957]}
            if a <= 11:
                assert killed == expected.get(a, []), a                          # a = 4 is T8
            else:
                assert len(killed) == 30
    assert sizes == [1, 2, 3, 6, 12, 22, 44, 88, 169, 338, 646]
    assert surviving_residues_mod2(3)[1] == (1, 5) and surviving_residues_mod2(4)[1] == (1, 5, 13)
    assert surviving_residues_mod2(5)[1] == (1, 5, 13, 17, 21, 29)
    assert 0.315 < 646 / 2048 < 0.316
    # the kill in landing language: forward heights of M are a function of M mod 2^a, and 2^{A_j} < 3^j => x_j > M
    for M in range(1, 2000, 2):
        n, A = M, 0
        for j in range(1, 6):
            n, x = landing(n)
            A += x
            if (1 << A) < 3**j:
                assert n > M
                break
    # the modulus: the first j heights are a function of M mod 2^{A_j + 1} (v2(3M+1) = x is a condition mod 2^{x+1}),
    # NOT of M mod 2^{A_j}: M and M + t 2^{A_j+1} share them for every t, while M and M + 2^{A_j} already differ at j = 1
    def heights(M, j):
        n, w = M, []
        for _ in range(j):
            n, x = landing(n)
            w.append(x)
        return w
    assert heights(1, 1) == [2] and heights(5, 1) == [4] and 1 % 4 == 5 % 4
    for j in range(1, 5):
        differ_mod_A = 0
        for M in range(1, 5000, 2):
            w = heights(M, j)
            A = sum(w)
            assert all(heights(M + t * (1 << (A + 1)), j) == w for t in range(1, 8))
            differ_mod_A += heights(M + (1 << A), j) != w
        assert differ_mod_A == 2500                                         # every odd M < 5000
    # the kills happen at a = A_j + 1: a = 2, 4, 7, 10, 12 <-> A_j = 1, 3, 6, 9, 11 at j = 1, 2, 4, 6, 7, a = floor(j log2 3) + 1
    assert [floor_bound(j) + 1 for j in (1, 2, 4, 6, 7)] == [2, 4, 7, 10, 12]
    assert [floor_bound(j) + 1 for j in (3, 5)] == [5, 8] and all(floor_bound(j) + 1 != a for j in range(1, 8) for a in (3, 6, 9, 11))


def test_first_source_leaf_rule_on_the_3nq_harness():
    """General q, 2s > q: first admissible positive source is dead iff s = 5q or 7q (mod 9); q = 7, s = 1 is the boundary."""
    for q in (5, 7, 11, 13, 17, 19, 23, 29):
        for s in range(1, 4000, 2):
            if s % 3 == 0 or 2 * s <= q:
                continue
            x = next(x for x in range(1, 40) if admissible(s, x, q))
            assert x in (1, 2)
            assert (source(s, x, q) % 3 == 0) == (s % 9 in (5 * q % 9, 7 * q % 9)), (q, s)
    x = next(x for x in range(1, 40) if admissible(1, x, 7))
    assert x == 4 and source(1, 4, 7) == 3 and 1 % 9 not in (35 % 9, 49 % 9)


# ---------------------------------------------------------------------------
# 3. the height word and the residue automaton = Phi_k
# ---------------------------------------------------------------------------

def step_mod(n: int, x: int, k: int, q: int = 1) -> int:
    """The forward automaton on Z/3^k: n -> 2^{-x} (3n + q)."""
    mod = 3**k
    return pow(2, -x, mod) * (3 * n + q) % mod


def test_one_step_sweep_and_forward_realization_for_k_le_5():
    """A_k = J: 2^{-b}(3r+1) sweeps the units as b runs over Z/(2*3^{k-1}); k-step end state = Phi_k(reversed word), start-free."""
    rng = Random(20260923)
    for k in range(1, 6):
        mod, m = 3**k, 2 * 3 ** (k - 1)
        units = {r for r in range(mod) if r % 3}
        assert pow(2, m, mod) == 1 and all(pow(2, j, mod) != 1 for j in range(1, m))
        for r in range(mod):
            assert {step_mod(r, b, k) for b in range(m)} == units
        # forward realization (H3): all words for k <= 3, 3000 random words for k = 4, 5
        alphabet = range(1, m + 1)
        sample = product(alphabet, repeat=k) if k <= 3 else (tuple(rng.choice(alphabet) for _ in range(k)) for _ in range(3000))
        for w in sample:
            ends = set()
            for start in range(mod):
                n = start
                for x in w:
                    n = step_mod(n, x, k)
                ends.add(n)
            assert ends == {phi(tuple(reversed(w)))}


def test_integers_realize_phi_of_the_reversed_height_word():
    """S^k(n) = Phi_k(x_k, ..., x_1) (mod 3^k) for the first k forward heights of n: 6000 random n < 10^9, k <= 6."""
    rng = Random(1)
    for _ in range(1000):
        n0 = rng.randrange(1, 10**9, 2)
        for k in range(1, 7):
            n, word = n0, []
            for _ in range(k):
                n, x = landing(n)
                word.append(x)
            assert n % 3**k == phi(tuple(reversed(word)))


def test_survivor_sets_are_the_image_of_phi_and_the_counts():
    """image(Phi_k) over admissible k-words == S_k for k <= 6; a_k = 1,2,3,6,10,22; N_k = 1,2,3,7,12,30."""
    levels = surviving_residues(6)
    assert [len(l) for l in levels] == [1, 2, 3, 6, 10, 22]
    assert n_words(6) == [1, 2, 3, 7, 12, 30]
    for k in range(1, 7):
        ws = list(words(k))
        assert len(ws) == n_words(6)[k - 1]
        assert {phi(w) for w in ws} == set(levels[k - 1])
        assert all(phi(w) % 3 for w in ws)


def test_every_height_word_has_exactly_one_closed_walk_per_level():
    """Fixed point of the L-step map mod 3^k is unique, = c/(2^B - 3^L) mod 3^k, = Phi_k(b^inf|_k), b = reversed x."""
    for k in range(1, 5):
        mod = 3**k
        for L in range(1, 4):
            for x in product(range(1, 5), repeat=L):
                closers = []
                for start in range(mod):
                    n = start
                    for xi in x:
                        n = step_mod(n, xi, k)
                    if n == start:
                        closers.append(start)
                b = tuple(reversed(x))
                B, c = sum(b), c_constant(b)
                assert len(closers) == 1 and closers[0] % 3
                assert closers[0] == c * pow((1 << B) - 3**L, -1, mod) % mod
                periodic = tuple(b[i % L] for i in range(k))
                assert closers[0] == phi(periodic)
    # the negative examples of the document, as forward words x: n0 = c/(2^B - 3^L), c = sum 3^{L-i} 2^{X_{i-1}}
    def periodic_point(x):
        L, B = len(x), sum(x)
        c = sum(3 ** (L - i) * (1 << sum(x[: i - 1])) for i in range(1, L + 1))
        return Fraction(c, (1 << B) - 3**L)
    assert periodic_point((1,)) == -1 and periodic_point((1, 2)) == -5 and periodic_point((2, 1)) == -7
    assert periodic_point((1, 1, 1, 2, 1, 1, 4)) == -17 and sum((1, 1, 1, 2, 1, 1, 4)) == 11
    assert periodic_point((1, 1, 1, 2)).denominator != 1                # the draft's (1,1,1,2) is not an integer cycle
    n, cyc = -17, []
    for _ in range(7):
        cyc.append(n)
        n = landing(n)[0]
    assert n == -17 and cyc == [-17, -25, -37, -55, -41, -61, -91]


def test_trivial_cycle_and_the_immortal_negative_words():
    """(2) closes on 1; (1,2)^inf is admissible at every depth (floor superadditive); -7, -1 in S_k, -5 not (k <= 12);
    -91 is the unique immortal phase of the negative 7-cycle; S_k = {r(b) mod 3^k : b admissible, |b| >= k}, k <= 6."""
    assert phi((2,)) == 1 and Fraction(c_constant((2,)), 4 - 3) == 1
    for t in range(1, 400):
        assert floor_bound(t) >= (3 * t) // 2                        # caps of (1,2)^inf: B_t = floor(3t/2)
    assert Fraction(c_constant((1, 2)), (1 << 3) - 9) == -7
    assert Fraction(c_constant((1,)), 2 - 3) == -1
    K = 12
    levels = surviving_residues(K)
    for k in range(1, K + 1):
        S_k = set(levels[k - 1])
        assert (-7) % 3**k in S_k and (-1) % 3**k in S_k
        assert (-5) % 3**k not in S_k

    def r(b):
        return Fraction(c_constant(b), (1 << sum(b)) - 3 ** len(b))

    def cap_admissible(b):
        return all(sum(b[:t]) <= floor_bound(t) for t in range(1, len(b) + 1))

    def survives_to(n):
        return max((k for k in range(1, K + 1) if n % 3**k in set(levels[k - 1])), default=0)

    # the negative 7-cycle: backward word of each phase (heights into the phase, then into its predecessor, ...)
    cyc = [-17, -25, -37, -55, -41, -61, -91]
    heights_into = {cyc[(i + 1) % 7]: landing(cyc[i])[1] for i in range(7)}
    immortal = []
    for i, p in enumerate(cyc):
        b = tuple(heights_into[cyc[(i - j) % 7]] for j in range(7))
        assert r(b) == p
        if cap_admissible(b):
            immortal.append((p, b))
            assert survives_to(p) == K
        else:
            assert survives_to(p) < K
    assert immortal == [(-91, (1, 1, 2, 1, 1, 1, 4))]
    assert survives_to(-61) == 8 and survives_to(-17) == 0
    # the death depth of every phase (survives_to + 1): -17, -25, -37, -55, -41, -61 die at 1, 3, 6, 7, 1, 9; -91 never
    assert {p: survives_to(p) for p in cyc} == {-17: 0, -25: 2, -37: 5, -55: 6, -41: 0, -61: 8, -91: 12}
    assert survives_to(-5) == 0 and survives_to(-7) == K and survives_to(-1) == K
    # S_k is exactly the set of r(b) mod 3^k over admissible words of length >= k (checked for |b| <= k + 2)
    for k in range(1, 7):
        image = set()
        for m in range(k, k + 3):
            for b in words(m):
                x = r(b)
                assert x < 0 and x.denominator % 2 == 1
                image.add(x.numerator * pow(x.denominator, -1, 3**k) % 3**k)
        assert image == set(levels[k - 1])
    # a positive cycle's own word is over the cap at depth L (T7 forces B_L >= f(L) + 1): the caps never close on it
    assert sum((2,)) == floor_bound(1) + 1
    # ... but S_k is a residue set and cycle maxima do lie in it (harness, S_k(q) = q S_k(1)): the q = 5 cycle
    # (49, 19, 31), B = 5 > f(3) = 4, has 49 in S_k(5) for k <= 7 and dies at k = 8; the q = 7 cycle (11, 5),
    # B = 4 > f(2) = 3, survives to k = 4.  For q = 1 every nontrivial M = 2 (mod 3) is in S_1 = {2}.
    assert levels[0] == [2]
    for q, M, cyc, B, depth in ((5, 49, (49, 19, 31), 5, 7), (7, 11, (11, 5), 4, 4)):
        n = M
        for p in cyc:
            assert n == p
            n = landing(n, q)[0]
        assert n == M and B == sum(landing(p, q)[1] for p in cyc) > floor_bound(len(cyc))
        lv = surviving_residues(9, q)
        assert lv[0] == [2 * q % 3]                                        # S_1(q) = q S_1(1) = {2q mod 3}
        lv1 = surviving_residues(9, 1)
        assert all(set(lv[k - 1]) == {q * r % 3**k for r in lv1[k - 1]} for k in range(1, 10))  # S_k(q) = q S_k(1)
        assert [k for k in range(1, 10) if M % 3**k in set(lv[k - 1])] == list(range(1, depth + 1))


def test_mod_3_share_of_cycle_members(census):
    """#members = -q (mod 3) = #odd heights >= u >= 2L - B on every census cycle; 12825 is the sharp q = 1 threshold."""
    for c in census:
        q = c.q
        odd_heights = sum(1 for x in c.forward_halvings if x % 2)
        u = sum(1 for x in c.forward_halvings if x == 1)
        assert sum(1 for n in c.elements if n % 3 == (-q) % 3) == odd_heights >= u >= 2 * c.L - c.B, c
        assert not any(n % 3 == 0 for n in c.elements)
    cert = lambda m: (3 * m + 1) ** 200 <= 2**317 * m**200
    assert not cert(12824) and cert(12825)


# ---------------------------------------------------------------------------
# 4. the page (web/landing.html) geometry
# ---------------------------------------------------------------------------

def test_landing_table_geometry_and_in_degrees():
    """s <= 65, x <= 10: 22 rows, 110 admissible, 36 dead, max source 20821; default 47/8: 16, 64, 22, 3669."""
    def geometry(S: int, X: int) -> tuple[int, int, int, int]:
        rows = [s for s in range(1, S + 1, 2) if s % 3]
        cells = [(s, x) for s in rows for x in range(1, X + 1) if admissible(s, x)]
        dead = [c for c in cells if source(*c) % 3 == 0]
        return len(rows), len(cells), len(dead), max(source(*c) for c in cells)
    assert geometry(65, 10) == (22, 110, 36, 20821)
    assert geometry(47, 8) == (16, 64, 22, 3669)
    indeg: dict[int, int] = {}
    for n in range(1, 1 << 20, 2):
        s = landing(n)[0]
        indeg[s] = indeg.get(s, 0) + 1
    assert [indeg[s] for s in (1, 5, 7, 11, 13, 17)] == [10, 10, 9, 9, 8, 9]
    assert all(s in indeg for s in range(1, 2000, 2) if s % 3)
    assert min(s for s in range(1, 1 << 21, 2) if s % 3 and s not in indeg) == 786_433 == 3 * 2**18 + 1
    for s in (1, 5, 7, 11, 13, 17):                                  # closed form: Lemma U(c)
        assert indeg[s] == sum(1 for x in range(1, 40) if admissible(s, x) and source(s, x) < 1 << 20)
