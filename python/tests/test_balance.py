"""Witnesses for docs/BALANCE.md: loops near perfect balance, via norms in Q(2^(1/L)).

q = 1 throughout; the 3n+q census appears only as a harness (filter test A and the spread
lemma).
"""

from __future__ import annotations

import math
import random
from collections import deque
from itertools import combinations
from math import gcd

from collatz_maxodd.balance import (
    ELLISON_BASE,
    LOG2_3,
    PARSEVAL_RATE,
    RHIN_FROM,
    christoffel,
    corner_level,
    cycle_numerator,
    flatten,
    level_sum_mod_d,
    move_word,
    norm_exact,
    norm_test,
    odd_part,
    one_swaps,
    parseval_log_bound,
    parseval_mass,
    rhin_log_d,
    spread_threshold,
    swap_element,
    theta0,
    two_swap_direct,
    two_swap_element,
    two_swap_log_norm_bound,
    two_swap_loops,
    two_swap_mass_bounds,
    two_swaps,
    word_element,
)
from collatz_maxodd.syracuse import syracuse_with_exponent


def coprime_pairs(L_max: int, L_min: int = 2):
    for L in range(L_min, L_max + 1):
        for B in range(math.floor(L * LOG2_3) + 1, 2 * L):
            if gcd(L, B) == 1:
                yield L, B


def unit_factor(L: int, B: int, d: int, t: int) -> int:
    """(theta - 1) theta^(L-1) theta^(-B(L-1)) mod d: maps c(w) to A(w) (theta - 1) theta^(L-1)."""
    return (t - 1) * pow(t, L - 1, d) * pow(pow(t, B * (L - 1), d), -1, d) % d


# ---------------------------------------------------------------------------
# section 1: the reformulation
# ---------------------------------------------------------------------------


def test_theta0_is_a_root_of_both_equations() -> None:
    for L, B in coprime_pairs(60):
        d = 2**B - 3**L
        t = theta0(L, B)
        assert pow(t, L, d) == 2 % d and pow(t, B, d) == 3 % d


def test_theta_identity_on_random_words() -> None:
    rng = random.Random(3)
    n = 0
    for L, B in coprime_pairs(30):
        d = 2**B - 3**L
        t = theta0(L, B)
        for _ in range(10):
            cuts = sorted(rng.sample(range(1, B), L - 1))
            w = [b - a for a, b in zip([0] + cuts, cuts + [B])]
            X, A = 0, 0
            for i, x in enumerate(w):
                D = i * B - L * X
                A += pow(t, -D, d)  # Python's pow inverts modulo d for negative exponents
                X += x
            assert cycle_numerator(w) % d == pow(t, B * (L - 1), d) * A % d
            n += 1
    assert n > 1000


def test_norm_divisibility_holds_on_real_cycles(census) -> None:
    # soundness of the whole reformulation on loops that exist: a 3n+q cycle with coprime
    # (L, B) has d | q c(w), hence q P_w(theta) in (theta^B - 3), hence d | q^L N(P_w)
    checked = 0
    for c in census:
        L = c.L
        w = tuple(syracuse_with_exponent(n, c.q)[1] for n in c.elements)
        B = sum(w)
        if L < 2 or L > 30 or gcd(L, B) != 1 or 2**B < 3**L:
            continue
        d = 2**B - 3**L
        assert c.q * cycle_numerator(w) % d == 0
        assert c.q**L * norm_exact(word_element(w), L) % d == 0
        checked += 1
    assert checked == 709
    assert cycle_numerator((2,)) % (2**2 - 3) == 0 and not norm_test((2,))


# ---------------------------------------------------------------------------
# section 2: balanced words (Knight) and the spread lemma
# ---------------------------------------------------------------------------


def test_balanced_numerator_is_a_unit_and_coprime_to_d() -> None:
    for L, B in coprime_pairs(160):
        d = 2**B - 3**L
        c = cycle_numerator(christoffel(L, B))
        assert gcd(c, d) == 1
        if L <= 60:
            t = theta0(L, B)
            assert unit_factor(L, B, d, t) * c % d == 1 % d
            assert abs(norm_exact(word_element(christoffel(L, B)), L)) == 1  # P_w = 1 + theta + ... + theta^(L-1) = 1/(theta - 1)


def test_balanced_integral_only_when_d_is_one() -> None:
    hits = [(L, B) for L, B in coprime_pairs(80, 2) if cycle_numerator(christoffel(L, B)) % (2**B - 3**L) == 0]
    assert hits == []
    assert cycle_numerator(christoffel(1, 2)) % (2**2 - 3) == 0  # the trivial loop {1}


def test_spread_threshold() -> None:
    assert abs(spread_threshold() - 1.861456327711861) < 1e-12


def _is_balanced(w: tuple[int, ...]) -> bool:
    L = len(w)
    for ell in range(1, L):
        sums = {sum(w[(i + j) % L] for j in range(ell)) for i in range(L)}
        if max(sums) - min(sums) > 1:
            return False
    return True


def test_small_spread_forces_balance_on_the_census(census) -> None:
    # for a 3n+q cycle: windows of equal length differ by < 2 log2(M/m) + L log2(1 + q/(3m));
    # when that is < 2 the halving word must be balanced (every census cycle obeys this)
    checked = 0
    for c in census:
        if c.L < 2:
            continue
        m, M = min(c.elements), c.M
        if 2 * math.log2(M / m) + c.L * math.log2(1 + c.q / (3 * m)) < 2:
            w = tuple(syracuse_with_exponent(n, c.q)[1] for n in c.elements)
            assert _is_balanced(w)
            checked += 1
    assert checked > 0


# ---------------------------------------------------------------------------
# section 3: one swap from balance
# ---------------------------------------------------------------------------


def test_swap_kinds_ranges_and_reduction() -> None:
    n = 0
    for L, B in coprime_pairs(40, 3):
        d = 2**B - 3**L
        t = theta0(L, B)
        b = B - L
        u = unit_factor(L, B, d, t)
        for _, kind, p, v in one_swaps(L, B):
            g = sum(c * pow(t, m, d) for m, c in swap_element(kind, p).items()) % d
            if kind == "12->21":
                assert 0 <= p <= L - 1 - b and u * cycle_numerator(v) % d == g
            else:
                assert 2 <= p <= L - b and u * cycle_numerator(v) * pow(t, p, d) % d == g
            n += 1
    assert n == 2059


def test_parseval_bound() -> None:
    for L, B in coprime_pairs(45, 3):
        for _, kind, p, _ in one_swaps(L, B):
            el = swap_element(kind, p)
            bound = parseval_log_bound(el, L)
            assert bound <= L * PARSEVAL_RATE + 1e-9
            assert math.log(abs(norm_exact(el, L))) <= bound + 1e-9


def test_small_lengths_directly() -> None:
    n = 0
    for L, B in coprime_pairs(17, 3):
        d = 2**B - 3**L
        for _, _, _, v in one_swaps(L, B):
            assert cycle_numerator(v) % d != 0
            n += 1
    assert n == 159


def test_ellison_inequality_exactly_and_the_margin() -> None:
    assert math.sqrt(41 / 9) < ELLISON_BASE
    # the cited bound 2^B - 3^L > 2.56^L (Knight, Lemma 3.3), checked exactly for B = f(L)+1
    for L in range(18, 1500):
        B = math.floor(L * LOG2_3) + 1
        assert (2**B - 3**L) * 100**L > 256**L  # d > 2.56^L, exactly


def test_exact_norm_test_on_all_one_swap_words() -> None:
    tot = ok = 0
    for L, B in coprime_pairs(45, 3):
        d = 2**B - 3**L
        for _, kind, p, _ in one_swaps(L, B):
            n = odd_part(norm_exact(swap_element(kind, p), L))
            tot += 1
            ok += 0 < n < d
    assert ok == tot == 3034


# ---------------------------------------------------------------------------
# section 4: two swaps from balance (Theorem 2)
# ---------------------------------------------------------------------------


def _moves(L: int, B: int, p1: int, s1: int, p2: int, s2: int):
    return ((corner_level(L, B, p1), s1), (corner_level(L, B, p2), s2))


def _rl_params(L: int, B: int, p1: int, s1: int, p2: int, s2: int) -> tuple[int, int]:
    (D1, _), (D2, _) = _moves(L, B, p1, s1, p2, s2)
    Dr, Dl = (D1, D2) if s1 == 1 else (D2, D1)
    return L - 1 - Dr, Dl + 1


def test_two_swap_congruences() -> None:
    """Lemma 8: q(theta0) = theta0^(K+L-1) (theta0 - 1) S and c(w) = theta0^(B(L-1)) u S mod d,
    S the level sum of the moved staircase, u = 2^(-s) if corner 0 moved with sign s, else 1."""
    n = 0
    for L, B in coprime_pairs(24, 3):
        d, Z, A = level_sum_mod_d(L, B)
        t, half = theta0(L, B), (d + 1) // 2
        for p1, s1, p2, s2, w in two_swaps(L, B):
            mv = _moves(L, B, p1, s1, p2, s2)
            S = (A + sum(Z[D] if sg == 1 else -Z[D] * half for D, sg in mv)) % d
            ks = [D + 1 for D, sg in mv if sg == -1]
            _, q = two_swap_element(L, B, p1, s1, p2, s2)
            assert max(q) < L
            qv = sum(c * pow(t, m, d) for m, c in q.items()) % d
            assert qv == pow(t, max(ks, default=0) + L - 1, d) * (t - 1) * S % d
            u = 1 if p1 != 0 else (half if s1 == 1 else 2)
            assert cycle_numerator(w) % d == pow(t, B * (L - 1), d) * u * S % d
            n += 1
    assert n == 2438


def _classes_within(L: int, B: int, depth: int) -> dict[tuple[int, ...], int]:
    """Cyclic classes within ``depth`` actual swaps of the balanced word, with their distance."""
    start = _canon(christoffel(L, B))
    dist = {start: 0}
    frontier = [start]
    for k in range(1, depth + 1):
        nxt = []
        for w in frontier:
            for i in range(L):
                j = (i + 1) % L
                if w[i] != w[j]:
                    v = list(w)
                    v[i], v[j] = v[j], v[i]
                    c = _canon(tuple(v))
                    if c not in dist:
                        dist[c] = k
                        nxt.append(c)
        frontier = nxt
    return dist


def test_two_swap_words_are_the_distance_two_classes() -> None:
    """Moving two corners of the lower Christoffel word gives exactly the cyclic words at swap
    distance 2 (plus some at distance 0 or 1), for every coprime pair with L <= 40.  The
    distances come from a breadth-first search over actual cyclic swaps."""
    n2 = 0
    for L, B in coprime_pairs(40, 3):
        dist = _classes_within(L, B, 2)
        got = {_canon(w) for *_, w in two_swaps(L, B)}
        two = {c for c, k in dist.items() if k == 2}
        assert got <= set(dist) and got - {c for c, k in dist.items() if k < 2} == two
        if (L, B) in ((13, 21), (18, 29)):
            assert len(two) == {13: 18, 18: 51}[L]
        n2 += len(two)
    assert n2 == 12289


def test_two_swap_corner_types() -> None:
    """Lemma 7: raised corners are 12 corners and lowered ones 21 corners, except that adjacent
    raises use a 12 then a 22 corner and adjacent lowers a 22 then a 21 corner; a raise next to a
    lower is impossible.  Exponent ranges as in Lemma 8."""
    for L, B in coprime_pairs(60, 6):
        b = B - L
        a, s = L - b, 2 * b - L

        def kind(D: int) -> str:
            return "21" if D < a else ("12" if D >= b else "22")

        for p1, s1, p2, s2, _ in two_swaps(L, B):
            fam, q = two_swap_element(L, B, p1, s1, p2, s2)
            (D1, _), (D2, _) = _moves(L, B, p1, s1, p2, s2)
            if fam in ("RR", "LL", "RL"):
                for D, sg in ((D1, s1), (D2, s2)):
                    assert kind(D) == ("12" if sg == 1 else "21")
            else:
                assert fam in ("RRadj", "LLadj")
                first, second = (D1, D2) if (p2 - p1) % L == 1 else (D2, D1)
                want = ("12", "22") if fam == "RRadj" else ("22", "21")
                assert (kind(first), kind(second)) == want
            top = {"RR": a, "LL": a, "RL": 2 * a, "RRadj": min(2 * a, b), "LLadj": max(a + 1, min(b, 2 * a))}
            assert max(q) <= top[fam]


def test_two_swap_mass_bounds() -> None:
    """Lemma 9 on every two-corner move with 6 <= L <= 60: the Parseval mass of q (of
    flatten(q) for raise-lower moves with k >= 2, e >= 1) is at most the family bound."""
    n = 0
    for L, B in coprime_pairs(60, 6):
        mb = two_swap_mass_bounds(L, B)
        for p1, s1, p2, s2, _ in two_swaps(L, B):
            fam, q = two_swap_element(L, B, p1, s1, p2, s2)
            if fam == "RL":
                e, k = _rl_params(L, B, p1, s1, p2, s2)
                fam, q = ("RLflat", flatten(q)) if (e >= 1 and k >= 2) else ("RL0", q)
            assert parseval_mass(q, L) <= mb[fam] * (1 + 1e-12)
            n += 1
    assert n == 93417


def test_two_swap_parseval_against_exact_norms() -> None:
    """Exact norms (Bareiss) of the element of every two-corner move with 6 <= L <= 22: below the Parseval
    bound, odd when the constant term is odd, and below d -- at most 0.216 d, at (17, 27) --
    so the norm test alone settles them."""
    n, worst = 0, 0.0
    for L, B in coprime_pairs(22, 6):
        d = 2**B - 3**L
        bound = two_swap_log_norm_bound(L, B)
        for p1, s1, p2, s2, _ in two_swaps(L, B):
            _, q = two_swap_element(L, B, p1, s1, p2, s2)
            N = abs(norm_exact(q, L))
            if q.get(0, 0) % 2:
                assert N % 2 == 1
            assert 0 < N and math.log(N) <= bound + 1e-9
            worst = max(worst, odd_part(N) / d)
            n += 1
    assert n == 1722 and 0.215 < worst < 0.216


def test_two_swap_direct_agrees_with_brute_force() -> None:
    """The O(L) level-sum check finds no two-swap loop, matching d | c(w) word by word; its few
    solutions (6 for L <= 30) all leave the alphabet {1, 2}."""
    extra = 0
    for L, B in coprime_pairs(30, 3):
        d = 2**B - 3**L
        assert [w for *_, w in two_swaps(L, B) if cycle_numerator(w) % d == 0] == []
        sols = two_swap_direct(L, B)
        assert all(move_word(L, B, [(D1, s1), (D2, s2)]) is None for D1, s1, D2, s2 in sols)
        assert two_swap_loops(L, B) == []
        extra += len(sols)
    assert extra == 6


def test_three_swap_norm_can_exceed_d() -> None:
    """Why the size argument stops at two swaps.  At (233, 370), lowering the corner at level 95
    and raising those at levels 141 and 187 gives a word of 1s and 2s whose element
    1 - theta + theta^96 - theta^141 + theta^142 - theta^187 + theta^188 has an odd norm of
    about 11.33 d.  The word is not a loop: d does not divide the norm."""
    L, B = 233, 370
    d = 2**B - 3**L
    k, e1, e2 = 96, 91, 45
    moves = [(k - 1, -1), (L - 1 - e1, 1), (L - 1 - e2, 1)]
    w = move_word(L, B, moves)
    assert w is not None and set(w) == {1, 2} and sum(w) == B
    q = {0: 1, 1: -1, k: 1, k + e2: -1, k + e2 + 1: 1, k + e1: -1, k + e1 + 1: 1}
    _, Z, A = level_sum_mod_d(L, B)
    t, half = theta0(L, B), (d + 1) // 2
    S = (A + sum(Z[D] if sg == 1 else -Z[D] * half for D, sg in moves)) % d
    assert sum(c * pow(t, m, d) for m, c in q.items()) % d == pow(t, k + L - 1, d) * (t - 1) * S % d
    assert cycle_numerator(w) % d == pow(t, B * (L - 1), d) * S % d != 0
    N = abs(norm_exact(q, L))
    assert N % 2 == 1 and N // d == 11 and N % d != 0


SETTLED_DIRECTLY = [
    (3, 5), (4, 7), (5, 8), (8, 13), (11, 18), (13, 21), (14, 23), (17, 27), (18, 29), (22, 35),
    (27, 43), (29, 46), (32, 51), (39, 62), (41, 65), (46, 73), (63, 100), (70, 111), (94, 149),
    (147, 233),
]


def test_theorem2_finite_range() -> None:
    """Theorem 2, finite part: every coprime (L, B) with L < 100, and B = floor(L log2 3) + 1 for
    100 <= L < 4000, is settled by the norm bound (d > the Parseval bound, margin >= 0.079 in
    log) or, for the 20 listed pairs, by the direct check."""
    direct, margin, n = [], math.inf, 0
    for L in range(3, RHIN_FROM):
        Bmin = math.floor(L * LOG2_3) + 1
        for B in range(Bmin, 2 * L if L < 100 else Bmin + 1):
            if gcd(L, B) != 1:
                continue
            n += 1
            gap = math.log(2**B - 3**L) - two_swap_log_norm_bound(L, B)
            if gap > 0:
                margin = min(margin, gap)
            else:
                assert two_swap_loops(L, B) == []
                direct.append((L, B))
    assert n == 3622 and direct == SETTLED_DIRECTLY and margin > 0.079


def test_theorem2_analytic_ranges() -> None:
    """Theorem 2, infinite part.  (a) B >= floor(L log2 3) + 2: with beta = b/L, every family
    bound is at most 4^(2/L) G(beta) with G(beta) / 4^(1+beta) <= 0.94034, below
    4^(-3/L) (1 - 2^(1-L))^(2/L) for L >= 100, so |N(q)| < 2^(B-1) < d.  (b) B = floor(L log2 3)
    + 1, L >= 4000: Rhin's bound Lambda >= B^(-13.3) beats 4 (8.46296)^(L/2) / (1 - 2^(1-L))."""
    b0 = LOG2_3 - 1

    def G(be: float) -> dict[str, float]:
        mu = min(1 - be, 2 * be - 1)
        return {
            "RR": 1 + 4 * 4 ** (1 - be),
            "RRadj": 1 + 2 * 4**mu + 2 * 4 ** (mu + 1 - be),
            "LL": 2 + 3 * 4 ** (1 - be),
            "LLadj": 2 + 4 ** min(be, 2 - 2 * be) + 2 * 4 ** (1 - be),
            "RL0": 2 + 2 * 4 ** (1 - be),
            "RLflat": 1.5 + 1.25 * 4 ** (1 - be) + 1.5 * 4 ** (2 - 2 * be),
        }

    sup = max(max(G(b0 + (1 - b0) * i / 20000).values()) / 4 ** (1 + b0 + (1 - b0) * i / 20000) for i in range(20001))
    assert abs(sup - 0.940329) < 1e-6
    assert sup < 4 ** (-3 / 100) * (1 - 2.0**-99) ** (2 / 100)
    # the family bounds of the module really are below 4^(2/L) G(beta)
    for L, B in coprime_pairs(400, 100):
        mb, g = two_swap_mass_bounds(L, B), G((B - L) / L)
        assert all(mb[k] <= 4 ** (2 / L) * g[k] * (1 + 1e-12) for k in g)
    # (b) at B = Bmin the largest G is the raise-lower one, 8.46296 at beta0, decreasing in beta
    Gmax = G(b0)["RLflat"]
    assert abs(Gmax - 8.462963) < 1e-6 and max(G(b0 + 1 / 4000).values()) <= Gmax
    assert 8.11 < sorted(G(b0).values())[-2] < 8.12  # the runner-up is the two-raise family

    def sigma(L: int) -> float:  # slack with log B replaced by its smooth majorant log(L log2 3 + 1)
        return 0.5 * L * math.log(9 / Gmax) - math.log(4 / (1 - 2.0 ** (1 - L))) - 13.3 * math.log(L * LOG2_3 + 1)

    def slack(L: int) -> float:  # the same with log B itself
        return 0.5 * L * math.log(9 / Gmax) - math.log(4 / (1 - 2.0 ** (1 - L))) - 13.3 * math.log(math.floor(L * LOG2_3) + 1)

    assert 5.2 < sigma(RHIN_FROM) < slack(RHIN_FROM) < 5.3
    assert slack(3808) < 0 < slack(3809) and all(slack(L) > 0 for L in range(3809, 20000))
    # sigma' > (1/2) log(9/Gmax) - 13.3/L > 0 once L > 2*13.3/log(9/Gmax) = 432.4
    assert 432 < 2 * 13.3 / math.log(9 / Gmax) < 433
    assert all(sigma(L + 1) > sigma(L) for L in range(433, 6000))
    # the form exp(-13.3(0.46057 + log L)) is not implied by Rhin's H^(-13.3): 0.46057 is rounded up
    assert math.exp(0.46057) > LOG2_3
    for L in range(RHIN_FROM, RHIN_FROM + 2000):
        B = math.floor(L * LOG2_3) + 1
        if gcd(L, B) == 1:
            assert rhin_log_d(L, B) > two_swap_log_norm_bound(L, B)


# ---------------------------------------------------------------------------
# section 5: reach of the norm test, by swap distance from balance
# ---------------------------------------------------------------------------


def _canon(w: tuple[int, ...]) -> tuple[int, ...]:
    return min(w[i:] + w[:i] for i in range(len(w)))


def _primitive(w: tuple[int, ...]) -> bool:
    L = len(w)
    return all(w != w[i:] + w[:i] for i in range(1, L) if L % i == 0)


def reach_profile(L: int, B: int) -> dict[int, tuple[int, int]]:
    b = B - L
    classes = set()
    for pos in combinations(range(L), b):
        w = [1] * L
        for p in pos:
            w[p] = 2
        c = _canon(tuple(w))
        if _primitive(c):
            classes.add(c)
    start = _canon(christoffel(L, B))
    dist = {start: 0}
    dq = deque([start])
    while dq:
        w = dq.popleft()
        for i in range(L):
            j = (i + 1) % L
            if w[i] != w[j]:
                v = list(w)
                v[i], v[j] = v[j], v[i]
                c = _canon(tuple(v))
                if c in classes and c not in dist:
                    dist[c] = dist[w] + 1
                    dq.append(c)
    prof: dict[int, tuple[int, int]] = {}
    for w, k in dist.items():
        tot, ok = prof.get(k, (0, 0))
        prof[k] = (tot + 1, ok + norm_test(w))
    return prof


def test_reach_profiles() -> None:
    p13 = reach_profile(13, 21)
    assert {k: (ok, tot) for k, (tot, ok) in p13.items()} == {
        0: (1, 1), 1: (7, 7), 2: (18, 18), 3: (22, 22), 4: (19, 20), 5: (13, 14), 6: (7, 9), 7: (1, 5), 8: (0, 2), 9: (0, 1)}
    p18 = reach_profile(18, 29)
    assert [p18[k][1] for k in range(4)] == [1, 11, 51, 128] and [p18[k][0] for k in range(4)] == [1, 11, 51, 129]
    assert sum(ok for _, ok in p18.values()) == 970 and sum(t for t, _ in p18.values()) == 1768


# ---------------------------------------------------------------------------
# filter test A: the theorem is about q = 1, and 3n+13 really has a one-swap loop
# ---------------------------------------------------------------------------


def test_q13_has_balanced_and_one_swap_loops() -> None:
    # 2^8 - 3^5 = 13, so for 3n+13 every word with L = 5, B = 8 closes; two of them:
    for word, members in (((1, 2, 1, 2, 2), [319, 485, 367, 557, 421]), ((1, 1, 2, 2, 2), [283, 431, 653, 493, 373])):
        n = members[0]
        seen = []
        for x in word:
            nxt, e = syracuse_with_exponent(n, 13)
            assert e == x
            seen.append(n)
            n = nxt
        assert n == members[0] and seen == members
    assert (1, 1, 2, 2, 2) in [_canon(v) for _, _, _, v in one_swaps(5, 8)]
