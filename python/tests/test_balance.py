"""Witnesses for docs/BALANCE.md: loops near perfect balance, via norms in Q(2^(1/L)).

q = 1 throughout; the 3n+q census appears only as a harness (filter test A and the spread
lemma).
"""

from __future__ import annotations

import math
import random
from fractions import Fraction
from collections import deque
from itertools import combinations, product
from math import gcd

from collatz_maxodd.balance import (
    ELLISON_BASE,
    LOG2_3,
    PARSEVAL_RATE,
    RHIN_FROM,
    admissible_rotations,
    balanced_word,
    christoffel,
    corner_level,
    cycle_numerator,
    displacement,
    flatten,
    generalized_levels,
    height_spread,
    level_sum_mod_d,
    longest_repeat,
    mass_criterion,
    max_moved_corners,
    move_word,
    moved_corner_reach,
    moved_corner_window,
    norm_exact,
    norm_test,
    normalize,
    odd_part,
    one_swaps,
    parseval_log_bound,
    parseval_mass,
    profile_element,
    profile_word,
    repeat_at_length,
    repeat_excludes,
    rhin_log_d,
    run_element,
    run_is_valid,
    run_log_norm_bound,
    run_word,
    size_exponent,
    size_exponent_bound,
    smallest_B,
    spread_threshold,
    swap_span,
    swap_element,
    theta0,
    two_swap_direct,
    two_swap_element,
    two_swap_log_norm_bound,
    two_swap_loops,
    two_swap_mass_bounds,
    two_swaps,
    window_suffices,
    word_element,
    heaviest_repeat,
    heights,
    least_size_exponent,
    local_repeat,
    low_stretch_length,
    low_stretch_window,
    max_lowered_corners,
    touching_stretch,
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
# section 5: one run of levels (Theorem 3)
# ---------------------------------------------------------------------------


def test_profile_formula_on_random_words() -> None:
    """Lemma 10 on words with arbitrary positive letters.  The normalized rotation has a
    non-negative profile, and its profile element equals (theta - 1) theta^(L-1) A(w), both
    modulo d and at the real embedding.  It is a unit times c(w) modulo d, so the two have the
    same gcd with d (non-trivial on 303 of the 4 600 words)."""
    rng = random.Random(3)
    n = shared = 0
    for L, B in coprime_pairs(30, 3):
        d = 2**B - 3**L
        t, th = theta0(L, B), 2 ** (1 / L)
        for _ in range(40):
            cuts = sorted(rng.sample(range(1, B), L - 1))
            w = tuple(hi - lo for lo, hi in zip([0, *cuts], [*cuts, B]))
            v = normalize(w)
            m = displacement(v)
            assert min(m) >= 0 and m[0] == 0 and _canon(v) == _canon(w)
            q = profile_element(m)
            assert max(q) < L
            X, a_mod, a_real = 0, 0, 0.0
            for i, x in enumerate(v):
                D = i * B - L * X
                a_mod = (a_mod + pow(t, -D, d)) % d
                a_real += th ** (-D)
                X += x
            q_mod = sum(c * pow(t, j, d) for j, c in q.items()) % d
            assert q_mod == (t - 1) * pow(t, L - 1, d) * a_mod % d
            assert abs(sum(c * th**j for j, c in q.items()) - (th - 1) * th ** (L - 1) * a_real) < 1e-9 * max(1.0, a_real)
            assert gcd(q_mod, d) == gcd(cycle_numerator(v), d)
            shared += gcd(q_mod, d) > 1
            n += 1
    assert (n, shared) == (4600, 303)


def test_mass_criterion_on_all_small_words() -> None:
    """Corollary 11 on every word with positive letters and L <= 10 (85 358 words, 8 947 cyclic
    classes).  None has d | c(w), so soundness is tested through its mechanism instead:
    h = gcd(c(w), d) divides N(q) and is at most M^(L/2), for every rotation with a
    non-negative profile (5 917 words have h > 1).  Those rotations are exactly the ones
    ``admissible_rotations`` lists.  The criterion gives one verdict per cyclic class and
    settles 562 classes (5 047 words)."""
    tot = shared = fired = 0
    verdicts: dict[tuple[int, int, tuple[int, ...]], set[bool]] = {}
    for L, B in coprime_pairs(10, 3):
        d = 2**B - 3**L
        for cuts in combinations(range(1, B), L - 1):
            w = tuple(hi - lo for lo, hi in zip((0, *cuts), (*cuts, B)))
            tot += 1
            c = cycle_numerator(w)
            assert c % d != 0
            adm = admissible_rotations(w)
            assert normalize(w) in adm
            assert adm == [v for v in (w[r:] + w[:r] for r in range(L)) if min(displacement(v)) >= 0]
            h = gcd(c, d)
            if h > 1:
                shared += 1
                assert norm_exact(profile_element(displacement(normalize(w))), L) % h == 0
                for v in adm:
                    assert math.log(h) <= 0.5 * L * math.log(parseval_mass(profile_element(displacement(v)), L)) + 1e-9
            verdict = mass_criterion(w)
            fired += verdict
            verdicts.setdefault((L, B, _canon(w)), set()).add(verdict)
    assert (tot, shared, fired) == (85358, 5917, 5047)
    assert all(len(v) == 1 for v in verdicts.values())
    assert (len(verdicts), sum(1 for v in verdicts.values() if v == {True})) == (8947, 562)


def test_run_validity_and_element() -> None:
    """Lemma 12 and the element of Theorem 3, on every interval of levels with L <= 40: the
    raised run is a word iff D1 >= a or D2 = L - 1; its letters are 1, 2, 3 (1, 2 for runs of 12
    corners); its profile is the indicator of the run; its element is 1 - theta^g + theta^f or
    theta^f; and it is not a loop.  Below the top level a 3 appears iff D1 <= b - 1.  Of the
    55 855 valid runs, 5 245 reach the top level (rotations of the balanced word), 4 088 are
    runs of 12 corners and 46 522 contain a 3."""
    n = valid = top = twelve = threes = 0
    for L, B in coprime_pairs(40, 3):
        b, d = B - L, 2**B - 3**L
        for D1 in range(1, L):
            for D2 in range(D1, L):
                w = run_word(L, B, D1, D2)
                n += 1
                assert (w is not None) == run_is_valid(L, B, D1, D2)
                if w is None:
                    continue
                valid += 1
                assert max(w) <= 3
                assert displacement(w) == [int(D1 <= D <= D2) for D in range(L)]
                assert profile_element(displacement(w)) == run_element(L, D1, D2)
                assert cycle_numerator(w) % d != 0
                if D2 == L - 1:
                    top += 1
                    assert _canon(w) == _canon(christoffel(L, B))
                else:
                    assert (max(w) == 3) == (D1 <= b - 1)
                    twelve += D1 >= b
                    threes += D1 <= b - 1
    assert (n, valid, top, twelve, threes) == (79323, 55855, 5245, 4088, 46522)


def test_run_duality_and_counts() -> None:
    """Raising the runs inside [a, L-2] gives b(b-1)/2 distinct cyclic words.  A lowered run
    [D1, D2] is a word iff D2 <= b - 1, and it is the cyclic word of the raised run
    [L-1-D2, L-2-D2+D1].  Exactly a(a-1)/2 of the words consist of 1s and 2s: the runs of 12
    corners."""
    for L, B in coprime_pairs(40, 3):
        b = B - L
        a = L - b
        up = {_canon(run_word(L, B, D1, D2)) for D1 in range(a, L - 1) for D2 in range(D1, L - 1)}
        assert len(up) == b * (b - 1) // 2
        w0, Binv = christoffel(L, B), pow(B, -1, L)
        down = set()
        for D1 in range(1, L):
            for D2 in range(D1, L):
                v = list(w0)
                for D in range(D1, D2 + 1):
                    p = D * Binv % L
                    v[p - 1] -= 1
                    v[p] += 1
                assert (min(v) >= 1) == (D2 <= b - 1)
                if D2 <= b - 1:
                    assert _canon(tuple(v)) == _canon(run_word(L, B, L - 1 - D2, L - 2 - D2 + D1))
                    down.add(_canon(tuple(v)))
        assert down == up
        twelve = {_canon(run_word(L, B, D1, D2)) for D1 in range(b, L - 1) for D2 in range(D1, L - 1)}
        assert twelve == {c for c in up if max(c) <= 2} and len(twelve) == a * (a - 1) // 2


def test_run_theorem() -> None:
    """Theorem 3.  (a) B >= B0 + 1: mass <= 1 + 2 4^beta and (1 + 2 4^beta)/4^(1+beta) < 11/18,
    with (11/18)^(L/2) <= 1/2 for L >= 3.  (b) B = B0, L >= 18: mass < 13/4 + (9/4) 4^(1/18) <
    2.56^2, so Ellison's bound applies.  The exact d beats the Parseval bound on all 20 166
    coprime pairs with 18 <= L <= 400.  (c) L <= 17: every run word checked directly."""
    b0 = LOG2_3 - 1
    assert 4 ** (-1 - b0) + 0.5 < 11 / 18 + 1e-12 and (11 / 18) ** 1.5 <= 0.5 < 11 / 18
    assert 13 / 4 + 9 / 4 * 4 ** (1 / 18) < 5.6802 < ELLISON_BASE**2
    n, margin = 0, math.inf
    for L, B in coprime_pairs(400, 18):
        b = B - L
        if B > math.floor(L * LOG2_3) + 1:
            assert run_log_norm_bound(L, B) <= 0.5 * L * math.log(11 / 18) + B * math.log(2) < (B - 1) * math.log(2)
        else:
            assert 1 + 4 ** ((b - 1) / L) + 4 ** (b / L) < 13 / 4 + 9 / 4 * 4 ** (1 / 18)
        margin = min(margin, math.log(2**B - 3**L) - run_log_norm_bound(L, B))
        n += 1
    assert n == 20166 and margin > 3.2
    small = below = 0
    needed = []
    for L, B in coprime_pairs(17, 3):
        d = 2**B - 3**L
        if math.log(d) <= run_log_norm_bound(L, B):
            needed.append((L, B))
        for D1 in range(1, L):
            for D2 in range(D1, L):
                if run_is_valid(L, B, D1, D2):
                    assert cycle_numerator(run_word(L, B, D1, D2)) % d != 0
                    small += 1
                    below += D2 <= L - 2
    assert (small, below) == (2218, 1791)
    assert needed == [(3, 5), (5, 8)]  # elsewhere the exact d already beats the Parseval bound
    # a second route for part (b): Rhin's bound instead of Ellison's, from L = 342 on

    def rhin_gap(L: int) -> float:
        return L * math.log(3) - 13.3 * math.log(L * LOG2_3 + 1) - 0.5 * L * math.log(13 / 4 + 9 / 4 * 4 ** (1 / L))

    assert rhin_gap(341) < 0 < rhin_gap(342) and all(rhin_gap(L + 1) > rhin_gap(L) for L in range(100, 5000))


def test_positive_letters_are_needed() -> None:
    """The hypothesis of Theorem 3 is not decorative.  At (5, 8) the run [1, 2] is not a word:
    raising it gives (1, 3, 0, 3, 1), and its numerator 455 = 35 * 13 is divisible by d = 13.
    It is the only zero of 1 - theta0^g + theta0^f with 1 <= g < f <= L - 1 for L <= 60."""
    assert run_word(5, 8, 1, 2) is None and not run_is_valid(5, 8, 1, 2)
    assert cycle_numerator((1, 3, 0, 3, 1)) == 455 and 2**8 - 3**5 == 13
    zeros = []
    for L, B in coprime_pairs(60, 3):
        d = 2**B - 3**L
        t = theta0(L, B)
        pw = [1] * L
        for j in range(1, L):
            pw[j] = pw[j - 1] * t % d
        zeros += [(L, B, g, f) for g in range(1, L - 1) for f in range(g + 1, L) if (1 - pw[g] + pw[f]) % d == 0]
    assert zeros == [(5, 8, 2, 4)]


def test_run_exact_norms() -> None:
    """Exact norms (Bareiss) of all run elements 1 - theta^g + theta^f with L <= 22: odd, below
    the Parseval bound, and below d except at the two smallest slopes."""
    n, over = 0, set()
    for L, B in coprime_pairs(22, 3):
        a, d = 2 * L - B, 2**B - 3**L
        for D1 in range(a, L - 1):
            for D2 in range(D1, L - 1):
                q = run_element(L, D1, D2)
                N = abs(norm_exact(q, L))
                assert N % 2 == 1 and math.log(N) <= 0.5 * L * math.log(parseval_mass(q, L)) + 1e-9
                assert math.log(N) <= run_log_norm_bound(L, B) + 1e-9
                if N >= d:
                    over.add((L, B))
                n += 1
    assert n == 4589 and over == {(3, 5), (5, 8)}


def test_run_words_reach_far_from_balance() -> None:
    """A run of 12 corners with element 1 - theta^g + theta^f is exactly min(g, f - g) swaps from
    balance, so there are 2a + 1 - 4n such words at distance n, for n up to a // 2
    (breadth-first search over actual swaps at seven slopes)."""
    for L, B in ((13, 21), (17, 28), (18, 29), (19, 31), (21, 34), (22, 35), (23, 37)):
        b = B - L
        a = L - b
        dist = _classes_within(L, B, a // 2)
        prof: dict[int, int] = {}
        for D1 in range(b, L - 1):
            for D2 in range(D1, L - 1):
                g, f = L - 1 - D2, L - D1
                assert dist[_canon(run_word(L, B, D1, D2))] == min(g, f - g)
                prof[min(g, f - g)] = prof.get(min(g, f - g), 0) + 1
        assert prof == {k: 2 * a + 1 - 4 * k for k in range(1, a // 2 + 1)}


# ---------------------------------------------------------------------------
# section 6: repeats (Theorem 4)
# ---------------------------------------------------------------------------


def _orbit(c) -> tuple[list[int], list[int]]:
    """Members of a 3n+q loop in cycle order, and their halving counts."""
    ns = [c.elements[0]]
    while len(ns) < c.L:
        ns.append(syracuse_with_exponent(ns[-1], c.q)[0])
    assert syracuse_with_exponent(ns[-1], c.q)[0] == ns[0]
    return ns, [syracuse_with_exponent(n, c.q)[1] for n in ns]


def test_repeat_identity_on_real_loops(census) -> None:
    """Lemma 13 on every 3n+q loop of the census with L >= 2 (the +q cancels in differences):
    if the halving words from p and from q agree for j letters of weight X, then
    3^j (n_p - n_q) = 2^X (n_(p+j) - n_(q+j)).  Both differences are even, so
    2^(X+1) | n_p - n_q and M - m >= max(2^(X+1), 2 * 3^j)."""
    loops = pairs = longest = 0
    for c in census:
        L = c.L
        if L < 2:
            continue
        ns, w = _orbit(c)
        loops += 1
        for p in range(L):
            for q in range(p + 1, L):
                j = X = 0
                while j < L - 1 and w[(p + j) % L] == w[(q + j) % L]:
                    X += w[(p + j) % L]
                    j += 1
                if j == 0:
                    continue
                pairs += 1
                longest = max(longest, j)
                assert ns[p] != ns[q] and (ns[p] - ns[q]) % 2 ** (X + 1) == 0
                assert 3**j * (ns[p] - ns[q]) == 2**X * (ns[(p + j) % L] - ns[(q + j) % L])
                assert (ns[(p + j) % L] - ns[(q + j) % L]) % (2 * 3**j) == 0
                assert max(ns) - min(ns) >= max(2 ** (X + 1), 2 * 3**j)
    assert (loops, pairs, longest) == (1681, 100137, 7)


def test_member_size_bounds_on_real_loops(census) -> None:
    """Lemma 14 and Theorem 4 on every 3n+q loop with 2^B > 3^L (each bound carries a factor q):
    2^((D'_p - max D')/L) <= n_p (2^(B/L) - 3)/q <= 2^((D'_p - min D')/L) for every member, so
    m <= q/(2^(B/L) - 3) and M <= q 2^sigma/(2^(B/L) - 3); and the longest repeated stretch has
    weight X < log2 q + sigma + tau."""
    members = 0
    gap = -math.inf
    for c in census:
        ns, w = _orbit(c)
        L, B = c.L, sum(w)
        if 2**B <= 3**L:
            continue
        D = generalized_levels(w)
        base = 2 ** (B / L) - 3
        for p, n in enumerate(ns):
            v = math.log2(n * base / c.q)
            assert (D[p] - max(D)) / L - 1e-9 <= v <= (D[p] - min(D)) / L + 1e-9
            members += 1
        assert (3 * min(ns) + c.q) ** L >= 2**B * min(ns) ** L  # m <= q/(2^(B/L) - 3), exactly
        _, X, _, _ = longest_repeat(w)
        if X:
            gap = max(gap, X - (math.log2(c.q) + float(height_spread(w)) + size_exponent(L, B)))
    assert members == 22405 and -2.7 < gap < -2.6


def _lean_cycle(c) -> tuple[list[int], list[int], list[int]]:
    """A loop in the notation of lean/Collatz/Cycle.lean: y[0] = M, y[k+1] is the member
    before y[k], bb[k] is the halving count of the step y[k] -> y[k-1] (so bb[0] is unused),
    and BB[k] = bb[1] + ... + bb[k].  Indices are taken modulo L by the caller."""
    ns, w = _orbit(c)
    L = c.L
    top = ns.index(max(ns))
    y = [ns[(top - k) % L] for k in range(L)]
    bb = [w[(top - k) % L] for k in range(L)]
    for k in range(L):
        assert 3 * y[(k + 1) % L] + c.q == 2 ** bb[(k + 1) % L] * y[k]  # Cycle.bb_spec
    BB = [0]
    for k in range(1, L + 1):
        BB.append(BB[-1] + bb[k % L])
    return y, bb, BB


def _replay_lean(c) -> dict:
    """Every statement of lean/Collatz/Repeat.lean on one loop of 3n+q, in Lean's indexing.

    Returns the least certificates and the slack.  N is the least exponent passing the size
    test hN, a/b (b = 64) the least fraction passing hK, D the least height passing hD."""
    L, q = c.L, c.q
    y, bb, BB = _lean_cycle(c)
    B, M, m = BB[L], y[0], min(y)

    def window(p: int, j: int) -> int:
        return sum(bb[(p + i) % L] for i in range(1, j + 1))

    assert all(window(0, k) == BB[k] for k in range(L + 1))  # window_zero_left
    assert all(window(s, j) >= j for s in range(L) for j in (1, L))  # le_window
    for d in range(1, L):  # bb_period: no shift by d < L fixes the pattern
        assert any(bb[(i + 1) % L] != bb[(d + i + 1) % L] for i in range(L))

    N = 0
    while (3 * 2**N + q) ** L > 2 ** (N * L + B):
        N += 1
    assert N == 0 or (3 * 2 ** (N - 1) + q) ** L > 2 ** ((N - 1) * L + B)
    b = 64
    lo, hi = 0, b * 2**N  # least a with (3a + qb)^L <= a^L 2^B
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if (3 * mid + q * b) ** L <= mid**L * 2**B:
            hi = mid
        else:
            lo = mid
    a = hi
    assert (3 * a + q * b) ** L <= a**L * 2**B
    assert b * m <= a and m <= 2**N  # m_le_of_size

    heights = []
    for s in range(L):
        n = y[s]
        if a <= b * n:  # size_mono
            assert (3 * n + q) ** L <= n**L * 2**B
        if n**L * 2**B <= (3 * n + q) ** L:  # le_of_size
            assert b * n <= a
        Ds = max(k * B - L * window(s, k) for k in range(1, L + 1))  # least D for member s
        assert Ds >= 0
        assert (b * n) ** L <= a**L * 2**Ds and n**L <= 2 ** (N * L + Ds)  # member_pow_le
        heights.append(Ds)
    D = heights[0]  # the largest member: hD of max_pow_le
    assert D == max(k * B - L * BB[k] for k in range(1, L + 1))
    assert (b * M) ** L <= a**L * 2**D  # max_pow_le
    sw = -(-D // L)  # least whole s with k B <= L (B_k + s)
    assert all(k * B <= L * (BB[k] + sw) for k in range(1, L + 1))

    stretches = sharper = weaker = 0
    slack = slack_unique = slack_local = None
    for p in range(L):
        for r in range(p + 1, L):
            j = 0
            while bb[(p + j + 1) % L] == bb[(r + j + 1) % L]:
                j += 1
                assert j < L  # by bb_period the agreement stops
            for jj in range(1, j + 1):
                stretches += 1
                X = window(p, jj)
                assert X == window(r, jj)  # window_congr
                yp, yr = y[p], y[r]
                ypj, yrj = y[(p + jj) % L], y[(r + jj) % L]
                assert 3**jj * ypj + 2**X * yr == 3**jj * yrj + 2**X * yp  # repeat_identity
                t0, rem = divmod(ypj - yrj, 2**X)  # repeat_split
                assert rem == 0 and yp - yr == 3**jj * t0
                t, rem = divmod(ypj - yrj, 2 ** (X + 1))  # repeat_dvd
                assert rem == 0 and yp - yr == 2 * 3**jj * t and t != 0
                assert abs(ypj - yrj) >= 2 ** (X + 1) and abs(yp - yr) >= 2 * 3**jj  # repeat_gap
                assert m + 2 ** (X + 1) <= M and m + 2 * 3**jj <= M  # repeat_gap_M
                assert 2 ** (X + 1) < M  # repeat_lt_M
                assert (b * (m + 2 ** (X + 1))) ** L <= a**L * 2**D  # repeat_bound
                assert (X + 1) * L < N * L + D  # repeat_theorem
                assert N + sw > X + 1  # repeat_unique, contrapositive
                v = Fraction(N * L + D - (X + 1) * L, L)
                slack = v if slack is None else min(slack, v)
                u = N + sw - (X + 1)
                slack_unique = u if slack_unique is None else min(slack_unique, u)
                # the local forms: only the heights of the two starting members enter
                sp, sr = (p + jj) % L, (r + jj) % L
                hbig = heights[sp] if ypj >= yrj else heights[sr]
                hboth = max(heights[sp], heights[sr])
                assert (b * (min(ypj, yrj) + 2 ** (X + 1))) ** L <= a**L * 2**hbig  # repeat_bound_local
                assert (X + 1) * L < N * L + hbig  # repeat_theorem_local_of_le
                assert (X + 1) * L < N * L + hboth  # repeat_theorem_local
                assert N + -(-hboth // L) > X + 1  # repeat_unique_local, contrapositive
                sharper += hboth < D
                weaker += hboth > D
                v = Fraction(N * L + hboth - (X + 1) * L, L)
                slack_local = v if slack_local is None else min(slack_local, v)
    return {
        "N": N, "D": D, "a": a, "b": b, "M": M, "L": L, "stretches": stretches,
        "slack": slack, "slack_unique": slack_unique,
        "slack_local": slack_local, "sharper": sharper, "weaker": weaker,
    }  # fmt: skip


def test_lean_statements_on_real_loops(census) -> None:
    """lean/Collatz/Repeat.lean, statement by statement, on every 3n+q loop of the census.

    The Lean file proves these for every cycle; this test replays the same whole-number
    statements, in the same backward indexing, on loops that exist.  It guards the
    transcription, not the proof: Lean checks the proof, nothing checks that a formal
    statement means what the prose says except reading it and trying it.

    repeat_identity  3^j y(p+j) + 2^X y(r) = 3^j y(r+j) + 2^X y(p)
    repeat_dvd       y(p+j) - y(r+j) = 2^(X+1) t  and  y(p) - y(r) = 2 * 3^j t  with one t
    repeat_gap_M     m + 2^(X+1) <= M  and  m + 2 * 3^j <= M
    m_le_of_size     b m <= a             whenever (3a + qb)^L <= a^L 2^B
    member_pow_le    (b y_s)^L <= a^L 2^D whenever also k B <= L W_k + D for 1 <= k <= L
    repeat_bound     (b (m + 2^(X+1)))^L <= a^L 2^D
    repeat_theorem   (X + 1) L < N L + D  whenever (3 * 2^N + q)^L <= 2^(N L + B)
    repeat_unique    a stretch with X + 1 >= N + s occurs at one place
    bb_period        the halving counts have no period shorter than L
    repeat_bound_local, repeat_theorem_local, repeat_unique_local
                     the same with D the height of the two members the stretch starts from"""
    loops = stretches = with_repeat = sharper = weaker = 0
    slack = slack_unique = slack_local = math.inf
    tight = -math.inf
    for c in census:
        if c.L < 2:
            continue
        loops += 1
        r = _replay_lean(c)
        stretches += r["stretches"]
        tight = max(tight, math.log2(r["M"] * r["b"] / r["a"]) - r["D"] / r["L"])
        if r["stretches"]:
            with_repeat += 1
            slack = min(slack, r["slack"])
            slack_unique = min(slack_unique, r["slack_unique"])
            slack_local = min(slack_local, r["slack_local"])
            sharper += r["sharper"]
            weaker += r["weaker"]
    assert (loops, with_repeat, stretches) == (1681, 1464, 144004)
    # local forms against the form with the height h_M of the largest member: neither contains
    # the other.  Both starting members sit below h_M in 120 116 cases and one of them above
    # it in `weaker` cases; the least value of N + max(h)/L - (X + 1) is exactly 1
    assert (sharper, weaker, slack_local) == (120116, 18737, 1)
    assert slack == Fraction(13, 7)  # the least N + D/L - (X + 1) over the census
    assert slack_unique == 2  # the least N + s - (X + 1): repeat_unique never comes closer
    assert -0.052 < tight < -0.051  # max_pow_le is within 3.6 % of equality on some loop


def test_lean_size_hypothesis_is_needed() -> None:
    """The size test hN of Cycle.repeat_theorem cannot be relaxed by one.

    On the census the conclusion happens to survive N - 1 (it first fails at N - 2), so a
    witness has to be built.  The word 4^11 1 (L = 12, B = 45) is a loop of 3n + q with
    q = (2^45 - 3^12)/7.  Its stretch 4^10 occurs at two places, with X = 40.  The least
    certificates are N = 39 and D = 33, and 12 * 41 = 492 < 39 * 12 + 33 = 501; with N = 38
    the right side is 489.  Found by the referee pass of 2026-10-08."""
    from types import SimpleNamespace

    w = (4,) * 11 + (1,)
    L, B = len(w), sum(w)
    d = 2**B - 3**L

    def numerator(v: tuple[int, ...]) -> int:
        X, total = 0, 0
        for i, x in enumerate(v):
            total += 3 ** (L - 1 - i) * 2**X
            X += x
        return total

    cs = [numerator(w[p:] + w[:p]) for p in range(L)]
    g = gcd(d, *cs)
    q = d // g
    assert (g, q) == (7, 5026338793913)
    c = SimpleNamespace(L=L, q=q, elements=(cs[0] // g,))
    r = _replay_lean(c)
    assert (r["N"], r["D"], r["M"]) == (39, 33, 3093131606365)
    assert r["slack"] == Fraction(501 - 492, 12)
    assert not (12 * 41 < 38 * 12 + 33)  # N - 1 would break the conclusion
    assert r["slack_unique"] == 1  # 39 + 3 - 41: repeat_unique is sharp here as well


def test_longest_repeat_and_spread() -> None:
    """The helpers behind Theorem 4: longest_repeat agrees with a naive search, the balanced
    word has spread (L-1)/L, and size_exponent is below its Rhin / log 2 bound."""
    rng = random.Random(11)
    for _ in range(300):
        L = rng.randrange(3, 40)
        w = tuple(rng.choice((1, 1, 2, 2, 3)) for _ in range(L))
        best = 0
        for p in range(L):
            for q in range(p + 1, L):
                j = 0
                while j < L - 1 and w[(p + j) % L] == w[(q + j) % L]:
                    j += 1
                best = max(best, j)
        j, X, p, q = longest_repeat(w)
        assert j == best
        if j:
            assert p < q and [w[(p + i) % L] for i in range(j)] == [w[(q + i) % L] for i in range(j)]
            assert X == sum(w[(p + i) % L] for i in range(j)) and repeat_at_length(w, j) is not None
        assert repeat_at_length(w, j + 1) is None or j + 1 >= L
    for L in range(3, 61):
        for B in range(smallest_B(L), 2 * L):
            assert height_spread(balanced_word(L, B)) == Fraction(L - gcd(L, B), L)
            assert size_exponent(L, B) < size_exponent_bound(L, B)
            assert abs(size_exponent(L, B) + math.log2(2 ** (B / L) - 3)) < 1e-9
    # the smallest B needs exact arithmetic: at Hercher's length L log2 3 is 1.3e-12 below an integer
    assert all(smallest_B(L) == math.floor(L * LOG2_3) + 1 == (3**L).bit_length() for L in range(1, 3000))
    H = 137528045312
    assert smallest_B(H) == 217976794617 and math.floor(H * LOG2_3) + 1 == 217976794618
    assert 75.43 < size_exponent(H, smallest_B(H)) < 75.44 < 536 < size_exponent_bound(H, smallest_B(H))


def test_balanced_words_are_full_of_repeats() -> None:
    """Lemma 15: the stretch of j letters starting at a corner of the lower Christoffel word
    depends only on the arc of its level among the cut points 0, -b, ..., -jb (mod L).  So there
    are j + 1 stretches of length j, each of weight floor(jB/L) or ceil(jB/L).  A balanced word
    with gcd > 1 has at most j + 1 as well."""
    for L, B in coprime_pairs(70, 3):
        w, b = christoffel(L, B), B - L
        for j in range(1, L):
            cuts = sorted({(-i * b) % L for i in range(j + 1)})
            arc_of = {}
            for D in range(L):
                arc_of[D] = max([c for c in cuts if c <= D], default=cuts[-1])
            by_arc: dict[int, set] = {}
            weights = set()
            for p in range(L):
                f = tuple(w[(p + i) % L] for i in range(j))
                by_arc.setdefault(arc_of[(p * B) % L], set()).add(f)
                weights.add(sum(f))
            assert len(cuts) == j + 1 and all(len(v) == 1 for v in by_arc.values())
            assert len({next(iter(v)) for v in by_arc.values()}) == j + 1
            assert weights <= {(j * B) // L, -((-j * B) // L)}
    for L in range(4, 61):
        for B in range(math.floor(L * LOG2_3) + 1, 2 * L):
            if gcd(L, B) == 1:
                continue
            w, g = balanced_word(L, B), gcd(L, B)
            for j in range(1, L):
                fs = {tuple(w[(p + i) % L] for i in range(j)) for p in range(L)}
                assert len(fs) == min(j + 1, L // g)
                assert {sum(f) for f in fs} <= {(j * B) // L, -((-j * B) // L)}


def _move_corners(w0: tuple[int, ...], moves) -> tuple[int, ...] | None:
    v = list(w0)
    for p, sg in moves:
        v[p - 1] += sg
        v[p] -= sg
    return tuple(v) if min(v) >= 1 else None


def test_repeat_theorem_excludes_words_near_balance() -> None:
    """Corollary 16 in practice, with the exact size exponent: whenever (k + 1)(j + 1) < L for
    the window j of displacement span 3, a balanced word with k corners moved one step each
    (any gcd) has a repeated stretch of weight >= sigma + tau, so Theorem 4 excludes it."""
    rng = random.Random(5)
    n = 0
    for L in (120, 200, 300, 306, 400, 600):
        B0 = math.floor(L * LOG2_3) + 1
        for B in (B0, B0 + 1, B0 + 5):
            w0 = balanced_word(L, B)
            d = 2**B - 3**L
            for k in (1, 2, 3, 5, 8):
                if max_moved_corners(L, B, 3, exact=True) < k:
                    continue
                j = moved_corner_window(L, B, 3, exact=True)
                for _ in range(4):
                    w = None
                    while w is None:
                        ps = rng.sample(range(L), k)
                        w = _move_corners(w0, [(p, rng.choice((1, -1))) for p in ps])
                    assert height_spread(w) < 3
                    jj, X, _, _ = longest_repeat(w)
                    assert jj >= j and X >= float(height_spread(w)) + size_exponent(L, B)
                    assert repeat_excludes(w) and cycle_numerator(w) % d != 0
                    n += 1
    assert n == 360


def test_repeat_theorem_numbers() -> None:
    """The explicit form of Corollary 16, valid for every B: k corners with displacement span s
    are excluded when k + 1 < L / Psi(L, s).  L / Psi increases, so each k has a threshold.
    At Hercher's floor L = 137 528 045 312 the window is 341 letters."""
    assert all(moved_corner_reach(L + 1, s) > moved_corner_reach(L, s) for s in (1, 3, 7) for L in range(3, 3000))

    def first_L(k: int, s: int) -> int:
        L = 3
        while not k + 1 < moved_corner_reach(L, s):
            L += 1
        return L

    assert first_L(0, 1) == 62
    assert [first_L(k, 3) for k in (1, 2, 3, 4, 5, 10, 100)] == [149, 242, 340, 443, 548, 1104, 13414]
    # the explicit form is implied by the window count, for every admissible B
    for L in (62, 149, 340, 1000, 5000):
        for B in range(math.floor(L * LOG2_3) + 1, 2 * L, max(1, L // 7)):
            assert max_moved_corners(L, B, 3) + 1 >= math.ceil(moved_corner_reach(L, 3)) - 1
    H = 137528045312
    BH = smallest_B(H)
    assert moved_corner_window(H, BH, 3) == 341 and max_moved_corners(H, BH, 3) == 402128786
    assert math.floor(moved_corner_reach(H, 3)) == 401035065
    # with the exact size exponent of the pair (H, BH), 75.43, the stretch needed has 50 letters
    assert moved_corner_window(H, BH, 3, exact=True) == 50 and max_moved_corners(H, BH, 3, exact=True) == 2696628338
    lo, hi = 0, H
    while lo < hi:  # k arbitrary swaps move at most k corners, with displacement span at most isqrt(2k) + 1
        mid = (lo + hi + 1) // 2
        lo, hi = (mid, hi) if mid + 1 < moved_corner_reach(H, swap_span(mid)) else (lo, mid - 1)
    assert lo == 27426966


def test_swap_span() -> None:
    """After k swaps of a balanced word of 1s and 2s the height spread is below isqrt(2k) + 1:
    all 7 766 cyclic classes within 8 swaps of balance at seven slopes, two of them not coprime."""
    n = 0
    for L, B in ((13, 21), (17, 27), (18, 29), (19, 31), (16, 26), (20, 32), (12, 20)):
        start = _canon(balanced_word(L, B))
        dist = {start: 0}
        frontier = [start]
        for k in range(1, 9):
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
        for w, k in dist.items():
            assert height_spread(w) < swap_span(k)
            n += 1
    assert n == 7766


def test_three_moved_corners_every_length() -> None:
    """Corollary 18: at most three corners of a balanced word moved one step each, positive
    letters, any gcd, every L.  (i) L >= 77: Ellison's bound gives tau < log2(2L/3) +
    L log2(3/2.56) at the smallest B, and a window j with 4(j + 1) < L; above the smallest B,
    tau < log2 L - 1.05.  (ii) 30 <= L <= 339 (only 30..76 is needed): an exact integer test
    confirms the window on all 23 583 pairs.  (iii) L <= 29: all 1 087 329 corner moves
    (1 087 266 distinct words, 698 of them non-primitive) checked directly, through the sum
    c_bal + sum of the moved terms, which is a unit times c(w) modulo d."""
    for L in range(18, 3001):
        B0 = smallest_B(L)
        tau_hat = math.log2(2 * L / 3) + L * math.log2(3 / ELLISON_BASE)
        assert size_exponent(L, B0) < tau_hat  # 2^(B/L) - 3 >= 3d/(2L 3^L) and d > 2.56^L
        j = math.ceil((4 + tau_hat) / LOG2_3)
        assert 4 * (j + 1) < L or L <= 76  # holds from 77 on, and fails at 76
        assert L != 76 or 4 * (j + 1) >= L
        if L >= 77:
            assert (j * B0) // L >= 3 + tau_hat
            j1 = math.ceil((4 + math.log2(L) - 1.05) / LOG2_3)
            assert 4 * (j1 + 1) < L and (j1 * (B0 + 1)) // L >= 3 + size_exponent(L, B0 + 1)
    assert 4 < moved_corner_reach(340, 3) and not 4 < moved_corner_reach(339, 3)  # the Rhin form
    pairs = 0
    for L in range(30, 340):
        for B in range(smallest_B(L), 2 * L):
            j = moved_corner_window(L, B, 3, exact=True)
            assert 4 * (j + 1) < L and window_suffices(L, B, j, 3) and not window_suffices(L, B, j - 1, 3)
            pairs += 1
    assert pairs == 23583
    words = 0
    distinct, nonprimitive = set(), {}
    for L in range(3, 30):
        for B in range(math.floor(L * LOG2_3) + 1, 2 * L):
            w0 = balanced_word(L, B)
            d = 2**B - 3**L
            half = (d + 1) // 2
            X, term = 0, []
            for p, x in enumerate(w0):
                term.append(pow(3, L - 1 - p, d) * pow(2, X, d) % d)
                X += x
            c0 = sum(term) % d
            assert c0 == cycle_numerator(w0) % d
            for k in (1, 2, 3):
                for ps in combinations(range(L), k):
                    for sgs in product((1, -1), repeat=k):
                        w = _move_corners(w0, list(zip(ps, sgs)))
                        if w is None:
                            continue
                        S = (c0 + sum(term[p] if sg == 1 else -term[p] * half for p, sg in zip(ps, sgs))) % d
                        assert S != 0
                        distinct.add((B, w))
                        for h in (2, 3, 5, 7):
                            if L % h == 0 and w == w[: L // h] * h:
                                nonprimitive[(k, h)] = nonprimitive.get((k, h), 0) + 1
                        if words % 997 == 0:  # the sum is a unit times c(w): spot-check the relation
                            u = 1 if ps[0] != 0 else (half if sgs[0] == 1 else 2)
                            assert cycle_numerator(w) % d == u * S % d
                        words += 1
    assert words == 1087329 and len(distinct) == 1087266
    # a non-primitive word v^h here has k = h in {2, 3}: v is one corner move from a balanced word
    assert nonprimitive == {(2, 2): 556, (3, 3): 142}


def test_few_runs_have_few_stretches() -> None:
    """Corollary 17: a word whose profile has r' jump points in level order has at most
    (j + 1)(r' + 1) different stretches of length j, each of weight >= floor(jB/L) - (s - 1).
    Checked on random profiles with values 0 and 1 (unions of raised runs)."""
    rng = random.Random(8)
    n = 0
    for L, B in ((55, 89), (89, 142), (144, 229), (233, 370)):
        a = 2 * L - B
        for r in (1, 2, 3, 5, 8):
            for _ in range(6):
                cuts = sorted(rng.sample(range(a, L), 2 * r))
                m = [0] * L
                for i in range(r):
                    for D in range(cuts[2 * i], cuts[2 * i + 1]):
                        m[D] = 1
                w = profile_word(L, B, m)
                assert w is not None and displacement(w) == m
                jumps = sum(1 for D in range(L) if m[D] != m[D - 1])
                assert jumps <= 2 * r and height_spread(w) < 2
                for j in (3, 7, 12, 20):
                    fs = {tuple(w[(p + i) % L] for i in range(j)) for p in range(L)}
                    assert len(fs) <= (j + 1) * (jumps + 1)
                    assert min(sum(f) for f in fs) >= (j * B) // L - 1
                n += 1
    assert n == 120


def test_one_move_from_a_power() -> None:
    """Lemma 19: c(u^g) = c(u) Phi with Phi = (2^(gB') - 3^(gL')) / (2^B' - 3^L').  Moving one
    corner of u^g changes c by +-3^alpha 2^beta, so gcd(c(w), Phi) = 1 and d does not divide
    c(w), for every word u with positive letters and every g >= 2."""
    n = 0
    for Lp in range(1, 5):
        for u in product(range(1, 5), repeat=Lp):
            Bp = sum(u)
            if 2**Bp <= 3**Lp:
                continue
            for g in (2, 3, 4):
                w0 = tuple(u) * g
                L, d = Lp * g, 2 ** (Bp * g) - 3 ** (Lp * g)
                Phi = d // (2**Bp - 3**Lp)
                assert Phi * (2**Bp - 3**Lp) == d and cycle_numerator(w0) == cycle_numerator(u) * Phi
                assert Phi > 1 and gcd(Phi, 6) == 1
                for p in range(L):
                    for sg in (1, -1):
                        w = _move_corners(w0, [(p, sg)])
                        if w is not None:
                            assert gcd(cycle_numerator(w), Phi) == 1 and cycle_numerator(w) % d != 0
                            n += 1
    assert n == 16452


# ---------------------------------------------------------------------------
# section 7: reach of the norm test, by swap distance from balance
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# section 6.2: local repeats (Theorem 5)
# ---------------------------------------------------------------------------


def _loop_of_word(w: tuple[int, ...]) -> tuple[int, list[int]] | None:
    """A primitive word as a loop of 3n+q: ``(q, members)`` with ``q = d/g`` and members
    ``c(w^(p))/g``, ``g = gcd(d, c(w))``.  ``None`` if ``2^B <= 3^L``."""
    L, B = len(w), sum(w)
    d = 2**B - 3**L
    if d <= 0:
        return None
    cs = [cycle_numerator(w[p:] + w[:p]) for p in range(L)]
    g = gcd(d, *cs)
    return d // g, [c // g for c in cs]


def _check_local_theorem(w: tuple[int, ...], q: int, ns: list[int]) -> tuple[int, int, Fraction | None]:
    """Theorem 5 on one loop of 3n+q, forward notation: every repeated stretch, exactly.
    Returns (stretches, stretches where the local height is below the spread, least slack)."""
    L, B = len(w), sum(w)
    for p in range(L):
        assert 2 ** w[p] * ns[(p + 1) % L] == 3 * ns[p] + q
    N = least_size_exponent(L, B, q)
    h = heights(w)
    spread = max(h)
    for p in range(L):  # Lemma 14, member by member, in the form of Cycle.member_pow_le
        assert ns[p] ** L <= 2 ** (N * L + h[p])
    count = sharper = 0
    slack = None
    for p in range(L):
        for r in range(p + 1, L):
            j = X = 0
            while j < L - 1 and w[(p + j) % L] == w[(r + j) % L]:
                X += w[(p + j) % L]
                j += 1
                hh = max(h[p], h[r])
                assert abs(ns[p] - ns[r]) >= 2 ** (X + 1)
                assert (X + 1) * L < N * L + hh  # Theorem 5
                count += 1
                sharper += hh < spread
                v = Fraction(N * L + hh - (X + 1) * L, L)
                slack = v if slack is None else min(slack, v)
    return count, sharper, slack


def test_local_repeat_theorem_on_real_loops(census) -> None:
    """Theorem 5 on every 3n+q loop of the census: a stretch of weight X that starts at two
    different members has X + 1 < N + max(h_p, h_r)/L, where h is the height of a starting
    member above the lowest level and N >= tau + log2 q is the least whole exponent passing the
    size test.  Theorem 4 has the full spread in place of max(h_p, h_r).  The functions
    local_repeat (both forms) must find nothing to exclude on a loop that exists."""
    loops = stretches = sharper = 0
    slack = math.inf
    for c in census:
        if c.L < 2:
            continue
        ns, w = _orbit(c)
        w = tuple(w)
        loops += 1
        n, sh, sl = _check_local_theorem(w, c.q, ns)
        stretches += n
        sharper += sh
        if sl is not None:
            slack = min(slack, sl)
        assert local_repeat(w, c.q) is None and local_repeat(w, c.q, local=False) is None
    # 141 056 of the 144 004 stretches start from two members that both sit below the spread
    assert (loops, stretches, sharper, slack) == (1681, 144004, 141056, 1)


def test_local_repeat_theorem_on_every_small_word() -> None:
    """Theorem 5 is not vacuous: every primitive word with positive letters is the halving word
    of a loop of 3n + d/g, and the theorem holds there with log2 q added to tau.  All words
    with L <= 9 and 2^B > 3^L, B <= 2L + 1."""
    words = stretches = sharper = integral = 0
    slack = math.inf
    for L in range(2, 10):
        for B in range(smallest_B(L), 2 * L + 2):
            for cuts in combinations(range(1, B), L - 1):
                w = tuple(b - a for a, b in zip((0,) + cuts, cuts + (B,)))
                if not _primitive(w):
                    continue
                q, ns = _loop_of_word(w)
                words += 1
                integral += q == 1
                n, sh, sl = _check_local_theorem(w, q, ns)
                stretches += n
                sharper += sh
                if sl is not None:
                    slack = min(slack, sl)
                assert local_repeat(w, q) is None
    assert (words, stretches, sharper, integral, slack) == (122422, 1688793, 1550704, 0, 2)


def test_consecutive_corners_of_a_balanced_word_repeat() -> None:
    """Lemma 20: among any j + 2 consecutive corners of a balanced word, two carry the same
    stretch of length j (1 <= j <= L - 2), whatever the gcd.  So 2j + 1 consecutive letters of
    a balanced word always contain a repeated stretch of length j."""
    pairs = cases = 0
    for L in range(3, 61):
        for B in range(smallest_B(L), 2 * L):
            c = balanced_word(L, B)
            cc = c + c + c
            pairs += 1
            for j in range(1, L - 1):
                for p0 in range(L):
                    seen = {cc[p0 + i : p0 + i + j] for i in range(j + 2)}
                    assert len(seen) <= j + 1
                    cases += 1
    assert (pairs, cases) == (729, 1292357)


def _below_and_touching(c: tuple[int, ...], p0: int, touch: int, u: int, rng: random.Random) -> tuple[int, ...]:
    """A word whose staircase agrees with that of ``c`` on the ``touch`` corners from ``p0``,
    rises at most ``u`` steps above it elsewhere, and otherwise wanders below it: the
    displacement falls by at most one per step (only where ``c`` has a 2) and jumps back up
    freely, which makes long runs of 1s followed by one large letter."""
    L = len(c)
    m = [0] * L
    cur = 0
    for t in range(touch, L):
        p = (p0 + t) % L
        prev_letter = c[(p - 1) % L]
        lowest = cur + 1 - prev_letter  # keeps the letter before corner p positive
        r = rng.random()
        if r < 0.75:
            cur = lowest
        elif r < 0.9:
            cur = rng.randint(lowest, max(lowest, u))
        else:
            cur = max(lowest, rng.randint(min(0, lowest), u))
        m[p] = cur
    w = tuple(c[p] + m[(p + 1) % L] - m[p] for p in range(L))
    return w


def _touching_pair(w: tuple[int, ...], p0: int, j: int, N: int) -> tuple[int, int] | None:
    """The mechanism of Corollary 21, checked directly: two of the corners p0, ..., p0 + j + 1
    whose stretches of length exactly j are equal and forbidden by Theorem 5."""
    L = len(w)
    h = heights(w)
    ww = w + w + w
    for a in range(j + 2):
        for b in range(a + 1, j + 2):
            pa, pb = (p0 + a) % L, (p0 + b) % L
            if ww[pa : pa + j] == ww[pb : pb + j]:
                X = sum(ww[pa : pa + j])
                if (X + 1) * L >= N * L + max(h[pa], h[pb]):
                    return pa, pb
    return None


def _forbidden_pairs(w: tuple[int, ...], N: int) -> list[tuple[int, int]]:
    """Every pair of positions that Theorem 5 forbids, through their longest common stretch."""
    L = len(w)
    h = heights(w)
    out = []
    for p in range(L):
        for r in range(p + 1, L):
            j = X = 0
            while j < L - 1 and w[(p + j) % L] == w[(r + j) % L]:
                X += w[(p + j) % L]
                j += 1
            if j and (X + 1) * L >= N * L + max(h[p], h[r]):
                out.append((p, r))
    return out


def test_low_stretch_corollary() -> None:
    """Corollary 21 in practice.  Words that lie on or below a balanced staircase (at most u
    steps above it), and touch it along 2j + 2 consecutive corners with floor(jB/L) >= N + u,
    are excluded by Theorem 5 through two of the touching corners (_touching_pair checks that
    mechanism, not merely that some pair is forbidden).  Theorem 4 misses 79 of the 210, or 84
    in its whole-exponent form.  Each word is a genuine loop of 3n + d/g with q = d/g > 1, and
    with that q nothing is excluded.

    These words have long runs of 1s in the hanging part, which Theorem 5 forbids by
    themselves; test_low_stretch_corollary_isolated uses words without them."""
    rng = random.Random(20261009)
    made = whole_misses = real_misses = 0
    biggest_spread = Fraction(0)
    for L in (60, 90, 120, 150):
        for B in (smallest_B(L), smallest_B(L) + 1, smallest_B(L) + 7):
            if B >= 2 * L:
                continue
            c = balanced_word(L, B)
            N = least_size_exponent(L, B)
            tau = size_exponent(L, B)
            for u in (0, 1, 2):
                j = 1
                while (j * B) // L < N + u:
                    j += 1
                assert 2 * j + 2 <= L
                for _ in range(6):
                    p0 = rng.randrange(L)
                    w = _below_and_touching(c, p0, 2 * j + 2, u, rng)
                    if min(w) < 1 or w == c or not _primitive(w):
                        continue
                    assert len(w) == L and sum(w) == B
                    assert touching_stretch(w, c, j, u) is not None  # the hypothesis
                    assert _touching_pair(w, p0, j, N) is not None  # the proof's own pair
                    hit = local_repeat(w)
                    assert hit is not None  # Theorem 5 forbids it
                    p, r, jj, X = hit
                    h = heights(w)
                    assert (X + 1) * L >= N * L + max(h[p], h[r])
                    made += 1
                    sigma = height_spread(w)
                    # Theorem 4 with the real tau and the heaviest repeated stretch
                    miss = heaviest_repeat(w) + 1 < float(sigma) + tau - 1e-9
                    real_misses += miss
                    if local_repeat(w, local=False) is None:  # whole exponent N in place of tau
                        whole_misses += 1
                        biggest_spread = max(biggest_spread, sigma)
                    assert not (miss and local_repeat(w, local=False) is not None)
                    q, ns = _loop_of_word(w)
                    assert q > 1  # so w is not a loop of 3n+1 ...
                    assert local_repeat(w, q) is None  # ... and is consistent as a loop of 3n+q
                    _check_local_theorem(w, q, ns)
    assert (made, real_misses, whole_misses, biggest_spread) == (210, 79, 84, Fraction(93, 5))


def _irregular_below(c: tuple[int, ...], p0: int, touch: int, rng: random.Random) -> tuple[int, ...]:
    """Like _below_and_touching with u = 0, but the displacement falls at only half of the 2s
    and comes back up in random jumps: no long runs of 1s, so the hanging part has few
    repeats of its own."""
    L = len(c)
    m = [0] * L
    cur = 0
    for t in range(touch, L):
        p = (p0 + t) % L
        lowest = cur + 1 - c[(p - 1) % L]
        if rng.random() < 0.04:
            cur = rng.randint(cur, 0)
        elif lowest < cur and rng.random() < 0.5:
            cur = lowest
        m[p] = cur
    return tuple(c[p] + m[(p + 1) % L] - m[p] for p in range(L))


def test_low_stretch_corollary_isolated() -> None:
    """Corollary 21 where nothing else helps.  In hanging words without long runs of 1s the
    touching corners still carry a forbidden pair (always), Theorem 4 misses every one of them,
    and in some the touching corners carry the ONLY forbidden pairs."""
    rng = random.Random(5)
    made = t4_misses = only_touching = 0
    for L, B in ((200, 317), (300, 476)):
        c = balanced_word(L, B)
        N = least_size_exponent(L, B)
        tau = size_exponent(L, B)
        j = 1
        while (j * B) // L < N:
            j += 1
        for _ in range(30):
            p0 = rng.randrange(L)
            w = _irregular_below(c, p0, 2 * j + 2, rng)
            if min(w) < 1 or not _primitive(w):
                continue
            made += 1
            assert touching_stretch(w, c, j, 0) is not None
            assert _touching_pair(w, p0, j, N) is not None
            touching = {(p0 + i) % L for i in range(j + 2)}
            pairs = _forbidden_pairs(w, N)
            assert any(a in touching and b in touching for a, b in pairs)
            only_touching += all(a in touching and b in touching for a, b in pairs)
            t4_misses += heaviest_repeat(w) + 1 < float(height_spread(w)) + tau - 1e-9
    assert (made, t4_misses, only_touching) == (60, 60, 5)


def test_lowered_corners_corollary() -> None:
    """Corollary 22: k corners of a balanced word moved down by any number of steps (and none
    up) leave a run of 2j + 2 unmoved corners as soon as k (2j + 2) < L, so the word is
    excluded.  On these short words Theorem 4 excludes them too (counted);
    test_lowered_corners_beyond_theorem_4 has a word where it does not."""
    rng = random.Random(7)
    made = deepest = also_theorem_4 = 0
    for L, B in ((200, 317), (200, 318), (300, 476), (400, 634), (400, 640)):
        c = balanced_word(L, B)
        N = least_size_exponent(L, B)
        j = 1
        while (j * B) // L < N:
            j += 1
        kmax = (L - 1) // (2 * j + 2)
        assert kmax >= 2
        for _ in range(8):
            k_target = rng.randint(1, kmax)
            # pits: the displacement falls by one at each corner that follows a 2 of c, for as
            # long as the pit lasts, and returns to 0 in one jump (one large letter)
            m = [0] * L
            moved = 0
            for _attempt in range(200):
                if moved >= k_target:
                    break
                start = rng.randrange(1, L - 1)
                want = rng.randint(1, k_target - moved)
                if m[start - 1] != 0:
                    continue
                depth, t, pit = 0, start, []
                while len(pit) < want and t < L - 1 and m[t] == 0:
                    if c[t - 1] == 2:
                        depth += 1
                    if depth == 0:
                        break
                    pit.append((t, -depth))
                    t += 1
                if not pit or m[t] != 0:
                    continue
                for pos, val in pit:
                    m[pos] = val
                moved += len(pit)
            w = tuple(c[p] + m[(p + 1) % L] - m[p] for p in range(L))
            k = sum(1 for x in m if x != 0)
            if k == 0 or min(w) < 1 or not _primitive(w):
                continue
            assert k * (2 * j + 2) < L and max(m) == 0
            p0 = touching_stretch(w, c, j, 0)
            assert p0 is not None and _touching_pair(w, p0, j, N) is not None
            assert local_repeat(w) is not None
            made += 1
            deepest = max(deepest, -min(m))
            also_theorem_4 += local_repeat(w, local=False) is not None
    assert (made, deepest, also_theorem_4) == (40, 13, 40)


def test_lowered_corners_beyond_theorem_4() -> None:
    """Corollary 22 on a word that Theorem 4 misses.  L = 12 000, B = 19 220: one pit of 599
    corners, 210 steps deep, with the displacement falling at about 60 % of the 2s, and 600
    single corners lowered at irregular intervals elsewhere.  The spread is 210, the heaviest
    repeated stretch has 186 halvings, so Theorem 4 says nothing; the 1 199 moved corners still
    leave a run of 10 unmoved corners, and Theorem 5 forbids two of them."""
    L = 12000
    B = smallest_B(L) + 200
    assert B == 19220
    c = balanced_word(L, B)
    N = least_size_exponent(L, B)
    tau = size_exponent(L, B)
    j = 1
    while (j * B) // L < N:
        j += 1
    kmax = (L - 1) // (2 * j + 2)
    assert (N, j, kmax) == (5, 4, 1199) and kmax == max_lowered_corners(L, B, exact=True)
    rng = random.Random(5)
    m = [0] * L
    cur, t, used = 0, 1, 0
    while used < kmax // 2:  # the deep pit
        lowest = cur + 1 - c[t - 1]
        if lowest < cur and rng.random() < 0.6:
            cur = lowest
        if cur != 0:
            m[t] = cur
            used += 1
        t += 1
    lo_sp = 2 * j + 3
    hi_sp = int(2 * (L - t) / (kmax - used) - lo_sp)
    t += lo_sp
    while t < L - 1 and sum(1 for x in m if x) < kmax:  # single corners, one step down
        if c[t - 1] == 2 and m[t - 1] == 0:
            m[t] = -1
            t += rng.randint(lo_sp, hi_sp)
        else:
            t += 1
    w = tuple(c[p] + m[(p + 1) % L] - m[p] for p in range(L))
    k = sum(1 for x in m if x)
    assert min(w) >= 1 and max(m) == 0 and (k, -min(m)) == (1199, 210)
    assert k * (2 * j + 2) < L  # the hypothesis of Corollary 22
    p0 = touching_stretch(w, c, j, 0)
    assert p0 is not None and _touching_pair(w, p0, j, N) is not None
    assert local_repeat(w) is not None  # Theorem 5 forbids it
    heaviest, spread = heaviest_repeat(w), max(heights(w))
    assert heaviest == 186
    assert heaviest + 1 < spread / L + tau  # Theorem 4, real tau: 187 < 214.86
    assert (heaviest + 1) * L < N * L + spread  # and in its whole-exponent form


def test_local_and_largest_member_forms_are_incomparable() -> None:
    """Two remarks of section 6.2, on real loops found by the referee pass.

    The loop 13 -> 499 -> 307 -> 235 of 3n+959 has heights 0, 10, 12, 14.  Its largest member
    499 sits at height 10, below 307 and 235.  The stretch "3" starts at 499 and at 307, so the
    local form uses max(h) = 12 where the form of section 6.1 uses h_M = 10: Theorem 5 does
    not contain that form.

    The loop 5 -> 11 -> 53 -> 29 of 3n+73 shows that the LARGER of the two heights is needed:
    the stretch "3" starts at 5 (height 0) and 53 (height 8), N = 4, and with the smaller height
    the inequality would read 16 < 16."""
    q, ns, w = 959, [13, 499, 307, 235], (1, 3, 3, 7)
    for p in range(4):
        assert 2 ** w[p] * ns[(p + 1) % 4] == 3 * ns[p] + q
    assert heights(w) == [0, 10, 12, 14] and max(ns) == 499
    assert w[1] == w[2] and max(heights(w)[1], heights(w)[2]) == 12 > heights(w)[1]
    _check_local_theorem(w, q, ns)

    q, ns, w = 73, [5, 11, 53, 29], (3, 1, 3, 5)
    for p in range(4):
        assert 2 ** w[p] * ns[(p + 1) % 4] == 3 * ns[p] + q
    h, N = heights(w), least_size_exponent(4, 12, 73)
    assert (h[0], h[2], N) == (0, 8, 4) and w[0] == w[2] == 3
    assert (3 + 1) * 4 < N * 4 + max(h[0], h[2])  # Theorem 5: 16 < 24
    assert not ((3 + 1) * 4 < N * 4 + min(h[0], h[2]))  # with the smaller height: 16 < 16
    _check_local_theorem(w, q, ns)


def test_local_repeat_numbers() -> None:
    """The numbers quoted in section 6.2.  At Hercher's length a balanced stretch of 679
    letters (Rhin's bound at the smallest B) or 97 letters (the exact size exponent) suffices;
    the explicit form 2 Psi(L, u) - 1 bounds the length for every admissible B."""
    H = 137528045312
    BH = smallest_B(H)
    assert (low_stretch_window(H, BH), low_stretch_length(H, BH)) == (339, 679)
    assert (low_stretch_window(H, BH, exact=True), low_stretch_length(H, BH, exact=True)) == (48, 97)
    assert low_stretch_length(H, BH, 1) == 681
    assert (max_lowered_corners(H, BH), max_lowered_corners(H, BH, exact=True)) == (202247125, 1403347401)
    # like with like: Corollary 16's direct count at the same length, one step each
    assert max_moved_corners(H, BH, 3) == 402128786
    # the explicit formula j = ceil((u + 1 + tau_bar)/log2 3) gives 340, hence 681 letters
    tau_bar = math.log2(H / 3) + 13.3 * math.log2(H * LOG2_3 + 1)
    assert math.ceil((1 + tau_bar) / LOG2_3) == 340
    for L in (100, 1000, 10**4, 10**6, H):
        for u in (0, 1, 3):
            for B in (smallest_B(L), smallest_B(L) + 1, smallest_B(L) + L // 10):
                assert low_stretch_length(L, B, u) <= 2 * (L / moved_corner_reach(L, u)) - 1
    # small pairs, exact: how many consecutive letters must agree with the balanced word
    need = {}
    for L, B in ((13, 21), (41, 65), (200, 317), (306, 485), (987, 1565)):
        N = least_size_exponent(L, B)
        j = 1
        while (j * B) // L < N:
            j += 1
        need[(L, B)] = 2 * j + 1
        assert need[(L, B)] == low_stretch_length(L, B, exact=True)
    assert need == {(13, 21): 7, (41, 65): 15, (200, 317): 19, (306, 485): 23, (987, 1565): 15}


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
