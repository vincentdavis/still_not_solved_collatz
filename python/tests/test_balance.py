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
    christoffel,
    cycle_numerator,
    norm_exact,
    norm_test,
    odd_part,
    one_swaps,
    parseval_log_bound,
    spread_threshold,
    swap_element,
    theta0,
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
# section 4: reach of the norm test, by swap distance from balance
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
