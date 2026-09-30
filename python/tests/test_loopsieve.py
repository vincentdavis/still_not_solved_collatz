"""Witnesses for docs/LOOP_SIEVE.md and web/loopsieve.html: the loop sieve (q = 1).

Every number quoted on the page is pinned here.  General q appears only as a harness
(``test_filter_a_q5_harness``).
"""

from __future__ import annotations

import math
from collections import Counter
from fractions import Fraction

from collatz_maxodd.cycles import find_cycles
from collatz_maxodd.loopsieve import (
    VERIFIED_LIMIT,
    classes_hit,
    compositions,
    doorway,
    last_survivor,
    loop_through_class,
    odd_steps_table,
    odd_steps_to_one,
    pass_histogram,
    pass_one,
    pass_records,
    pass_two_closed_form,
    rational_loop,
    rational_loop_point,
    shadow_rate,
    shadow_survival,
    shadow_survival_float,
    survivors_after,
)
from collatz_maxodd.syracuse import syracuse, syracuse_with_exponent

# ---------------------------------------------------------------------------
# L1: the user's rule
# ---------------------------------------------------------------------------


def test_pass_one_is_exactly_the_powers_of_two() -> None:
    p1 = pass_one(2**40)
    assert p1[:8] == [5, 21, 85, 341, 1365, 5461, 21845, 87381]
    assert len(p1) == 19
    want = [n for n in range(3, 1 << 20, 2) if (3 * n + 1) & (3 * n) == 0]
    assert want == pass_one(1 << 20)
    for k, n in enumerate(p1, start=2):
        assert 3 * n + 1 == 4**k and syracuse(n) == 1
        assert bin(n)[2:] == "10" * (k - 1) + "1"
        assert (n % 3 == 0) == (k % 3 == 0)
    assert VERIFIED_LIMIT == 2**71


#: doorways below 2^20: every odd 1 < n < 2^20 enters the known loop through one pass-one number
DOORWAYS_2_20 = {5: 491853, 341: 19819, 85: 12317, 21845: 231, 5461: 42, 349525: 21, 21: 1, 1365: 1, 87381: 1, 1398101: 1}


def test_doorways() -> None:
    door = Counter(doorway(n) for n in range(3, 1 << 20, 2))
    assert door == Counter(DOORWAYS_2_20)
    assert set(door) <= set(pass_one(1 << 21))
    assert sum(door.values()) == (1 << 19) - 1
    assert doorway(1) is None and doorway(21) == 21 and doorway(27) == 5


# ---------------------------------------------------------------------------
# L2: the passes (the backward tree of 1)
# ---------------------------------------------------------------------------


def test_odd_steps_table_matches_iteration() -> None:
    t = odd_steps_table(1 << 14)
    assert all(t[(n - 1) // 2] == odd_steps_to_one(n) for n in range(1, 1 << 14, 2))
    assert odd_steps_to_one(27) == 41 and odd_steps_to_one(837799) == 195


def test_closure_rule() -> None:
    # pass d = pass of the next odd number + 1: the closure rule as a recursion
    t = odd_steps_table(1 << 16)
    for n in range(3, 1 << 16, 2):
        s = syracuse(n)
        assert t[(n - 1) // 2] == 1 + odd_steps_to_one(s)


#: (N, last survivor, its pass, mean pass rounded to 2 decimals)
LAST_SURVIVORS = [
    (1 << 10, 871, 65, 22.21), (1 << 12, 3711, 87, 27.49), (1 << 14, 13255, 101, 32.04),
    (1 << 16, 52527, 125, 36.49), (1 << 18, 230631, 164, 41.36), (1 << 20, 837799, 195, 46.15),
]


def test_last_survivors_and_means() -> None:
    for N, n, d, mean in LAST_SURVIVORS:
        assert last_survivor(N) == (n, d)
        t = odd_steps_table(N)
        assert round(sum(t) / len(t), 2) == mean
    assert last_survivor(1000) == (871, 65)


def test_survivors_below_1000() -> None:
    passes = (0, 1, 2, 5, 10, 20, 40, 60, 64, 65)
    assert [survivors_after(1000, d) for d in passes] == [332, 329, 324, 296, 231, 140, 78, 3, 1, 0]
    assert [survivors_after(1000, d, t0=False) for d in passes] == [499, 495, 486, 444, 340, 206, 109, 3, 1, 0]
    t = odd_steps_table(1000)
    assert [2 * i + 1 for i, s in enumerate(t) if s > 60] == [703, 871, 937]
    assert sum(1 for n in range(1, 1000, 2) if n % 3 == 0) == 167


def test_pass_counts_are_polylogarithmic() -> None:
    h = pass_histogram(1 << 20)
    assert [h[d] for d in range(0, 8)] == [1, 9, 34, 78, 176, 309, 508, 871]
    h10 = pass_histogram(1 << 10)
    assert [h10[d] for d in range(1, 6)] == [4, 9, 10, 15, 17]
    # the proved bound: at most C(floor(log2 N) + 2d, d) numbers below N at pass d
    for k, hist in ((10, h10), (20, h)):
        assert all(hist[d] <= math.comb(k + 2 * d, d) for d in range(0, 40))
    assert (math.comb(22, 1), math.comb(24, 2)) == (22, 276)
    # and the product identity behind it: 2^X <= 4^d n along every path to 1
    for n in range(3, 1 << 14, 2):
        d = X = 0
        x = n
        while x != 1:
            x, e = syracuse_with_exponent(x)
            d += 1
            X += e
        assert 2**X <= 4**d * n


def test_pass_two_closed_form() -> None:
    t = odd_steps_table(1 << 20)
    assert pass_two_closed_form(1 << 20) == [2 * i + 1 for i, s in enumerate(t) if s == 2]
    assert pass_two_closed_form(1 << 20)[:6] == [3, 13, 53, 113, 213, 227]


RECORDS = [
    (1, 0), (3, 2), (7, 5), (9, 6), (25, 7), (27, 41), (73, 42), (97, 43), (129, 44), (171, 45),
    (231, 46), (313, 47), (327, 52), (703, 62), (871, 65), (1161, 66), (2463, 76), (2919, 79),
    (3711, 87), (6171, 96), (10971, 98), (13255, 101), (17647, 102), (23529, 103), (26623, 113),
    (34239, 114), (35655, 119), (52527, 125), (77031, 129), (106239, 130),
]


def test_pass_records() -> None:
    assert pass_records(110_000) == RECORDS


# ---------------------------------------------------------------------------
# L4: the shadow of the verified region
# ---------------------------------------------------------------------------


def test_shadow_exact_small() -> None:
    s = shadow_survival(0, 6)
    assert s == [Fraction(1, 2), Fraction(3, 8), Fraction(1, 4), Fraction(13, 64), Fraction(19, 128), Fraction(1, 8)]
    assert shadow_survival(1, 1) == [Fraction(3, 4)] and shadow_survival(5, 1) == [Fraction(63, 64)]
    f = shadow_survival_float(0, 6)
    assert all(abs(a - float(b)) < 1e-15 for a, b in zip(f, s))


def test_shadow_word_model_matches_numbers() -> None:
    # odd n just above V = 2^40 (a stand-in for 2^71): share whose orbit stays >= V for k odd steps
    V = 1 << 40
    exact = shadow_survival(0, 6)
    for k in range(1, 7):
        tot = stay = 0
        for n in range(V + 1, V + (1 << 17), 2):
            x, ok = n, True
            for _ in range(k):
                x = syracuse(x)
                if x < V:
                    ok = False
                    break
            tot += 1
            stay += ok
        assert Fraction(stay, tot) == exact[k - 1]
    # and 2 bits above V: n near 4V
    exact2 = shadow_survival(2, 4)
    for k in range(1, 5):
        tot = stay = 0
        for n in range(4 * V + 1, 4 * V + (1 << 17), 2):
            x, ok = n, True
            for _ in range(k):
                x = syracuse(x)
                if x < V:
                    ok = False
                    break
            tot += 1
            stay += ok
        assert Fraction(stay, tot) == exact2[k - 1]


#: crossed-out share 1 - survival, rounded to 4 places: rows h, columns k
SHADOW_K = (1, 2, 5, 10, 20, 50, 100, 200, 400)
SHADOW_TABLE = {
    0: (0.5000, 0.6250, 0.8516, 0.9355, 0.9807, 0.9987, 1.0000, 1.0000, 1.0000),
    1: (0.2500, 0.3750, 0.6914, 0.8527, 0.9531, 0.9966, 0.9999, 1.0000, 1.0000),
    5: (0.0156, 0.0391, 0.2036, 0.4501, 0.7549, 0.9754, 0.9992, 1.0000, 1.0000),
    10: (0.0005, 0.0018, 0.0252, 0.1228, 0.4170, 0.8995, 0.9958, 1.0000, 1.0000),
    20: (0.0000, 0.0000, 0.0002, 0.0031, 0.0504, 0.5517, 0.9580, 0.9998, 1.0000),
    40: (0.0000, 0.0000, 0.0000, 0.0000, 0.0001, 0.0385, 0.5628, 0.9911, 1.0000),
    60: (0.0000, 0.0000, 0.0000, 0.0000, 0.0000, 0.0004, 0.1099, 0.8934, 1.0000),
}
#: (h, k for 50 %, 99 %, 99.9 % crossed out)
SHADOW_STEPS = {0: (1, 27, 54), 1: (3, 37, 67), 5: (12, 63, 97), 10: (23, 87, 123), 20: (47, 127, 169), 40: (95, 198, 246), 60: (144, 264, 317)}


def test_shadow_table() -> None:
    for h, row in SHADOW_TABLE.items():
        s = shadow_survival_float(h, 400)
        assert tuple(round(1 - s[k - 1], 4) for k in SHADOW_K) == row
    for h, (k50, k99, k999) in SHADOW_STEPS.items():
        s = shadow_survival_float(h, 400)
        first = lambda p: next(i + 1 for i, v in enumerate(s) if 1 - v >= p)  # noqa: E731
        assert (first(0.5), first(0.99), first(0.999)) == (k50, k99, k999)
    ex = shadow_survival(10, 50)
    fl = shadow_survival_float(10, 50)
    assert all(abs(float(a) - b) < 1e-12 for a, b in zip(ex, fl))


def test_shadow_rate_is_lambda_over_three() -> None:
    a = math.log2(3)
    assert abs(shadow_rate() - 0.946504576832584) < 1e-12
    # the Cramer form min_t 3^t / (2^{t+1} - 1) at 2^{t+1} = a/(a-1)
    t = math.log2(a / (a - 1)) - 1
    assert abs(3**t / (2 ** (t + 1) - 1) - shadow_rate()) < 1e-12
    assert all(3 ** (t + e) / (2 ** (t + e + 1) - 1) >= shadow_rate() for e in (-0.2, -0.01, 0.01, 0.2))
    # long-run decay of the exact survival, k^-3/2 removed, approaches lambda/3
    s = shadow_survival_float(0, 1200)
    rate = math.exp((math.log(s[1199]) - math.log(s[599])) / 600) / (600 / 1200) ** (1.5 / 600)
    assert abs(rate - shadow_rate()) < 1e-4


# ---------------------------------------------------------------------------
# L5: rational loops through every class except the multiples of 3
# ---------------------------------------------------------------------------


def test_rational_loops_are_loops() -> None:
    for B in range(1, 12):
        for w in compositions(B):
            members = rational_loop(w)  # raises unless the word and the closure check out
            assert all(x.denominator % 2 == 1 and x.numerator % 2 == 1 for x in members)
            assert all(x.numerator % 3 != 0 for x in members)
    assert rational_loop((2,)) == [Fraction(1)]
    assert rational_loop((1,)) == [Fraction(-1)]
    assert rational_loop((1, 2)) == [Fraction(-5), Fraction(-7)]
    assert sorted(rational_loop((1, 1, 1, 2, 1, 1, 4))) == [-91, -61, -55, -41, -37, -25, -17]


#: (a, b) -> smallest B at which rational loops with B halvings hit every open class mod 2^a 3^b
COVER_B = {
    (1, 0): 1, (2, 0): 2, (3, 0): 3, (4, 0): 4, (5, 0): 5, (6, 0): 6, (7, 0): 7,
    (1, 1): 2, (2, 1): 3, (3, 1): 4, (4, 1): 5, (5, 1): 6, (6, 1): 7, (7, 1): 8,
    (1, 2): 5, (2, 2): 7, (3, 2): 8, (4, 2): 9, (5, 2): 10, (6, 2): 11, (7, 2): 12,
    (1, 3): 8, (2, 3): 9, (3, 3): 11, (4, 3): 12, (5, 3): 13, (6, 3): 14, (7, 3): 15,
}


def test_rational_loops_cover_every_open_class() -> None:
    for (a, b), bneed in COVER_B.items():
        m = 2**a * 3**b
        open_classes = {r for r in range(m) if r % 2 == 1 and (b == 0 or r % 3 != 0)}
        hit = classes_hit(m, bneed)
        assert hit == open_classes
        if bneed > 1:
            assert classes_hit(m, bneed - 1) != open_classes


#: (r, m) -> (first word found, the loop member in class r mod m), as quoted on the page
LOOP_EXAMPLES = {
    (7, 16): ((1, 1, 2), Fraction(-19, 11)),
    (15, 16): ((1,), Fraction(-1)),
    (5, 12): ((2, 1), Fraction(-7)),
    (7, 12): ((1, 2), Fraction(-5)),
    (17, 36): ((2, 1, 1), Fraction(-29, 11)),
    (29, 36): ((2, 1), Fraction(-7)),
    (13, 32): ((3,), Fraction(1, 5)),
    (65, 144): ((2, 2, 1), Fraction(37, 5)),
}


def test_loop_through_class_examples() -> None:
    for (r, m), (w, x) in LOOP_EXAMPLES.items():
        assert loop_through_class(r, m, 14) == (w, x)
        assert x.numerator * pow(x.denominator, -1, m) % m == r and rational_loop_point(w) == x
    assert loop_through_class(3, 9, 10) is None and loop_through_class(21, 36, 10) is None


def test_positive_integer_rational_loops() -> None:
    pos = set()
    for B in range(1, 16):
        for w in compositions(B):
            x = rational_loop_point(w)
            if x > 0 and x.denominator == 1:
                pos.add(x)
    assert pos == {1}


# ---------------------------------------------------------------------------
# the strategy filter (docs/FILTER.md), test A as a harness
# ---------------------------------------------------------------------------


def test_filter_a_q5_harness() -> None:
    # the reach-the-known-loop rule is sound at q = 5: no member of another q = 5 cycle ever
    # reaches the fixed point 1, so the rule never crosses one out -- and never finishes.
    cyc = find_cycles(5, 5000)
    assert (1,) in [c.elements for c in cyc] and len(cyc) >= 3
    others = [c for c in cyc if c.elements != (1,)]
    for c in others:
        for n in c.elements:
            seen, x = set(), n
            while x not in seen:
                seen.add(x)
                x = syracuse(x, 5)
            assert 1 not in seen
    assert syracuse_with_exponent(1, 5) == (1, 3)
