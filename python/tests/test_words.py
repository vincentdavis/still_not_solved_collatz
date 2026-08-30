"""Witnesses for docs/WORDS.md: the word -> residue lemmas, the sign law, collisions.

Every PROVED lemma there gets its computational witness here; the two central
CONJECTURES (deficit bound B, transfer fact TF) get exact-range checks clearly
scoped as such.  All fixtures below were computed independently by at least two
agents (prover + adversarial checker) before being pinned.
"""

from __future__ import annotations

import pytest

from collatz_maxodd.backtree import c_constant, floor_bound
from collatz_maxodd.deathdepth import live_chains, surviving_residues
from collatz_maxodd.words import (
    bump_last,
    deficit_in_range,
    fibers,
    jump,
    n_words,
    phi,
    sign_law_violations,
    slack_moments,
    window1_bound,
    word_profiles,
    words,
    zarubin_rhs,
)

# fixtures: all double-verified (docs/WORDS.md, audit 2026-08-30)
N_21 = [1, 2, 3, 7, 12, 30, 85, 173, 476, 961, 2652, 8045, 17637, 51033,
        108950, 312455, 663535, 1900470, 5936673, 13472296, 39993895]
A_24 = [1, 2, 3, 6, 10, 22, 50, 104, 254, 538, 1302, 3202, 7553, 19206, 44732,
        113034, 262243, 660954, 1693714, 4204015, 10995110, 26812105,
        69626820, 182840849]  # docs/DEATH_DEPTH.md
NEG1_CHAINS = [1, 1, 1, 2, 2, 2, 3, 3, 4, 4, 5, 7, 8]  # chains at -1, k = 1..13
FIBER_HIST_12 = {1: 1181, 2: 864, 3: 339, 4: 408, 5: 197, 6: 86, 7: 66,
                 8: 39, 9: 8, 10: 14}


def _exact_chain(r: int, w: tuple[int, ...]) -> bool:
    """All ``len(w)`` backward divisions from ``r`` exact (liveness, W0)."""
    y = r
    for b in w:
        num = (1 << b) * y - 1
        if num % 3 != 0:
            return False
        y = num // 3
    return True


def _admissible(w: tuple[int, ...]) -> bool:
    B = 0
    for t, b in enumerate(w, start=1):
        B += b
        if b < 1 or B > floor_bound(t):
            return False
    return True


# ---------------------------------------------------------------------------
# W0/W4(1): caps and the Sturmian jump word
# ---------------------------------------------------------------------------


def test_cap_is_exact_and_jump_word_is_sturmian():
    """floor(t*alpha) via bit_length; gaps in {1,2}; no '11', no '222'."""
    for t in range(1, 2001):
        f = floor_bound(t)
        assert 2**f <= 3**t < 2 ** (f + 1)
    js = [jump(k) for k in range(1, 1001)]
    assert set(js) <= {1, 2}
    assert all(js[i] + js[i + 1] >= 3 for i in range(len(js) - 1))  # no '11'
    assert all(sum(js[i:i + 3]) <= 5 for i in range(len(js) - 2))   # no '222'


# ---------------------------------------------------------------------------
# W1 realization: every word live at exactly one residue; prefixes collapse
# ---------------------------------------------------------------------------


def test_realization_every_word_pins_one_residue():
    """Brute force over ALL residues: live set == {phi(w)}, admissible or not."""
    import itertools

    for k in range(1, 6):
        mod = 3**k
        pool = list(words(k)) + [
            w for w in itertools.product((1, 2, 3, 4), repeat=k)
        ][:40]
        for w in pool:
            assert {r for r in range(mod) if _exact_chain(r, w)} == {phi(w)}


def test_realization_prefix_congruences():
    """phi(w) mod 3^t == phi(w[:t]) -- the depth-k congruence implies them all."""
    for k in range(2, 11):
        for w in words(k):
            for t in range(1, k):
                assert phi(w) % 3**t == phi(w[:t])


def test_survivor_set_is_the_image_of_phi():
    """S_k = image(Phi_k) over admissible words, as SETS, k <= 10."""
    levels = surviving_residues(10)
    for k in range(1, 11):
        assert sorted({phi(w) for w in words(k)}) == levels[k - 1]


def test_word_counts_and_collision_census():
    """N_k fixture; a_k = #fibers; collisions; first collision; k=12 histogram."""
    assert n_words(21) == N_21
    for k in range(1, 13):
        fib = fibers(k)
        assert sum(len(f) for f in fib.values()) == N_21[k - 1]
        assert len(fib) == A_24[k - 1]
    fib4 = fibers(4)
    multi = {r: f for r, f in fib4.items() if len(f) > 1}
    assert multi == {80: [(1, 1, 1, 1), (1, 1, 1, 3)]}  # -1 mod 81
    hist: dict[int, int] = {}
    for f in fibers(12).values():
        hist[len(f)] = hist.get(len(f), 0) + 1
    assert hist == FIBER_HIST_12


# ---------------------------------------------------------------------------
# W2 slope-blindness: the all-ones chain and the -1 witness
# ---------------------------------------------------------------------------


def test_slope_blindness():
    """phi(1^k) = -1 mod 3^k; c = 3^k - 2^k; min slope unique; -1's chain counts."""
    for k in range(1, 14):
        ones = (1,) * k
        assert c_constant(ones) == 3**k - 2**k
        assert phi(ones) == 3**k - 1
        assert len(live_chains(3**k - 1, 0, 0, k)) == NEG1_CHAINS[k - 1]
    for k in range(1, 13):
        assert sum(1 for w in words(k) if sum(w) == k) == 1


# ---------------------------------------------------------------------------
# W3 bump law: even last-letter bumps preserve phi; odd bumps shift the top digit
# ---------------------------------------------------------------------------


def test_naive_bump_is_false():
    """(1) is admissible, (3) is not: bumping can break the last cap."""
    assert _admissible((1,)) and not _admissible((3,))


def test_bump_law():
    """Even j: phi preserved mod 3^k.  Odd j: moved mod 3^k, preserved mod 3^{k-1}."""
    for k in range(2, 11):
        mod = 3**k
        for w in words(k):
            for j in (-2, 2, 4):
                if w[-1] + j >= 1:
                    assert phi(bump_last(w, j)) == phi(w)
            for j in (-1, 1, 3):
                if w[-1] + j >= 1:
                    p = phi(bump_last(w, j))
                    assert p != phi(w)
                    assert (p - phi(w)) % 3 ** (k - 1) == 0
                    assert (p - phi(w)) % mod != 0


def test_cap_saturation():
    """Every survivor carries a chain with B >= f(k)-1; the -1 is sharp from k=2."""
    for k in range(1, 13):
        best = {r: max(sum(w) for w in f) for r, f in fibers(k).items()}
        deficit = max(floor_bound(k) - b for b in best.values())
        assert min(best.values()) >= floor_bound(k) - 1
        assert deficit == (0 if k == 1 else 1)
    assert fibers(2)[8] == [(1, 1)]  # the k=2 witness stuck at f(2)-1


# ---------------------------------------------------------------------------
# W4(2) extension count, W5 leafless, W6 forced doubling
# ---------------------------------------------------------------------------


def test_extension_count():
    """#{words with B_k = f(k)} = N_{k-1}: unique cap-hitting extension."""
    for k in range(1, 14):
        n_prev = 1 if k == 1 else N_21[k - 2]
        assert sum(1 for w in words(k) if sum(w) == floor_bound(k)) == n_prev


def test_leafless_and_forced_doubling():
    """Children >= 1 always; >= 2 exactly at jump-2 levels; pinned witnesses."""
    levels = surviving_residues(12)
    for k in range(1, 12):
        kids: dict[int, int] = {r: 0 for r in levels[k - 1]}
        for r2 in levels[k]:
            kids[r2 % 3**k] += 1
        low = min(kids.values())
        assert low >= 1
        assert low >= 2 if jump(k) == 2 else low == 1
        if k == 2:
            assert [r2 for r2 in levels[2] if r2 % 9 == 2] == [20]
        if k == 4:
            singles = sorted(r for r, c in kids.items() if c == 1)
            assert singles == [44, 74]
    for k in range(1, 24):
        if jump(k) == 2:
            assert A_24[k] >= 2 * A_24[k - 1]
    assert [k for k in range(1, 24) if jump(k) == 2 and A_24[k] == 2 * A_24[k - 1]] == [1, 3]


# ---------------------------------------------------------------------------
# Theorem A and Conjecture B: the Sturmian sign law
# ---------------------------------------------------------------------------


def test_sign_law_holds_to_400():
    """sign(N_k^2 - N_{k-1}N_{k+1}) = +1 iff jump(k) = 1; never zero.  k <= 399."""
    assert sign_law_violations(400) == []


def test_mean_increment_identity():
    """D_k = N_{k-1}S_k - N_kS_{k-1} - jump(k) N_k N_{k-1}, exact, k <= 199."""
    K = 200
    profiles = word_profiles(K)
    N = [sum(p.values()) for p in profiles]
    S = [sum(B * c for B, c in p.items()) for p in profiles]
    for k in range(2, K - 1):
        d = N[k - 1] ** 2 - N[k - 2] * N[k]
        assert d == N[k - 2] * S[k - 1] - N[k - 1] * S[k - 2] - jump(k) * N[k - 1] * N[k - 2]
        # branching identity: N_{k+1} = f(k+1) N_k - S_k
        assert N[k] == floor_bound(k + 1) * N[k - 1] - S[k - 1]


def test_four_case_moment_criterion():
    """sign(D_k) from slack moments at n = k-1 (Theorem A's L4), exact, k <= 199."""
    K = 200
    profiles = word_profiles(K)
    N = [sum(p.values()) for p in profiles]
    for k in range(3, K - 1):
        n = k - 1
        m = floor_bound(n)
        s0 = s1 = s2 = 0
        for B, cnt in profiles[n - 1].items():
            x = m - B
            s0 += cnt
            s1 += cnt * x
            s2 += cnt * x * x
        j, jp = jump(n), jump(k)
        crit = (2 * s1 * s1 + 2 * (j - jp) * s1 * s0
                + j * (j + 1 - 2 * jp) * s0 * s0 - (s2 - s1) * s0)
        d = N[k - 1] ** 2 - N[k - 2] * N[k]
        assert (d > 0) == (crit > 0) and d != 0 and crit != 0
        assert s1 + j * s0 == N[k - 1]  # N_k = N_n * E[X + j]


def test_slack_profiles_strictly_log_concave():
    """g_k > 0 on full interval support, strictly log-concave inside; k <= 120."""
    for k, prof in enumerate(word_profiles(120), start=1):
        lo, hi = k, floor_bound(k)
        assert sorted(prof) == list(range(lo, hi + 1))
        vals = [prof[B] for B in range(lo, hi + 1)]
        for i in range(1, len(vals) - 1):
            assert vals[i] ** 2 > vals[i - 1] * vals[i + 1]


def test_deficit_bracket_conjecture_B_range():
    """0 < c_n < 2 in exact integers, n <= 300.  Lower half PROVED; upper is
    Conjecture B (== the open jump-2 half of the sign law)."""
    assert deficit_in_range(300)
    s0, s1, s2 = slack_moments(5)  # pinned: g_5 = (7, 4, 1)
    assert (s0, s1, s2) == (12, 6, 8)
    assert 2 * s1 * s1 + s1 * s0 - s2 * s0 == 48  # W_5 = 48 < 2*144


# ---------------------------------------------------------------------------
# Collisions: window-1 rule, closed-form bound, minimal prefix, rigidity
# ---------------------------------------------------------------------------


def test_window1_parity_rule():
    """Same-prefix last letters collide iff equal parity, k <= 9."""
    for k in range(2, 10):
        by_prefix: dict[tuple[int, ...], list[tuple[int, int]]] = {}
        for w in words(k):
            by_prefix.setdefault(w[:-1], []).append((w[-1], phi(w)))
        for exts in by_prefix.values():
            for b1, p1 in exts:
                for b2, p2 in exts:
                    assert (p1 == p2) == (b1 % 2 == b2 % 2)


def test_window1_closed_form_bound():
    """E_k = 2N_{k-1} - [inc=1]N_{k-2}; a_k <= E_k; pinned values."""
    assert window1_bound(13) == 13438
    assert window1_bound(15) == 84429
    assert window1_bound(16) == 217900 == 2 * N_21[14]
    for k in range(2, 17):
        assert A_24[k - 1] <= window1_bound(k)


def test_minimal_common_prefix_is_three():
    """Every colliding pair has common prefix >= 3; j=3 pairs are (1,1,1)x{1,3}."""
    for k in range(4, 11):
        for f in fibers(k).values():
            for i in range(len(f)):
                for w2 in f[i + 1:]:
                    w1 = f[i]
                    j = 0
                    while j < k and w1[j] == w2[j]:
                        j += 1
                    assert j >= 3
                    if j == 3:
                        assert w1[:3] == (1, 1, 1)
                        assert {w1[3], w2[3]} == {1, 3}


def test_fixed_length_exponent_sums_injective():
    """Sum 3^{s-1} 2^{E_s} injective at FIXED length (variable length fails: 38)."""
    from itertools import combinations

    assert 2**5 + 3 * 2**1 == 2**3 + 3 * 2**2 + 9 * 2**1 == 38  # the counterexample
    for r in range(1, 5):
        seen: dict[int, tuple[int, ...]] = {}
        for combo in combinations(range(12, 0, -1), r):
            v = sum(3**s * 2**e for s, e in enumerate(combo))
            assert v not in seen, (combo, seen[v])
            seen[v] = combo


def test_reconvergent_pair_fixture():
    """First genuinely interior rewrite (k=11): admissible, colliding, tiny suffix."""
    w1 = (1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1)
    w2 = (1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1)
    assert _admissible(w1) and _admissible(w2)
    assert phi(w1) == phi(w2)
    b1 = [sum(w1[:t]) for t in range(1, 12)]
    b2 = [sum(w2[:t]) for t in range(1, 12)]
    assert b1[9:] == b2[9:] and b1[:9] != b2[:9]  # equal sums from position 10


def test_lte_normalization_valuations():
    """v_3(2^{2*3^{m-1}} - 1) = m -- the letter-reduction engine (C-lemma 5)."""
    for m in range(1, 8):
        v, x = 0, 2 ** (2 * 3 ** (m - 1)) - 1
        while x % 3 == 0:
            v, x = v + 1, x // 3
        assert v == m


def test_unconstrained_windows_saturate_units():
    """Image of G_m over uncapped tails = ALL units mod 3^m (why caps are essential)."""
    from itertools import combinations

    for m in range(1, 4):
        mod = 3**m
        period = 2 * 3 ** (m - 1)
        image = set()
        for combo in combinations(range(1, period + m + 1), m):
            image.add(sum(3**s * pow(2, -d, mod) for s, d in enumerate(combo)) % mod)
        assert image == {u for u in range(mod) if u % 3 != 0}


# ---------------------------------------------------------------------------
# The a_k side: phase lock and the transfer fact (both CONJECTURE, exact range)
# ---------------------------------------------------------------------------


def test_collision_series_and_phase_lock():
    """N_k - a_k extended terms; collision-rate increment sign-locked to jump."""
    diffs = [N_21[k] - A_24[k] for k in range(21)]
    assert diffs[:12] == [0, 0, 0, 1, 2, 8, 35, 69, 222, 423, 1350, 4843]
    assert diffs[18:] == [4242959, 9268281, 28998785]
    for k in range(8, 22):  # rate_k > rate_{k-1}  iff  cap increment at k is 2
        rises = A_24[k - 1] * N_21[k - 2] < A_24[k - 2] * N_21[k - 1]
        assert rises == (jump(k - 1) == 2)


def test_transfer_fact_exact_range():
    """TF: a-ratio strictly between 1 and (N-ratio)^2, same side; k <= 23.
    Given the N sign law, TF implies the a_k sign law (both open in general)."""
    N = n_words(24)
    assert N[:21] == N_21
    for k in range(2, 24):
        dn = N[k - 1] ** 2 - N[k - 2] * N[k]
        da = A_24[k - 1] ** 2 - A_24[k - 2] * A_24[k]
        assert dn != 0 and da != 0
        assert (dn > 0) == (da > 0)
        # |a-ratio deviation| < |N-ratio deviation|^2, cross-multiplied
        lhs = A_24[k - 1] ** 2 * N[k - 2] ** 2 * N[k] ** 2
        rhs = N[k - 1] ** 4 * A_24[k - 2] * A_24[k]
        assert (lhs < rhs) == (dn > 0)


def test_zarubin_recursion_witness():
    """Zarubin's OEIS 'Theorem 1' (no published proof found): exact to k = 120."""
    N = n_words(121)
    for k in range(1, 121):
        assert zarubin_rhs(k, N) == N[k - 1]


if __name__ == "__main__":
    pytest.main([__file__, "-q"])
