"""The three explorations proposed in the review, and what they returned.

Two of the three refute the guess that motivated them.  These tests pin the
refutations, not just the numbers -- if a future change made the guesses come
out true, that would be a bug in the data, not a discovery.
"""

from __future__ import annotations

import json
import pathlib
from collections import defaultdict

from collatz_maxodd.census import primitive_cycles, total_halvings
from collatz_maxodd.structure import reachable_set

ROOT = pathlib.Path(__file__).resolve().parents[2]
ADM = [q for q in range(1, 601, 2) if q % 3]


def _explore():
    return json.loads((ROOT / "web" / "explore.json").read_text())


# ---------------------------------------------------------------------------
# 1. Where the over-dispersion lives -- the guess was backwards
# ---------------------------------------------------------------------------


def test_over_dispersion_is_concentrated_in_the_m_gt_q_regime():
    """Guessed: the excess sits in m <= q.  It is the other way round.

    m > q cycles are rarer (they need the +q term to be a small correction)
    but far more clustered.  That is the uncomfortable direction: the regime
    that most resembles q = 1 is the MORE over-dispersed one.
    """
    d = _explore()["dispersion"]
    assert d["m_gt_q"]["var_over_mean"] > d["all"]["var_over_mean"]
    assert d["all"]["var_over_mean"] > d["m_le_q"]["var_over_mean"]
    # and the m>q population really is the rarer one
    assert d["m_gt_q"]["mean"] < d["m_le_q"]["mean"]


def test_the_quotient_k_is_always_odd_and_prime_to_three():
    """k = (2^B - 3^L)/q has the same admissibility q does.

    2^B - 3^L is odd (even minus odd) and never 0 mod 3 (since 2^B is not),
    so k inherits both.  An exact hit is k = 1.
    """
    seen = set()
    for q in ADM:
        for L, M, el in primitive_cycles(q, 40 * q):
            B = total_halvings(el, q)
            d = 2 ** B - 3 ** L
            assert d % q == 0
            k = d // q
            assert k % 2 == 1 and k % 3 != 0, (q, L, B, k)
            seen.add(k)
    assert 1 in seen                      # exact hits occur
    assert not any(k % 2 == 0 for k in seen)


# ---------------------------------------------------------------------------
# 2. The tail rate -- Fekete runs the wrong way for what was wanted
# ---------------------------------------------------------------------------


def test_a_k_is_supermultiplicative_not_sub():
    """Guessed: a relaxation would give a rigorous UPPER bound on the rate.

    a_k is supermultiplicative (a_{j+k} >= a_j a_k) and emphatically not
    submultiplicative, so Fekete gives lim = sup and therefore a rigorous
    LOWER bound -- and no upper bound at all by this route.
    """
    a = json.loads((ROOT / "web" / "asym.json").read_text())["a_k"]
    n = len(a)
    ratios = [a[j + k - 1] / (a[j - 1] * a[k - 1])
              for j in range(1, n) for k in range(1, n - j + 1)]
    assert min(ratios) >= 1.0            # supermultiplicative
    assert max(ratios) > 1.0             # not submultiplicative
    f = _explore()["fekete"]
    assert f["supermultiplicative"] and not f["submultiplicative"]


def test_the_rigorous_lower_bound_is_weaker_than_the_published_bracket():
    """The bracket's lower end is a model FIT; the rigorous bound is wider.

    sup a_k^(1/k) / 3 = 0.7364 is a genuine lower bound on the tail rate.
    The published 0.8958 is where the fitted models put it.  Worth keeping
    straight: [0.896, 0.947] is not an interval of proof.
    """
    f = _explore()["fekete"]
    lo_fit, hi = f["published_bracket"]
    assert f["best_rigorous_lower_rate"] < lo_fit < hi
    assert f["best_rigorous_lower_rate"] > 0.7


# ---------------------------------------------------------------------------
# 3. The Hercher pincer -- this one worked
# ---------------------------------------------------------------------------


def test_reachable_set_is_flat_in_M():
    """|R(M)| shows no growth from 10^5 to 10^10 on the surviving class."""
    rows = _explore()["pincer"]["rows"]
    meds = [r["median"] for r in rows]
    assert max(meds) - min(meds) <= 2
    assert all(r["mean"] < 8 for r in rows)


def test_the_pincer_leaves_nine_orders_of_headroom():
    """L <= |R(O)| is machine-checked; Hercher gives L > 1.375e11.

    So a Collatz cycle maximum needs |R(O)| > 1.375e11.  Nothing observed
    comes within eight orders of magnitude of that, and |R(M)| does not grow.
    """
    p = _explore()["pincer"]
    assert p["worst_seen"] < p["hercher_L"]
    assert p["headroom"] > 10 ** 8
    # spot-check the claim directly rather than trusting the file
    worst = max(len(reachable_set(M, 1))
                for M in range(10 ** 9 + 1, 10 ** 9 + 8001, 2)
                if M % 36 in (17, 29))
    assert worst < 10 ** 4


def test_a_real_cycle_max_would_be_wildly_atypical():
    """The pincer measures how atypical, not that it is impossible.

    A genuine cycle maximum has |R(O)| >= L by construction, so this is the
    same wall in another disguise -- but it does say a counterexample must be
    ~9 orders of magnitude off a distribution that is otherwise flat.
    """
    # the known q=5 cycle max has |R| = 10 and L = 3: L <= |R(O)| holds
    assert 3 <= len(reachable_set(49, 5)) == 10


# ---------------------------------------------------------------------------
# Supermultiplicativity, PROVED -- see docs/EXPLORE.md.
#
# These check the construction the proof is built on, not just the inequality:
# if the splice ever failed to land in the survivors, or ever collided, the
# proof would be wrong and these would catch it.
# ---------------------------------------------------------------------------


def test_the_splice_lands_in_the_survivors():
    """Claim A: splice(r,j,s,k) survives to depth j+k.

    The two chains concatenate and the size cap composes, because
    2^B <= 3^j and 2^B' <= 3^i give 2^(B+B') <= 3^(j+i).
    """
    from collatz_maxodd.deathdepth import splice, survives

    n = 0
    for j in range(1, 5):
        for k in range(1, 5):
            if j + k > 7:
                continue
            for r in (x for x in range(3 ** j) if survives(x, j)):
                for s in (x for x in range(3 ** k) if survives(x, k)):
                    assert survives(splice(r, j, s, k), j + k), (r, j, s, k)
                    n += 1
    assert n == 108


def test_the_splice_is_injective():
    """Claim B: distinct (r,s) give distinct M.

    r is recovered as M mod 3^j; the canonical chain follows from r; then the
    depth-j endpoint, and hence s, follows from M.  This is the step the
    canonical choice exists for.
    """
    from collatz_maxodd.deathdepth import splice, survives

    for j in range(1, 5):
        for k in range(1, 5):
            if j + k > 7:
                continue
            seen = {}
            for r in (x for x in range(3 ** j) if survives(x, j)):
                for s in (x for x in range(3 ** k) if survives(x, k)):
                    M = splice(r, j, s, k)
                    assert M not in seen, (M, seen.get(M), (r, s))
                    seen[M] = (r, s)


def test_the_splice_is_injective_where_canonicity_actually_bites():
    """Injectivity past j+k = 11 -- the first depth where it could fail.

    A residue can carry several live depth-j chains; below j+k = 11 no M in the
    image does, so a non-canonical implementation would still pass.  At (5,6)
    one does (M = 42443 mod 3^11 has two, ending at 242 and 485 mod 3^6, both
    survivors), so this is the first test that the choice function is load
    bearing rather than decorative.
    """
    from collatz_maxodd.deathdepth import live_chains, splice, survives

    for j, k in ((5, 6), (6, 5), (4, 7)):
        Sj = [r for r in range(3 ** j) if survives(r, j)]
        Sk = [x for x in range(3 ** k) if survives(x, k)]
        Ms = [splice(r, j, x, k) for r in Sj for x in Sk]
        assert len(set(Ms)) == len(Ms), (j, k)
        assert all(survives(M, j + k) for M in Ms), (j, k)
    # and confirm the ambiguity really is present at this depth
    multi = [r for r in range(3 ** 5) if len(live_chains(r, 0, 0, 5)) > 1]
    assert multi, "expected some residue with several live depth-5 chains"


def test_supermultiplicativity_holds_where_we_can_check_it():
    """a_(j+k) >= a_j * a_k -- now a consequence, not an observation."""
    from collatz_maxodd.deathdepth import surviving_residue_count

    a = surviving_residue_count(9)
    for j in range(1, 9):
        for k in range(1, 9 - j + 1):
            assert a[j + k - 1] >= a[j - 1] * a[k - 1], (j, k)


def test_fekete_gives_a_rigorous_lower_bound_on_the_rate():
    """Supermultiplicative + bounded => the limit EXISTS and equals the sup.

    a_k >= 1 and a_k <= 3^k, so a_k^(1/k) is in [1, 3]; Fekete then gives
    lim a_k^(1/k) = sup_k a_k^(1/k).  Every term is therefore a rigorous lower
    bound on the growth, and the best available one comes from k = 24.
    """
    import math

    a = json.loads((ROOT / "web" / "asym.json").read_text())["a_k"]
    assert all(1 <= a[k - 1] <= 3 ** k for k in range(1, len(a) + 1))
    best = max(a[k - 1] ** (1 / k) for k in range(1, len(a) + 1))
    assert best == a[-1] ** (1 / len(a))          # the sup is attained at k=24
    # NB superadditivity does not make a_k^(1/k) monotone -- only the running
    # max is guaranteed to improve.  It happens to be monotone here, but that
    # is data, not the lemma.
    seq = [a[k - 1] ** (1 / k) for k in range(1, len(a) + 1)]
    assert seq == sorted(seq)                     # true for k <= 24, not a theorem
    rate = best / 3
    assert rate > 0.736
    # and it is genuinely below where the fitted models put it
    lo_fit, hi = _explore()["fekete"]["published_bracket"]
    assert rate < lo_fit < hi
    # the upper end stays as it was: a_k <= N_k, so mu <= lambda
    assert hi == pytest_approx(0.9465)


def pytest_approx(x, tol=1e-4):
    class _A:
        def __eq__(self, other):
            return abs(other - x) < tol
    return _A()


# ---------------------------------------------------------------------------
# The upper end, now proved too:  a_k <= N_k <= C(floor(k*alpha), k) <= lambda^k
#
# This closes the bracket.  Unlike GROUND_TRUTH's N_k ~ C*lambda^k*k^(-3/2),
# which is measured, every step here is a bound that holds at every k.
# ---------------------------------------------------------------------------


def test_the_chain_bound_holds_at_every_depth():
    """a_k <= N_k <= C(floor(k*alpha), k) <= lambda^k."""
    import json as _json

    from collatz_maxodd.backtree import chain_bound_holds

    a = _json.loads((ROOT / "web" / "asym.json").read_text())["a_k"]
    for k in range(1, 16):
        assert chain_bound_holds(k, a[k - 1]), k
    for k in range(16, 61):
        assert chain_bound_holds(k), k


def test_the_entropy_step_is_what_makes_it_elementary():
    """C(n,k) <= n^n / (k^k (n-k)^(n-k)), and that is increasing in n.

    From 1 = (p+q)^n >= C(n,k) p^k q^(n-k) at p = k/n.  Evaluated at the real
    point n = k*alpha it is exactly lambda^k, so floor(k*alpha) <= k*alpha
    gives the bound with no asymptotics and no Stirling.
    """
    import math

    alpha = math.log2(3.0)
    lam = alpha ** alpha / (alpha - 1.0) ** (alpha - 1.0)

    def f(n, k):                       # the entropy bound, at real n
        return n ** n / (k ** k * (n - k) ** (n - k))

    for k in range(2, 40):
        n = math.floor(k * alpha)
        assert math.comb(n, k) <= f(n, k) * (1 + 1e-9), k      # entropy bound
        assert f(n, k) <= f(k * alpha, k) * (1 + 1e-9), k      # increasing in n
        assert f(k * alpha, k) == pytest_approx(lam ** k, tol=lam ** k * 1e-9)


def test_the_bracket_is_now_rigorous_at_both_ends():
    """0.7364 <= tail rate <= 0.9465, both ends proved.

    Lower: supermultiplicativity + Fekete (this file, above).
    Upper: a_k <= lambda^k, so mu <= lambda.
    The published [0.8958, 0.9465] sits strictly inside, and its lower end
    remains a model fit -- it is not implied by either bound.
    """
    import math

    from collatz_maxodd.backtree import _LAMBDA

    a = json.loads((ROOT / "web" / "asym.json").read_text())["a_k"]
    lower = max(a[k - 1] ** (1 / k) for k in range(1, len(a) + 1)) / 3
    upper = _LAMBDA / 3
    assert lower == pytest_approx(0.7364)
    assert upper == pytest_approx(0.9465)
    lo_fit, hi_fit = _explore()["fekete"]["published_bracket"]
    assert lower < lo_fit and hi_fit == pytest_approx(upper)
    # every computed a_k respects the upper bound
    assert all(a[k - 1] <= _LAMBDA ** k for k in range(1, len(a) + 1))
