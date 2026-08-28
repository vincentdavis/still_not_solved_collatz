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
