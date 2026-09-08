"""The word -> residue map ``Phi``, its collisions, and the Sturmian sign law.

The objects
-----------
An *admissible word* of length ``k`` is ``(b_1, ..., b_k)``, integers
``b_t >= 1``, whose partial sums ``B_t`` obey the caps ``B_t <= floor(t*alpha)``
(``alpha = log2 3``; symbolic large-``M`` mode of ``backtree``).  ``N_k``
counts them.  The residue map is

    Phi_k(b) = c_k * 2^{-B_k}  (mod 3^k),      c_t = 2^{b_t} c_{t-1} + 3^{t-1}

REALIZATION (docs/WORDS.md W1; the uncapped core is Wirsching's, LNM 1681):
every word is live at exactly the one residue ``Phi_k(b)``, and the depth-k
congruence implies every prefix congruence.  So live (word, residue) pairs
number ``N_k``, the survivor set of the death-depth sieve is ``image(Phi_k)``,
``a_k = |image|``, and ALL arithmetic content of the sieve beyond lattice-path
combinatorics is the fiber (collision) structure ``N_k - a_k``.

The sign law
------------
With ``jump(k) = floor((k+1)*alpha) - floor(k*alpha)`` (the Sturmian word of
``alpha``, values 1 or 2):

    sign(N_k^2 - N_{k-1} N_{k+1})  =  +1  iff  jump(k) = 1        (checked)

* PROVED (Theorem A, docs/WORDS.md): the jump-1 direction, every ``k >= 2`` --
  via the exact identity ``D_k = N_k N_{k-1} ((sbar_k - sbar_{k-1}) - jump(k))``,
  log-concavity of the slack profiles ``g_k``, and the geometric moment bound
  ``E[X(X-1)] < 2 mu^2`` for discrete log-concave laws.
* CONJECTURE (B): the jump-2 direction is EQUIVALENT to the deficit bound
  ``c_n = mu(mu+1) - Var < 2``; verified to n ~ 1200, sup ~ 1.47.
* The law itself: zero violations on independent OEIS A100982 data to k = 2216.

Collisions (docs/WORDS.md C-lemmas)
-----------------------------------
Whether two words with common prefix length ``j`` collide depends on their
TAILS ONLY (prefix-free criterion); the prefix enters only through cap slack.
Window-1 rule: two last letters collide iff they have equal parity, giving the
closed-form bound  ``a_k <= E_k = 2 N_{k-1} - [cap increment at k = 1] N_{k-2}``.
Every fixed-window bound has exactly ``N``'s growth rate (no-rate-gain), so
these improve constants, never the rate: ``mu <= lambda`` stays the only
proved rate bound.

PRIOR ART / NOVELTY.  Realization core: Wirsching (via Monks et al.
arXiv:1204.3904 Sec. 4); forward mirror: Terras 1976.  The Sturmian caps, the
image count ``a_k``, the sign law, and the collision classification were not
found in the literature (audit 2026-08-30; nearest named objects: Terras's
coefficient stopping time conjecture and Garner 1985's coalescence pairs,
both structurally different).  Zarubin's A100982 recursion is an OEIS comment
labeled "Theorem 1" with NO published proof located; here it is a checked
CONJECTURE, not an input.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb
from typing import Iterator, Sequence

from .backtree import (
    admissible_halving_vectors,
    c_constant,
    floor_bound,
)

__all__ = [
    "jump",
    "phi",
    "words",
    "fibers",
    "n_words",
    "word_profiles",
    "word_profile",
    "slack_moments",
    "sign_law_violations",
    "deficit_in_range",
    "window1_bound",
    "zarubin_rhs",
    "bump_last",
    "binomial_moments",
    "moment_step",
    "mu_c",
    "dyadic_live_mass",
]


def jump(k: int) -> int:
    """``floor((k+1)*alpha) - floor(k*alpha)`` -- the Sturmian letter, 1 or 2."""
    return floor_bound(k + 1) - floor_bound(k)


def phi(bs: Sequence[int]) -> int:
    """``Phi_k(b) = c_k * 2^{-B_k} mod 3^k`` -- the unique residue where ``b`` is live.

    Defined for EVERY word with ``b_t >= 1`` (admissibility is the sieve's
    budget, not a hypothesis of realization -- W1).
    """
    k = len(bs)
    if k == 0:
        raise ValueError("empty word")
    mod = 3**k
    return c_constant(bs) * pow(2, -sum(bs), mod) % mod


def words(k: int) -> Iterator[tuple[int, ...]]:
    """All admissible words of length ``k`` (symbolic caps)."""
    return admissible_halving_vectors(k)


def fibers(k: int) -> dict[int, list[tuple[int, ...]]]:
    """``Phi_k``-fibers over admissible words: residue -> its live words.

    ``len(fibers(k)) == a_k`` and ``sum(len(f)) == N_k``; multi-word fibers
    are the collisions.  Enumerative -- intended for ``k <= 13`` or so.
    """
    out: dict[int, list[tuple[int, ...]]] = {}
    for w in words(k):
        out.setdefault(phi(w), []).append(w)
    return out


def n_words(K: int) -> list[int]:
    """``[N_1, ..., N_K]`` by the O(K^2) prefix-sum DP over ``B``."""
    out: list[int] = []
    dist = {1: 1}  # length 1: cap(1) = 1 forces b_1 = 1
    out.append(1)
    for j in range(2, K + 1):
        lim = floor_bound(j)
        nxt: dict[int, int] = {}
        running = 0
        for B in range(j, lim + 1):
            running += dist.get(B - 1, 0)
            if running:
                nxt[B] = running
        dist = nxt
        out.append(sum(dist.values()))
    return out[:K]


def word_profiles(K: int) -> list[dict[int, int]]:
    """``[f_1, ..., f_K]``: partial-sum profiles ``{B: #words with B_k = B}``, one DP pass.

    Support of ``f_k`` is exactly ``{k, ..., floor(k*alpha)}`` and each profile
    is log-concave (Theorem A's L2; strict at every internal point as computed).
    """
    out: list[dict[int, int]] = [{1: 1}]
    for j in range(2, K + 1):
        lim = floor_bound(j)
        nxt: dict[int, int] = {}
        running = 0
        for B in range(j, lim + 1):
            running += out[-1].get(B - 1, 0)
            if running:
                nxt[B] = running
        out.append(nxt)
    return out[:K]


def word_profile(k: int) -> dict[int, int]:
    """``f_k`` alone; see :func:`word_profiles`."""
    return word_profiles(k)[-1]


def slack_moments(k: int) -> tuple[int, int, int]:
    """``(S0, S1, S2)``: count, sum, sum-of-squares of the slack ``X = cap - B``.

    The sign law is a second-moment statement about these: with
    ``W_n = 2*S1^2 + S1*S0 - S2*S0`` (integer form of ``c_n = mu(mu+1) - Var``
    times ``S0^2``), Theorem A's L3 proves ``W_n > 0`` and Conjecture B says
    ``W_n < 2*S0^2``.
    """
    m = floor_bound(k)
    s0 = s1 = s2 = 0
    for B, cnt in word_profile(k).items():
        x = m - B
        s0 += cnt
        s1 += cnt * x
        s2 += cnt * x * x
    return s0, s1, s2


def sign_law_violations(K: int) -> list[int]:
    """Indices ``2 <= k <= K-1`` violating the sign law (expected: none).

    Law: ``sign(N_k^2 - N_{k-1} N_{k+1}) = +1 iff jump(k) = 1``, strict
    (a zero difference also counts as a violation).
    """
    N = n_words(K)
    bad = []
    for k in range(2, K):
        d = N[k - 1] ** 2 - N[k - 2] * N[k]
        if (d > 0) != (jump(k) == 1) or d == 0:
            bad.append(k)
    return bad


def deficit_in_range(K: int) -> bool:
    """``0 < c_n < 2`` for ``2 <= n <= K`` in exact integers.

    The lower half is PROVED (Theorem A's L3); the upper half is Conjecture B,
    whose truth for all ``n`` would complete the sign law.
    """
    profiles = word_profiles(K)
    for n in range(2, K + 1):
        m = floor_bound(n)
        s0 = s1 = s2 = 0
        for B, cnt in profiles[n - 1].items():
            x = m - B
            s0 += cnt
            s1 += cnt * x
            s2 += cnt * x * x
        w = 2 * s1 * s1 + s1 * s0 - s2 * s0
        if not 0 < w < 2 * s0 * s0:
            return False
    return True


def window1_bound(k: int) -> int:
    """``E_k = 2 N_{k-1} - [cap(k) - cap(k-1) = 1] * N_{k-2}`` (PROVED: a_k <= E_k).

    The window-1 collision rule: same-prefix extensions collide iff their last
    letters share parity, so each (k-1)-prefix contributes min(slack, 2)
    residues; the cap-hitting bijection (W4) turns the count into this closed
    form.  ``N_0 = 1``.
    """
    if k < 2:
        return 1
    N = n_words(max(k - 1, 1))
    n1 = N[k - 2]
    n2 = N[k - 3] if k >= 3 else 1
    inc = floor_bound(k) - floor_bound(k - 1)
    return 2 * n1 - (n2 if inc == 1 else 0)


def zarubin_rhs(k: int, N: Sequence[int]) -> int:
    """RHS of Zarubin's (unproved) A100982 recursion for ``N_k``.

    ``N_k = sum_{m=1..k} (-1)^(m-1) C(floor((k-m+1)*alpha) + m - 1, m) N_{k-m}``
    with ``N_0 = 1`` and ``N = [N_1, N_2, ...]``.  Stated as "Theorem 1" in an
    OEIS comment (Zarubin, 2015) with no proof or reference attached -- checked
    exactly to k = 250 by two independent agents, but a CONJECTURE here.
    """
    total = 0
    for m in range(1, k + 1):
        nprev = 1 if k - m == 0 else N[k - m - 1]
        term = comb(floor_bound(k - m + 1) + m - 1, m) * nprev
        total += term if m % 2 == 1 else -term
    return total


def bump_last(bs: Sequence[int], j: int) -> tuple[int, ...]:
    """The last-letter bump ``(b_1, ..., b_k + j)`` (requires ``b_k + j >= 1``).

    Bump law (W3): even ``j`` preserves ``Phi_k`` mod ``3^k`` unconditionally;
    odd ``j`` shifts exactly the top 3-adic digit (``Phi`` preserved mod
    ``3^{k-1}``, moved mod ``3^k``).  The mod-``3^k`` shadow of the classical
    merging of ``z`` and ``4z + 1``.
    """
    if not bs or bs[-1] + j < 1:
        raise ValueError("last letter must stay >= 1")
    return tuple(bs[:-1]) + (bs[-1] + j,)


# ---------------------------------------------------------------------------
# exact level dynamics (docs/WORDS.md section 11)
# ---------------------------------------------------------------------------


def binomial_moments(n: int, K: int) -> list[int]:
    """``[M_0, ..., M_{K-1}]`` with ``M_k = sum_x C(x, k) g_n(x)`` -- binomial
    moments of the slack profile (``M_0 = N_n``, ``M_1 = N_n * mu_n``).

    Combinatorially ``M_k`` counts (admissible word, k-subset of its slack
    units); in tails, ``M_k = sum_{a_1..a_k >= 1} T_n(a_1 + ... + a_k)``.
    """
    m = floor_bound(n)
    return [sum(comb(m - B, k) * c for B, c in word_profile(n).items())
            for k in range(K)]


def moment_step(M: Sequence[int], j: int) -> list[int]:
    """The PROVED level dynamics on binomial moments (one fewer returned):

        jump 1 (tail sum U):          M'_k = M_k + M_{k+1}
        jump 2 (head-duplicated DU):  M'_k = M_{k-1} + 2 M_k + M_{k+1}   (M_{-1} = 0)

    Equivalent to the GF cocycle ``G_{k+1}(z) = (N_k - z^j G_k(z)) / (1 - z)``.
    """
    K = len(M) - 1
    if j == 1:
        return [M[k] + M[k + 1] for k in range(K)]
    return [(M[k - 1] if k else 0) + 2 * M[k] + M[k + 1] for k in range(K)]


def mu_c(n: int) -> tuple[Fraction, Fraction]:
    """``(mu_n, c_n)`` exactly: mean slack and deficit ``c = 2(mu^2 - m_2)``."""
    N, M1, M2 = binomial_moments(n, 3)
    mu = Fraction(M1, N)
    return mu, 2 * (mu * mu - Fraction(M2, N))


def dyadic_live_mass(n: int) -> Fraction:
    """``sum over admissible words of 2^{-B_n(w)}`` -- the 2-adic measure of
    the live word tree.  PROVED conservation law (Kraft-type):

        dyadic_live_mass(n) + sum_{i=1}^{n-1} N_i 2^{-floor((i+1) alpha)} = 1/2,

    because each admissible ``i``-word loses exactly ``2^{-m_{i+1}}`` of mass to
    over-cap extensions at step ``i+1``, independently of its own ``B_i``.
    """
    return sum(Fraction(c, 2**B) for B, c in word_profile(n).items())
