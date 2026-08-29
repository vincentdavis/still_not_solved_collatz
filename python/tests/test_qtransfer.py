"""The q-transfer theorem and the strategy filter (docs/FILTER.md).

THE THEOREM (test A's engine).  For every odd ``q`` with ``3 ∤ q``, either sign:

    S_k(q) = q · S_k(1)   (mod 3^k),   hence   a_k(q) = a_k(1)   for all k.

Proof (ten lines, docs/FILTER.md).  A halving vector is live for ``M`` at
parameter ``q`` iff ``3^t | 2^{B_t} M − c_t(q)`` for ``t ≤ k`` plus the q-free
caps ``2^{B_t} ≤ 3^t``.  The constant is linear in ``q``: ``c_t(q) = q·c_t(1)``
from ``c_t = 2^{b_t} c_{t−1} + 3^{t−1} q``, ``c_0 = 0``.  So ``M`` is live for
``q`` iff ``q^{−1}M`` is live for ``1``, and multiplication by the unit ``q``
bijects ``Z/3^k``.  ∎

CONSEQUENCE.  Every statistic of the magnitude-free sieve — the ``a_k``, the
growth rate ``μ``, the whole death-rate bracket — is IDENTICAL between ``q = 1``
and ``q = 5``.  And ``q = 5`` has a real cycle, ``{19, 31, 49}``.  So no theorem
whose hypotheses are expressible in magnitude-free sieve statistics alone can
prove ``q = 1`` cyclelessness: instantiated at ``q = 5`` it would prove a
falsehood.  (Scope: the MAGNITUDE-FREE sieve of docs/DEATH_DEPTH.md.  The exact
sieve ``y ≤ M`` transfers only along ``M ↦ qM``, which does not preserve
integrality in reverse — that is precisely where magnitude enters, and why real
``q = 5`` cycles have no ``q = 1`` partners.)

The same scaling governs the FORWARD (2-adic) sieve — confirmed here, which
makes its 1.80-bit saturation ceiling q-invariant too.

The Lean side checks the transfer exhaustively at ``k ≤ 4``
(``lean/Collatz/QTransfer.lean``); this file goes to ``k = 10`` and adds the
negative-``q`` cases Lean's ``Nat``-encoded residues cover via ``3^k − |q|``.
"""

from __future__ import annotations

import pytest

from collatz_maxodd.deathdepth import (
    live_chains,
    surviving_residue_count,
    surviving_residues,
    survives,
)
from collatz_maxodd.sieve import surviving_residues_mod2

QS = (5, 7, 11, 25, -1, -5)
K_MAX = 10

A_K = [1, 2, 3, 6, 10, 22, 50, 104, 254, 538]  # docs/DEATH_DEPTH.md, k = 1..10


@pytest.fixture(scope="module")
def s1() -> list[list[int]]:
    return surviving_residues(K_MAX, 1)


# ---------------------------------------------------------------------------
# the theorem itself
# ---------------------------------------------------------------------------


def test_q1_sets_match_the_counting_dfs(s1):
    """The set-valued DFS and the counting DFS agree — and agree with a_k."""
    assert [len(level) for level in s1] == surviving_residue_count(K_MAX) == A_K


@pytest.mark.parametrize("q", QS)
def test_qtransfer_set_equality(q, s1):
    """S_k(q) = q·S_k(1) as SETS mod 3^k — not just equal counts."""
    sq = surviving_residues(K_MAX, q)
    for k in range(1, K_MAX + 1):
        mod = 3**k
        assert sq[k - 1] == sorted((q * r) % mod for r in s1[k - 1])


@pytest.mark.parametrize("q", QS)
def test_qtransfer_counts(q):
    """Hence a_k(q) = a_k(1): the sieve's statistics are exactly q-blind."""
    assert [len(level) for level in surviving_residues(K_MAX, q)] == A_K


@pytest.mark.parametrize("q", QS + (1,))
def test_witness_minus_q_survives_every_depth(q):
    """−q mod 3^k survives at every depth: the transfer image of the −1 witness."""
    for k in range(1, 13):
        assert survives((-q) % 3**k, k, q)


def test_transfer_is_not_an_artifact_of_the_scan_order():
    """live_chains and the DFS see the same survivors at k = 6, q = 7."""
    mod = 3**6
    via_chains = sorted(r for r in range(mod) if survives(r, 6, 7))
    assert via_chains == surviving_residues(6, 7)[5]


# ---------------------------------------------------------------------------
# the corollary, stated with the referee's correction
# ---------------------------------------------------------------------------


def test_q5_cycle_max_dies_in_the_magnitude_free_sieve():
    """49 = max{19,31,49} (a REAL q=5 cycle) dies at depth 8.

    The no-go must therefore be phrased as: statistics-only hypotheses are
    q-uniform and hence false at q = 5 — NOT as "the cycle survives the sieve".
    It does not: its own halving vector violates the magnitude-free cap
    (the very counterexample GROUND_TRUTH §6 ✗1 records), so the cycle is
    invisible to the asymptotic sieve, living below its regime.
    """
    for k in range(1, 8):
        assert survives(49 % 3**k, k, 5)
    assert not survives(49 % 3**8, 8, 5)


def test_q5_max_and_its_q1_partner_share_a_fate():
    """The transfer pairs 49 (q=5) with 5⁻¹·49 (q=1): both die at depth 8."""
    mod = 3**8
    partner = (pow(5, -1, mod) * 49) % mod
    assert survives(partner % 3**7, 7, 1)
    assert not survives(partner, 8, 1)


# ---------------------------------------------------------------------------
# test B: the forward (2-adic) sieve mirrors the same scaling
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("q", (5, 7, 11, 25))
def test_forward_sieve_q_transfer(q):
    """S^fwd_a(q) = q·S^fwd_a(1) mod 2^a — the mirror prediction, confirmed.

    (check_q restricts the forward sieve to q > 0 by design: its kill logic
    uses d_j > 0.  The magnitude-free backward sieve above has no such need.)
    """
    for a in range(1, 13):
        mod = 1 << a
        base = surviving_residues_mod2(a, 1)[1]
        assert surviving_residues_mod2(a, q)[1] == tuple(
            sorted((q * r) % mod for r in base)
        )


# ---------------------------------------------------------------------------
# test B continued: the 3x−1 sign audit
# ---------------------------------------------------------------------------

CYCLES_3X_MINUS_1 = ([1], [5, 7], [17, 25, 37, 55, 41, 61, 91])


def _step_3x_minus_1(n: int) -> tuple[int, int]:
    m = 3 * n - 1
    v = (m & -m).bit_length() - 1
    return m >> v, v


@pytest.mark.parametrize("cycle", CYCLES_3X_MINUS_1)
def test_3x_minus_1_cycles_are_real(cycle):
    """The three classical 3x−1 cycles close, with the stated elements."""
    n, elements, B = cycle[0], [], 0
    for _ in cycle:
        elements.append(n)
        n, v = _step_3x_minus_1(n)
        B += v
    assert n == cycle[0]
    assert sorted(elements) == sorted(cycle)


@pytest.mark.parametrize("cycle", CYCLES_3X_MINUS_1)
def test_sign_audit_t7_direction_flips(cycle):
    """q = −1 flips exactly the positivity-derived half: 2^B < 3^L.

    For q > 0, T7 gives c_L > 0 hence 2^B > 3^L.  For q = −1 the constant is
    negative and the inequality reverses — on all three real cycles.
    """
    n, B = cycle[0], 0
    for _ in cycle:
        n, v = _step_3x_minus_1(n)
        B += v
    assert 2**B < 3 ** len(cycle)


def test_sign_audit_congruences_survive():
    """The general-q congruence M ≡ q (mod 4) holds VERBATIM at q = −1.

    Both nontrivial maxima are ≡ 3 ≡ −1 (mod 4); the trivial cycle {1} is the
    M = |q| fixed-point case that the q > 0 theory also excepts (M > q).
    So the audit's boundary is clean: congruence-shaped conclusions are
    sign-blind, and only positivity (c_L > 0 and its consequences) is not.
    """
    for cycle in CYCLES_3X_MINUS_1[1:]:
        assert max(cycle) % 4 == (-1) % 4


def test_sign_audit_min_and_max_structure():
    """Structure at the extremes survives the sign flip for M > |q|.

    Out of the max: 2^{b} x = 3M − 1 with x ≤ M forces 2^b ≥ 3 − 1/M > 2,
    so b ≥ 2.  Out of the min: 2^b y = 3m − 1 with y ≥ m forces 2^b < 3,
    so b = 1.  Checked on both nontrivial cycles.
    """
    for cycle in CYCLES_3X_MINUS_1[1:]:
        big, small = max(cycle), min(cycle)
        _, v_max = _step_3x_minus_1(big)
        _, v_min = _step_3x_minus_1(small)
        assert v_max >= 2
        assert v_min == 1


# ---------------------------------------------------------------------------
# guard: the exact sieve does NOT residue-transfer (where magnitude enters)
# ---------------------------------------------------------------------------


def test_exact_sieve_scope_guard():
    """49 has death-depth ∞ in the EXACT q=5 sieve (it is in a cycle) yet dies
    at depth 8 in the magnitude-free one.  The transfer theorem is about the
    latter only; conflating the two sieves is the §4a mistake."""
    from collatz_maxodd.deathdepth import death_depth

    assert death_depth(49, q=5, cap=60) == 60  # hits the cap: chain never ends
    assert not survives(49 % 3**8, 8, 5)
