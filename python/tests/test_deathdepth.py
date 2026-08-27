"""``d(M)`` -- the sieve's death depth, and its exact tail.

Every number here is reproduced from scratch by the package.  The point of the
quantity is `Collatz/Equivalence.lean`: a counterexample to Collatz is exactly
an odd ``M > 1`` with ``d(M) = infinity``.
"""

from __future__ import annotations

import pytest

from collatz_maxodd.deathdepth import (
    death_depth,
    death_depth_congruence_only,
    exact_tail,
    tail_ratios,
)

# a_k with P(d >= k) = a_k / 3^k, computed exactly over a full residue period.
A_K = [1, 2, 3, 6, 10, 22, 50, 104, 254]


def test_exact_tail_matches_fixture():
    assert exact_tail(9) == A_K


def test_tail_is_an_exact_rational_at_two_magnitudes():
    """d(M) depends only on M mod 3^k, so the period scan is base-independent."""
    assert exact_tail(8, base=10 ** 12) == exact_tail(8, base=10 ** 18) == A_K[:8]


def test_deepest_known_survivor():
    """M = 3077 is the deepest survivor below 20000."""
    assert death_depth(3077) == 48
    assert max(death_depth(M) for M in range(3, 20000, 2)) == 48


@pytest.mark.parametrize("M,expected", [(27, 0), (9, 0), (3, 0), (17, 3), (5, 1)])
def test_small_values(M, expected):
    assert death_depth(M) == expected


def test_multiples_of_three_die_immediately():
    """3 | M means M has no odd predecessor at all (T0)."""
    assert all(death_depth(M) == 0 for M in range(3, 4000, 2) if M % 3 == 0)


def test_congruence_only_model_agrees_for_large_M():
    """This agreement is WHY the distribution is magnitude-independent."""
    assert all(
        death_depth(10 ** 18 + 1 + 2 * i) == death_depth_congruence_only(10 ** 18 + 1 + 2 * i)
        for i in range(4000)
    )


def test_ratios_are_below_the_tree_growth_constant():
    """a_k/a_(k-1) is conjectured to approach lambda = 2.83951 from below."""
    ratios = list(tail_ratios(A_K))
    assert all(1.0 < r < 2.83951 for r in ratios)


def test_rejects_even_and_nonpositive():
    for bad in (0, -3, 4):
        with pytest.raises(ValueError):
            death_depth(bad)


# a_k from the 3-adic tree DFS; agrees with the full-period scan where they overlap.
A_K_DEEP = [1, 2, 3, 6, 10, 22, 50, 104, 254, 538, 1302, 3202, 7553, 19206,
            44732, 113034]


def test_surviving_residue_count_matches_period_scan():
    from collatz_maxodd.deathdepth import surviving_residue_count
    assert surviving_residue_count(9) == A_K[:9] == exact_tail(9)


def test_surviving_residue_count_deep():
    from collatz_maxodd.deathdepth import surviving_residue_count
    assert surviving_residue_count(16) == A_K_DEEP


def test_a_k_never_exceeds_the_vector_count():
    """Each admissible vector pins one residue, so a_k <= N_k -- with equality
    only while no M has two distinct chains (k <= 3)."""
    from collatz_maxodd.backtree import count_admissible_halving_vectors
    from collatz_maxodd.deathdepth import surviving_residue_count
    a = surviving_residue_count(14)
    N = [count_admissible_halving_vectors(k) for k in range(1, 15)]
    assert all(x <= y for x, y in zip(a, N))
    assert a[:3] == N[:3]
    assert all(x < y for x, y in zip(a[3:], N[3:]))
