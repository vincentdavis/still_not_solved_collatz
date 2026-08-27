"""The documented edge cases, asserted as the *reasons* hypotheses cannot be dropped.

``docs/GROUND_TRUTH.md`` lists three:

1. ``(q=17, cycle {1,5})`` and ``(q=23, cycle {7,11})``, offered as showing that
   ``M > q`` is required for **T1 and T2**.
2. single-odd cycles (``q=1: {1}``, ``q=7: {7}``), offered as showing ``L >= 2``
   is required for T2.
3. ``q=7, M=11, L=2`` with ``b_2 = 3``, offered as showing T5 needs ``L >= 3``.

The audit found the doc partly wrong, and these tests pin down exactly what each
witness does and does not show:

* the two ``M < q`` cycles are **not** counterexamples to T1 -- they satisfy it.
  They are counterexamples to **T2 only**.
* ``L >= 2`` for T2 is redundant once ``M > q`` is assumed, because ``M = q``
  forces ``L = 1``.  The fixed points are still genuine T2 counterexamples for
  the weaker hypothesis ``M >= q``.
* the ``L >= 3`` hypothesis for T5 is **FALSE** as stated; the ``q=7, M=11``
  witness sits exactly on the sharp size threshold ``7M = 11q``, and
  ``q=37, (53, 49, 23)`` has ``L = 3`` and ``M > q`` and still ``b_2 = 3``.
"""

from __future__ import annotations

import pytest

from collatz_maxodd.cycles import Cycle, find_cycles


def get(q: int, elements: tuple[int, ...]) -> Cycle:
    for c in find_cycles(q, max(elements) + 2):
        if c.elements == elements:
            return c
    raise AssertionError(f"cycle {elements} not found for q={q}")


# ---------------------------------------------------------------- edge case 1


@pytest.mark.parametrize(
    "q, elements, b1",
    [
        (17, (5, 1), 2),  # the doc's {1,5}, normalised to start at M = 5
        (23, (11, 7), 2),  # the doc's {7,11}, normalised to start at M = 11
    ],
)
def test_M_less_than_q_breaks_T2_but_NOT_T1(q: int, elements: tuple[int, ...], b1: int):
    c = get(q, elements)
    assert c.M < c.q and c.L == 2

    # T2 FAILS here: b_1 != 1, so M's in-cycle predecessor is not (2M - q)/3.
    assert c.b1 == b1 != 1
    assert c.y(1) == (((1 << b1) * c.M - c.q) // 3)

    # T1 HOLDS here.  The doc's claim that these refute T1 is wrong.
    assert (3 * c.M + c.q) % 4 == 0
    assert c.forward_halvings[0] >= 2

    # In fact M < q gives the STRONGER conclusion 8 | 3M + q.
    assert (3 * c.M + c.q) % 8 == 0


def test_the_doc_s_two_witnesses_explicitly():
    """Spelled out: 3*5+17 = 32 (v2 = 5) and 3*11+23 = 56 (v2 = 3).  Both >= 2."""
    assert 3 * 5 + 17 == 32 and (32 & -32).bit_length() - 1 == 5
    assert 3 * 11 + 23 == 56 and (56 & -56).bit_length() - 1 == 3


# ---------------------------------------------------------------- edge case 2


@pytest.mark.parametrize("q", [1, 7, 5, 17, 23, 37])
def test_fixed_points_are_the_L_equals_1_obstruction_to_T2(q: int):
    """A fixed point has M = q/(2^b - 3) <= q and b_1 >= 2, so T2's b_1 = 1 fails."""
    fps = [c for c in find_cycles(q, 5 * q) if c.L == 1]
    assert fps
    for c in fps:
        b = c.forward_halvings[0]
        assert b >= 2 and c.b1 == b != 1
        assert c.M * ((1 << b) - 3) == c.q
        assert c.M <= c.q
        assert c.y(1) == c.M  # the "predecessor" of M is M itself -- it wraps


def test_L_ge_2_is_redundant_given_M_gt_q():
    """M = q forces L = 1, so 'M > q' already implies 'L >= 2'."""
    for q in range(1, 400, 2):
        if q % 3 == 0:
            continue
        for c in find_cycles(q, 4 * q + 10):
            if c.M > c.q:
                assert c.L >= 2
            if c.M == c.q:
                assert c.L == 1


# ---------------------------------------------------------------- edge case 3


def test_q7_M11_is_a_SIZE_coincidence_not_a_wrap():
    """q=7, M=11, L=2, b_2 = 3.  The doc blames the wrap; the real cause is 7M = 11q."""
    c = get(7, (11, 5))
    assert (c.q, c.M, c.L) == (7, 11, 2)
    assert c.b(1) == 1 and c.b(2) == 3

    # The exact T5 inequality holds with EQUALITY here: 11*7 = 77 = (2^3+3)*7.
    b2 = c.b(2)
    lhs = c.M * ((1 << (1 + b2)) - 9)
    rhs = ((1 << b2) + 3) * c.q
    assert lhs == rhs == 77

    # Equivalently M sits exactly on the sharp threshold 11q/7.
    assert 7 * c.M == 11 * c.q


def test_L_ge_3_does_NOT_rescue_T5():
    """FALSE row: L >= 3 and M > q still allows b_2 = 3.  Witness q=37, (53,49,23)."""
    c = get(37, (53, 49, 23))
    assert c.L == 3 and c.M == 53 > c.q == 37
    assert c.b(1) == 1 and c.b(2) == 3 > 2
    assert c.y(2) == 49 < c.M  # no wrap: y_2 is a genuine third element
    # ...and it is below the sharp threshold, which is what actually matters:
    assert 7 * c.M <= 11 * c.q  # 371 <= 407


def test_more_L_ge_3_counterexamples_to_the_doc_hypothesis():
    """Not an isolated accident."""
    found = []
    for q in range(1, 400, 2):
        if q % 3 == 0:
            continue
        for c in find_cycles(q, 3000):
            if c.L >= 3 and c.M > c.q and c.b(2) > 2:
                found.append((c.q, c.M, c.L, c.b(2)))
    assert len(found) >= 5, found
    assert (37, 53, 3, 3) in found
    # every one of them is at or below the sharp threshold M <= 11q/7
    for q, m, _L, _b2 in found:
        assert 7 * m <= 11 * q, (q, m)


# ------------------------------------------------- the user's seed intuitions


def test_seed_intuition_7_cannot_be_the_largest():
    """'7 can't be the largest, because 3*7+1 = 22 -> next odd is 11 > 7.'  Correct."""
    from collatz_maxodd.sieve import can_be_max_odd
    from collatz_maxodd.syracuse import syracuse

    assert 3 * 7 + 1 == 22 and syracuse(7, 1) == 11 > 7
    v = can_be_max_odd(7, 1)
    assert not v and "x_1 = 11" in v.reason
    assert 7 % 4 == 3  # exactly T1


def test_seed_intuition_about_11_has_the_wrong_reason():
    """'To reach 11 you need a bigger odd' is FALSE -- 7 -> 11 and 7 < 11.

    11 is nevertheless excluded, by T1: 11 = 3 (mod 4).
    """
    from collatz_maxodd.syracuse import smaller_predecessor, syracuse

    assert syracuse(7, 1) == 11 and 7 < 11
    # LEMMA-U: 11 has exactly one odd predecessor below itself, and it is 7.
    assert smaller_predecessor(11, 1) == (1, 7)
    # But T1 excludes 11 anyway.
    assert 11 % 4 == 3
    from collatz_maxodd.sieve import t1_ok

    assert not t1_ok(11, 1)


def test_seed_intuition_two_even_hops_back():
    """'We need only look two even hops back' -- true for q=1 with M >= 2 (T5).

    For q = 1 the sharp threshold 11q/7 = 11/7 < 2, so every q=1 cycle maximum
    other than M = 1 satisfies b_2 <= 2.  The statement is vacuous today.
    """
    from collatz_maxodd.backtree import floor_rule_threshold

    # depth 2 threshold is 1, i.e. the rule bites for every M >= 2
    assert floor_rule_threshold(2, 1) == 1
    q1 = find_cycles(1, 100_000)
    assert [c.elements for c in q1] == [(1,)]
