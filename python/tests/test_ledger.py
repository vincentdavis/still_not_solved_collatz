"""The cycle ledger identity, and the census counts web/ledger.html cites (docs/LEDGER.md).

The minimum's mirror gates themselves are tested in test_bounds.py and formalized in
lean/Collatz/Minimum.lean; here only the counts quoted on the page are pinned.
"""

from __future__ import annotations


def test_ledger_identity(census):
    """Around every cycle, ascents = descents, hence E = 4*O + 2*L*q (E: even members, O: odd)."""
    for c in census:
        q, O, E, A, D = c.q, sum(c.elements), 0, 0, 0
        for n in c.elements:
            m = 3 * n + q
            A += 2 * n + q
            while m % 2 == 0:
                E += m
                D += m // 2
                m //= 2
        assert A == D and E == 4 * O + 2 * c.L * q, c


def test_min_gate_counts_quoted_on_the_page(multi):
    """1681 minima entered by >= 2 halvings; 434 cycles with m >= q leave m by one halving, m = q+2 (mod 4)."""
    entered = checked = 0
    for c in multi:
        m = c.min_element
        i = c.elements.index(m)
        assert c.forward_halvings[(i - 1) % c.L] >= 2, c
        entered += 1
        if m >= c.q:
            checked += 1
            assert c.forward_halvings[i] == 1 and (m - c.q - 2) % 4 == 0 and m % 3, c
    assert (entered, checked) == (1681, 434)
