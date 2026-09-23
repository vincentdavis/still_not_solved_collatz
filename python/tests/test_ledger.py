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


def test_pairs_factor_and_balance_is_not_closure():
    """(2n+1, D(n)) = ((2^{x+1}s+1)/3, s(2^x-1)) with s = S(n); zero-sum sets abound, chained ones do not."""
    from itertools import combinations

    from collatz_maxodd.syracuse import syracuse_with_exponent

    for n in range(1, 4001, 2):
        s, x = syracuse_with_exponent(n, 1)
        assert 3 * n + 1 - s == s * (2**x - 1) and 3 * (2 * n + 1) == 2 ** (x + 1) * s + 1
        assert s % 2 == 1 and s % 3 == (1 if x % 2 == 0 else 2)
    net = {n: syracuse_with_exponent(n, 1)[0] - n for n in range(1, 400, 2)}
    pairs = [(a, b) for a, b in combinations(net, 2) if net[a] + net[b] == 0]
    S = lambda n: syracuse_with_exponent(n, 1)[0]
    assert len(pairs) == 83 and not any(S(a) == b and S(b) == a for a, b in pairs)
    net3 = {n: net[n] for n in range(1, 120, 2)}
    triples = [t for t in combinations(net3, 3) if sum(net3[v] for v in t) == 0]
    chained = [t for t in triples if {S(t[0]), S(t[1]), S(t[2])} == set(t)]
    assert len(triples) == 408 and chained == []
