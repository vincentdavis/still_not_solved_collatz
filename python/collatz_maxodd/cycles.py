"""Exhaustive search for ``S_q``-cycles: the empirical test bed.

``find_cycles(q, bound)`` returns **every** cycle of the ``3n+q`` Syracuse map
whose largest odd element ``M`` satisfies ``M <= bound``.  The completeness
argument is simple: every element of such a cycle is itself an odd number
``<= bound``, so the cycle is discovered when the search starts at that element,
and the orbit never has to leave ``[1, bound]`` to find it.  Orbits that climb
above ``bound`` are abandoned -- they cannot be inside a cycle whose max is
``<= bound``.

Only positive cycles are searched (``q > 0``, odd, ``3 | q`` false).
"""

from __future__ import annotations

from dataclasses import dataclass, field

from .syracuse import check_q, syracuse_with_exponent

__all__ = ["Cycle", "find_cycles", "find_cycles_multi"]


@dataclass(frozen=True, slots=True)
class Cycle:
    """A closed orbit of odd numbers under ``S_q``, normalised to start at ``M``.

    Attributes
    ----------
    q:
        The offset of the ``3n+q`` map.
    elements:
        The odd elements in forward order starting at the maximum:
        ``(M, S_q(M), S_q^2(M), ...)``, of length ``L``.
    forward_halvings:
        ``(a_1, ..., a_L)`` with ``a_j = v2(3 * elements[j-1] + q)``; so
        ``elements[j] = (3*elements[j-1] + q) / 2^{a_j}`` cyclically.
    """

    q: int
    elements: tuple[int, ...]
    forward_halvings: tuple[int, ...] = field(repr=False)

    @property
    def L(self) -> int:
        """Number of odd elements in the cycle."""
        return len(self.elements)

    @property
    def M(self) -> int:
        """Largest odd element."""
        return self.elements[0]

    @property
    def min_element(self) -> int:
        """Smallest odd element."""
        return min(self.elements)

    @property
    def B(self) -> int:
        """Total number of halvings around the cycle, ``B = a_1 + ... + a_L``."""
        return sum(self.forward_halvings)

    @property
    def backward_halvings(self) -> tuple[int, ...]:
        """``(b_1, ..., b_L)`` read backwards from ``M``: ``b_j = a_{L+1-j}``.

        ``3 * y_j + q = 2^{b_j} * y_{j-1}`` with ``y_0 = M``.
        """
        return tuple(reversed(self.forward_halvings))

    @property
    def backward_elements(self) -> tuple[int, ...]:
        """``(y_0, y_1, ..., y_{L-1}) = (M, ...)`` walking backwards from ``M``."""
        return (self.elements[0],) + tuple(reversed(self.elements[1:]))

    @property
    def b1(self) -> int:
        """``b_1``: the number of halvings on the step *into* ``M``."""
        return self.backward_halvings[0]

    def y(self, k: int) -> int:
        """The ``k``-th backward element from ``M``, wrapping around the cycle."""
        return self.backward_elements[k % self.L]

    def b(self, k: int) -> int:
        """``b_k`` for ``k >= 1``, wrapping around the cycle."""
        if k < 1:
            raise ValueError("k must be >= 1")
        return self.backward_halvings[(k - 1) % self.L]

    def __str__(self) -> str:  # pragma: no cover - cosmetic
        return (
            f"q={self.q} L={self.L} M={self.M} B={self.B} "
            f"elements={list(self.elements)} a={list(self.forward_halvings)}"
        )


def _normalise(orbit: list[int], q: int) -> Cycle:
    """Rotate a raw cycle so that it starts at its maximum, and attach exponents."""
    i = max(range(len(orbit)), key=lambda j: orbit[j])
    elems = tuple(orbit[i:] + orbit[:i])
    halvings = tuple(syracuse_with_exponent(x, q)[1] for x in elems)
    return Cycle(q=q, elements=elems, forward_halvings=halvings)


def find_cycles(q: int, bound: int) -> list[Cycle]:
    """All ``S_q``-cycles whose maximum odd element is ``<= bound``.

    Complete for that class (see module docstring).  Sorted by ``(M, L)``.
    """
    check_q(q)  # rejects even q, 3 | q, and q <= 0
    resolved: set[int] = set()
    cycles: dict[tuple[int, ...], Cycle] = {}

    for start in range(1, bound + 1, 2):
        if start in resolved:
            continue
        path: dict[int, int] = {}
        x = start
        while True:
            if x in resolved:
                break
            if x in path:
                idx = path[x]
                orbit = [v for v, i in sorted(path.items(), key=lambda kv: kv[1]) if i >= idx]
                cyc = _normalise(orbit, q)
                cycles.setdefault(cyc.elements, cyc)
                break
            path[x] = len(path)
            x = syracuse_with_exponent(x, q)[0]
            if x > bound:
                break
        resolved.update(path)

    return sorted(cycles.values(), key=lambda c: (c.M, c.L))


def find_cycles_multi(
    q_values: list[int] | range, bound: int
) -> list[Cycle]:
    """``find_cycles`` over many ``q``; non-admissible ``q`` are skipped silently."""
    out: list[Cycle] = []
    for q in q_values:
        if q <= 0 or q % 2 == 0 or q % 3 == 0:
            continue
        out.extend(find_cycles(q, bound))
    return out
