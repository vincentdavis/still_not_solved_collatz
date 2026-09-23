"""A SAT encoding of ``S_q``-cycles: bounded model checking of the cycle equation.

Question: can "there is an ``S_q``-cycle with ``L`` odd elements, all below
``2^W``" be handed to a SAT solver?  Yes.  This module writes that sentence as
CNF (pure Python, no dependencies) and, when ``python-sat`` is installed,
enumerates every model.  ``web/ledger.html`` carries the same encoding in
JavaScript and solves it in the browser with MiniSat.

What it is, honestly.  The encoding is sound and complete *for the box*
``(L, W)``: its models are exactly the cycles with ``L`` odd elements and
maximum ``< 2^W`` (regression-tested against ``find_cycles``).  It says nothing
about the unbounded question, and the box that would matter for ``q = 1`` has
``L > 1.375 x 10^11`` (Hercher 2023 + Barina 2025), far beyond any solver.
Bounded search is where SAT has *not* helped with Collatz; where it has is the
opposite direction -- Yolcu, Aaronson & Heule (JAR 2023) use SAT to search for
termination *certificates* of a rewriting system equivalent to the conjecture.

Encoding (LSB-first bit vectors, Tseitin with constant folding)
--------------------------------------------------------------
* ``n_i`` (``W`` bits, ``i = 0..L-1``): the odd elements in forward order,
  ``n_0`` the maximum.  Unit clauses make every ``n_i`` odd.
* ``t_i = 3 n_i + q`` (``W+2`` bits) by two ripple-carry adders,
  ``n_i + (n_i << 1)`` then ``+ q``.  ``t_i < 2^{W+2}`` whenever ``q < 2^W``,
  so the top carry is dropped soundly.
* ``y_{i,k}`` (``k = 1..W+1``), one-hot: ``y_{i,k}`` means ``v2(t_i) = k``.
  ``y_{i,k}`` implies the low ``k`` bits of ``t_i`` are ``0``, bit ``k`` is ``1``
  and ``n_{i+1} = t_i >> k`` (indices mod ``L``), i.e. ``n_{i+1}`` is the odd
  part of ``3 n_i + q``.
* ``n_i < n_0`` strictly for ``i >= 1``: a cycle's elements are distinct, so
  this fixes the rotation and also excludes a shorter cycle traversed several
  times.  With ``L = 1`` the models are the fixed points ``n(2^b - 3) = q``.
* Optional *gates* (``docs/GROUND_TRUTH.md``): T1, ``M = q (mod 4)``, is one
  unit clause on bit 1 of ``n_0``; T2, ``M > q  =>  v2(3 n_{L-1} + q) = 1``, is
  one clause guarded by a comparator; for ``q = 1`` T8, ``M != 9 (mod 16)``, is
  one 3-literal clause.  Every 2-adic gate is a clause on the low bits.  The
  3-adic gates (T0, T2's ``M = 2q (mod 3)``, T4, the whole sieve) are not
  bit-local and would each need a mod-3 circuit -- that asymmetry is the
  honest reason a bit-level encoding sees the 2-adic half of the problem for
  free and the 3-adic half not at all.

Enumeration blocks the value of ``n_0`` after each model: for fixed ``L`` the
maximum determines the cycle, so this yields each cycle exactly once.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from .syracuse import check_q

__all__ = ["Cnf", "Encoding", "encode", "decode", "enumerate_cycles", "cnf_stats"]

Lit = bool | int  # True/False are folded constants, nonzero ints are literals


class Cnf:
    """A growing CNF with Tseitin gates that fold constants."""

    def __init__(self) -> None:
        self.nv = 0
        self.clauses: list[list[int]] = []

    def var(self) -> int:
        self.nv += 1
        return self.nv

    def clause(self, lits: list[Lit]) -> None:
        out: list[int] = []
        for lit in lits:
            if isinstance(lit, bool):
                if lit:
                    return  # satisfied by a constant
                continue
            out.append(lit)
        self.clauses.append(out)  # an empty clause records unsatisfiability

    # -- gates ----------------------------------------------------------------
    @staticmethod
    def NOT(a: Lit) -> Lit:
        return (not a) if isinstance(a, bool) else -a

    def AND(self, a: Lit, b: Lit) -> Lit:
        if a is False or b is False:
            return False
        if a is True:
            return b
        if b is True:
            return a
        if a == b:
            return a
        if a == -b:
            return False
        z = self.var()
        self.clause([-z, a])
        self.clause([-z, b])
        self.clause([z, -a, -b])
        return z

    def OR(self, a: Lit, b: Lit) -> Lit:
        return self.NOT(self.AND(self.NOT(a), self.NOT(b)))

    def XOR(self, a: Lit, b: Lit) -> Lit:
        if a is False:
            return b
        if b is False:
            return a
        if a is True:
            return self.NOT(b)
        if b is True:
            return self.NOT(a)
        if a == b:
            return False
        if a == -b:
            return True
        z = self.var()
        self.clause([-z, a, b])
        self.clause([-z, -a, -b])
        self.clause([z, -a, b])
        self.clause([z, a, -b])
        return z

    def MAJ(self, a: Lit, b: Lit, c: Lit) -> Lit:
        for x, y, w in ((a, b, c), (b, a, c), (c, a, b)):
            if x is False:
                return self.AND(y, w)
            if x is True:
                return self.OR(y, w)
        if a == b or a == c:
            return a
        if b == c:
            return b
        if a == -b:
            return c
        if a == -c:
            return b
        if b == -c:
            return a
        z = self.var()
        for cl in ([-z, a, b], [-z, a, c], [-z, b, c], [z, -a, -b], [z, -a, -c], [z, -b, -c]):
            self.clause(cl)
        return z

    # -- arithmetic on LSB-first bit vectors -----------------------------------
    def add(self, A: list[Lit], B: list[Lit]) -> list[Lit]:
        n = max(len(A), len(B))
        A = A + [False] * (n - len(A))
        B = B + [False] * (n - len(B))
        carry: Lit = False
        out: list[Lit] = []
        for a, b in zip(A, B):
            out.append(self.XOR(self.XOR(a, b), carry))
            carry = self.MAJ(a, b, carry)
        out.append(carry)
        return out

    def lt(self, A: list[Lit], B: list[Lit]) -> Lit:
        """``A < B`` as unsigned integers."""
        n = max(len(A), len(B))
        A = A + [False] * (n - len(A))
        B = B + [False] * (n - len(B))
        res: Lit = False
        eq: Lit = True
        for j in range(n - 1, -1, -1):
            res = self.OR(res, self.AND(eq, self.AND(self.NOT(A[j]), B[j])))
            eq = self.AND(eq, self.NOT(self.XOR(A[j], B[j])))
        return res

    def require(self, lit: Lit) -> None:
        self.clause([lit])

    def imp_eq(self, y: int, a: Lit, b: Lit) -> None:
        """``y => (a <-> b)``."""
        self.clause([-y, self.NOT(a), b])
        self.clause([-y, a, self.NOT(b)])


def const_bits(v: int, n: int) -> list[Lit]:
    return [bool((v >> j) & 1) for j in range(n)]


@dataclass(frozen=True)
class Encoding:
    q: int
    L: int
    W: int
    gates: bool
    cnf: Cnf = field(repr=False)
    n: list[list[int]] = field(repr=False)  # n[i][j]: bit j of element i
    y: list[list[int]] = field(repr=False)  # y[i][k]: v2(3 n_i + q) == k, k >= 1 (index 0 unused)


def encode(q: int, L: int, W: int, gates: bool = True) -> Encoding:
    """CNF for "an ``S_q``-cycle with ``L`` odd elements, maximum ``< 2^W``"."""
    check_q(q)
    if L < 1 or W < 4 or q >= 2**W:
        raise ValueError("need L >= 1, W >= 4 and q < 2^W")
    c = Cnf()
    n = [[c.var() for _ in range(W)] for _ in range(L)]
    K = W + 1
    y = [[0] + [c.var() for _ in range(K)] for _ in range(L)]
    for i in range(L):
        c.require(n[i][0])  # odd
        t = c.add(n[i], [False] + n[i])  # 3 n_i, W+2 bits
        t = c.add(t, const_bits(q, W))[: W + 2]  # + q; top carry is provably 0
        nxt = n[(i + 1) % L]
        c.clause([y[i][k] for k in range(1, K + 1)])
        for a in range(1, K + 1):
            for b in range(a + 1, K + 1):
                c.clause([-y[i][a], -y[i][b]])
        for k in range(1, K + 1):
            yk = y[i][k]
            for j in range(k):
                c.clause([-yk, c.NOT(t[j])])
            c.clause([-yk, t[k]])
            for j in range(W):
                src: Lit = t[j + k] if j + k < W + 2 else False
                c.imp_eq(yk, nxt[j], src)
    for i in range(1, L):
        c.require(c.lt(n[i], n[0]))
    if gates:
        c.require(n[0][1] if (q >> 1) & 1 else -n[0][1])  # T1: M = q (mod 4)
        gt = c.lt(const_bits(q, W), n[0])  # T2: M > q  =>  single halving into M
        c.clause([c.NOT(gt), y[L - 1][1]])
        if q == 1:  # T8: M != 9 (mod 16)
            c.clause([-n[0][3], n[0][2], n[0][1]])
    return Encoding(q, L, W, gates, c, n, y)


def cnf_stats(enc: Encoding) -> tuple[int, int, int]:
    """``(variables, clauses, literals)``."""
    cl = enc.cnf.clauses
    return enc.cnf.nv, len(cl), sum(len(x) for x in cl)


def decode(enc: Encoding, model: set[int]) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Read ``(elements, halvings)`` off a model (the set of true literals), verifying it."""
    L, W, q = enc.L, enc.W, enc.q
    elems = tuple(sum(1 << j for j in range(W) if enc.n[i][j] in model) for i in range(L))
    xs = tuple(next(k for k in range(1, W + 2) if enc.y[i][k] in model) for i in range(L))
    for i in range(L):
        if 3 * elems[i] + q != elems[(i + 1) % L] << xs[i]:
            raise AssertionError(f"model is not a cycle: {elems} {xs}")
    return elems, xs


def blocking_clause(enc: Encoding, elems: tuple[int, ...]) -> list[int]:
    """Forbid this value of the maximum ``n_0`` (for fixed ``L`` it determines the cycle)."""
    return [-enc.n[0][j] if (elems[0] >> j) & 1 else enc.n[0][j] for j in range(enc.W)]


def enumerate_cycles(
    q: int, L: int, W: int, gates: bool = True, solver: str = "cd", limit: int = 10_000
) -> list[tuple[tuple[int, ...], tuple[int, ...]]]:
    """All ``S_q``-cycles with ``L`` odd elements and maximum ``< 2^W``, via python-sat.

    Each cycle is returned once as ``(elements from the maximum, halvings)``,
    the same normal form as :class:`collatz_maxodd.cycles.Cycle`.
    """
    from pysat.solvers import Solver  # optional dependency

    enc = encode(q, L, W, gates)
    out: list[tuple[tuple[int, ...], tuple[int, ...]]] = []
    with Solver(name=solver, bootstrap_with=enc.cnf.clauses) as s:
        while len(out) < limit and s.solve():
            model = {lit for lit in s.get_model() if lit > 0}
            elems, xs = decode(enc, model)
            out.append((elems, xs))
            s.add_clause(blocking_clause(enc, elems))
    return sorted(out)
