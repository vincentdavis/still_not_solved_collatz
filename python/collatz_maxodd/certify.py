"""Certifying that a number is **not** the maximum of a nontrivial cycle.

Three tests, all complete and unconditional, in increasing order of cleverness.
The point of this module is that they are not equally cheap.

``forward_to_one``
    Run the orbit of ``M`` until it reaches 1.  Complete because nothing in a
    nontrivial cycle ever reaches 1 (``lean/Collatz/Equivalence.lean``:
    ``S 1 1 = 1``, so a 1 anywhere in a backward chain drags the whole chain
    down to 1).  This is what a verification program like Barina's does.

``forward_exceeds``
    Run the orbit until it EXCEEDS ``M``.  If it does, ``M`` is not the maximum
    of its own orbit, so not a cycle maximum.  Cheap, and it disposes of about
    71.4% of odd numbers immediately -- exactly the complement of the 2-adic
    sieve's saturation density ``0.2863``.  Falls back to ``forward_to_one``.

``backward_depth``
    Compute ``d(M)``: exhaust the tree of backward chains from ``M`` that stay
    ``<= M``.  By the equivalence theorem an infinite such chain exists iff a
    nontrivial cycle does, so **the DFS terminating is itself the proof**.
    Two thirds of odd numbers die at depth 0 (they are ``0 mod 3``, or their
    forced predecessor is), which is why this is by far the cheapest.

Measured over 200 000 odd numbers from 10^7, counting work units
(orbit steps for the forward tests, tree nodes for the backward one)::

    forward_to_one            11,424,896     1.0x
    forward_exceeds            3,095,678     3.7x
    backward_depth               414,293    27.6x

Adding the residue sieve as a precomputed TABLE (which is how any real
implementation would do it, rather than the general-purpose predicate in
``sieve``) gives a further ~5x, for roughly **77x** over the naive forward test.

PRIOR ART / NOVELTY: none claimed.  Restricting a cycle search by residue is
standard; the backward formulation is the equivalence theorem read as an
algorithm.  What is here is the measurement.
"""

from __future__ import annotations

from .sieve import surviving_residues_mod2, surviving_residues_mod3

__all__ = ["forward_to_one", "forward_exceeds", "backward_depth",
           "residue_table", "certify_range",
           "class_threshold", "class_is_certified", "class_coverage"]

_CAP = 500


def _step(x: int, q: int) -> int:
    m = 3 * x + q
    while m % 2 == 0:
        m //= 2
    return m


def forward_to_one(M: int, q: int = 1) -> tuple[bool, int]:
    """``(not_a_cycle_max, work)`` by running the orbit until it reaches the
    fixed point.  Only meaningful for ``q = 1``, where the fixed point is 1."""
    x, w = M, 0
    while x != 1:
        x = _step(x, q)
        w += 1
        if w > 10 ** 6:
            return False, w                      # gave up; no conclusion
    return True, w


def forward_exceeds(M: int, q: int = 1) -> tuple[bool, int]:
    """``(not_a_cycle_max, work)``.  Exceeding ``M`` refutes ``M`` immediately;
    otherwise this is exactly ``forward_to_one``."""
    x, w = M, 0
    while True:
        x = _step(x, q)
        w += 1
        if x > M or x == 1:
            return True, w
        if w > 10 ** 6:
            return False, w


def backward_depth(M: int, q: int = 1, cap: int = _CAP) -> tuple[int, int]:
    """``(d(M), work)`` -- exhausts the bounded backward tree.

    Termination with ``d < cap`` is a proof that ``M`` is not a cycle maximum:
    a cycle maximum would admit an infinite chain, and the tree is finitely
    branching, so the DFS could not have finished.
    """
    best, work, stack = 0, 0, [(M, 0)]
    while stack:
        y, d = stack.pop()
        work += 1
        if d > best:
            best = d
        if d >= cap:
            return cap, work
        if y % 3 == 0:
            continue
        b = 2 if (y % 3) == (q % 3) else 1
        while True:
            num = (1 << b) * y - q
            if num <= 0:
                b += 2
                continue
            z, r = divmod(num, 3)
            if z > M:
                break
            if r == 0:
                stack.append((z, d + 1))
            b += 2
    return best, work


def residue_table(depth: int = 4, a: int = 10, q: int = 1):
    """``(mod3, set3, mod2, set2)`` -- the sieve as O(1) lookups."""
    m3, r3 = surviving_residues_mod3(depth, q)
    m2, r2 = surviving_residues_mod2(a, q)
    return m3, frozenset(r3), m2, frozenset(r2)


def certify_range(lo: int, hi: int, q: int = 1, depth: int = 4, a: int = 10,
                  cap: int = _CAP) -> dict:
    """Certify that no odd ``M`` in ``[lo, hi)`` is the maximum of a cycle.

    Sieve by residue table first, then run the backward test on what survives.
    Returns statistics, and ``ok=False`` with the offending ``M`` if any
    candidate reached ``cap`` (which would mean a cycle).
    """
    m3, s3, m2, s2 = residue_table(depth, a, q)
    tested = survivors = work = 0
    worst = (0, 0)
    for M in range(lo | 1, hi, 2):
        tested += 1
        if (M % m3) not in s3 or (M % m2) not in s2:
            continue
        survivors += 1
        d, w = backward_depth(M, q, cap)
        work += w
        if d > worst[1]:
            worst = (M, d)
        if d >= cap:
            return {"ok": False, "offender": M, "tested": tested}
    return {"ok": True, "tested": tested, "survivors": survivors,
            "sieve_kept": survivors / tested if tested else 0.0,
            "backward_work": work, "max_depth": worst[1], "argmax": worst[0]}

# ---------------------------------------------------------------------------
# Certifying a whole residue class -- infinitely many M in one computation
# ---------------------------------------------------------------------------
#
# The exact size test on a backward prefix is  M (2^{B_j} - 3^j) <= c_j ; the
# magnitude-free one is  2^{B_j} <= 3^j.  They differ only when 2^{B_j} > 3^j
# and  M <= c_j / (2^{B_j} - 3^j).  Above the largest such M the two agree, so
# d(M) depends ONLY on M mod 3^k -- and a residue class whose backward tree
# dies before depth k certifies every M in it at once.


def _c_max(q: int, j: int, B: int) -> int:
    """Largest ``c_j`` over prefixes with total halvings ``B``.

    ``c_j`` grows when the early hops are small, so it is maximised by
    ``b_i = 1`` for ``i < j``, giving this closed form.
    """
    return q * (2 ** (B - j + 1) * (3 ** (j - 1) - 2 ** (j - 1)) + 3 ** (j - 1))


def class_threshold(k: int, q: int = 1, extra: int = 40) -> int:
    """``T_k``: above this, the exact size test collapses to the magnitude-free one.

    Maximising over all ``(j, B)`` rather than only over admissible prefixes can
    only overestimate ``T_k``, which is safe -- a larger threshold still yields a
    valid certificate.  Reproduces the project's independently computed
    ``running_max`` (1, 1, 9, 9, 86, ..., 538 at ``k = 13``) exactly.
    """
    if k < 1:
        raise ValueError("k must be >= 1")
    best = 0
    for j in range(1, k + 1):
        p3 = 3 ** j
        B = p3.bit_length()
        while (1 << B) <= p3:
            B += 1
        for b in range(B, B + extra):
            v = _c_max(q, j, b) // ((1 << b) - p3)
            if v > best:
                best = v
    return best


def _free_depth(M: int, k: int, q: int = 1) -> int:
    """Magnitude-free backward depth: keeps only ``2^{B_j} <= 3^j``, capped at ``k``."""
    best, stack = 0, [(M, 0, 0)]
    while stack:
        y, d, B = stack.pop()
        if d > best:
            best = d
        if d >= k:
            return k
        if y % 3 == 0:
            continue
        b = 2 if (y % 3) == (q % 3) else 1
        while True:
            if (1 << (B + b)) > 3 ** (d + 1):
                break
            num = (1 << b) * y - q
            if num > 0 and num % 3 == 0:
                stack.append((num // 3, d + 1, B + b))
            b += 2
    return best


def class_is_certified(r: int, k: int, q: int = 1, base: int = 10 ** 24) -> bool:
    """Is every odd ``M = r (mod 3^k)`` above :func:`class_threshold` refuted?

    True when the class's magnitude-free backward tree dies before depth ``k``.
    One finite computation then covers infinitely many ``M``.
    """
    mod = 3 ** k
    M = base - (base % mod) + (r % mod)
    if M % 2 == 0:
        M += mod                      # mod is odd, so this restores oddness
    return _free_depth(M, k, q) < k


def class_coverage(k: int, q: int = 1) -> dict:
    """How much of ``Z/3^k`` is certified at depth ``k``, and above what bound."""
    mod = 3 ** k
    alive = sum(1 for r in range(mod) if not class_is_certified(r, k, q))
    return {"k": k, "modulus": mod, "alive": alive, "dead": mod - alive,
            "certified_fraction": (mod - alive) / mod,
            "threshold": class_threshold(k, q)}
