"""The loop sieve: crossing out odd numbers that cannot sit in a second 3n+1 loop.

Classical Collatz, ``q = 1`` (the page ``web/loopsieve.html`` is 3n+1 only).  ``S(n) =
(3n+1)/2^x`` on odd ``n``; a *loop* is a closed orbit of ``S``; the known loop is ``{1}``
(1 -> 4 -> 2 -> 1).  A number is *crossed out* when it provably lies in no other loop.

Rules (proofs in ``docs/LOOP_SIEVE.md``)
---------------------------------------
L0  (dead ends, T0) ``3 | n``: ``3m + 1`` is never a multiple of 3, so nothing maps to
    ``n`` and ``n`` is in no loop.  1 itself is the known loop.
L1  (the user's rule) ``3n + 1 = 2^i`` iff ``n = (4^k - 1)/3`` (OEIS A002450); for
    ``k >= 2`` the number lands on 1, so any loop through it would contain 1.
L2  (closure) a loop contains the next odd number of each member, so if ``S(n)`` is in no
    loop other than ``{1}``, neither is ``n``.  Iterating from ``{1}`` crosses out, at pass
    ``d``, exactly the numbers that reach 1 in ``d`` odd steps: the backward tree of 1.
L3  (the verified region) every ``n < 2^71`` reaches 1 (Barina 2025, CITED).
L4  (its shadow) above ``V`` a number is out once its orbit dips below ``V``.  For
    ``n = V * 2^h`` the dip within ``k`` odd steps is decided by the halving word
    ``(x_1..x_k)``: it happens iff ``X_j > h + j log2 3`` for some ``j <= k``
    (``X_j = x_1 + ... + x_j``), up to a relative error below ``k / (3V)``; a word's share
    of the odd numbers is ``2^{-X_k}``.  :func:`shadow_survival` is the exact share of
    words that have not dipped.
L5  (no residue rule beyond L0) every class ``r mod 2^a 3^b`` with ``r`` odd and
    ``3 \\nmid r`` contains a member of a rational 3n+1 loop, so an argument that uses only
    remainders cannot cross out any further class.

Prior art: L0 is T0 (Kaneda 2015); L1 is A002450 (its OEIS entry notes the 3x+1 link);
L2 is the backward tree of 1 (Lagarias 1985; the closed form of every path back from 1 is
Boehm & Sontacchi 1978, on the main page); the shadow at ``h = 0`` is Terras's stopping
time (1976); rational loops are Lagarias 1990.  Nothing here is claimed as new.
"""

from __future__ import annotations

import math
from collections import Counter
from fractions import Fraction

from .syracuse import syracuse, syracuse_with_exponent

__all__ = [
    "VERIFIED_LIMIT",
    "pass_one",
    "doorway",
    "odd_steps_to_one",
    "odd_steps_table",
    "pass_histogram",
    "survivors_after",
    "last_survivor",
    "pass_records",
    "pass_two_closed_form",
    "shadow_survival",
    "shadow_survival_float",
    "shadow_rate",
    "rational_loop_point",
    "rational_syracuse",
    "rational_loop",
    "compositions",
    "loop_through_class",
    "classes_hit",
]

#: Barina 2025, paper limit (docs/GROUND_TRUTH.md; cycleeq.BARINA_2025_PAPER_LIMIT)
VERIFIED_LIMIT = 2**71

LOG2_3 = math.log2(3)


# ---------------------------------------------------------------------------
# L1 and L2: the passes
# ---------------------------------------------------------------------------


def pass_one(limit: int) -> list[int]:
    """The numbers ``n > 1`` with ``3n + 1`` a power of 2, below ``limit``: ``(4^k - 1)/3``, ``k >= 2``."""
    out, k = [], 2
    while (4**k - 1) // 3 < limit:
        out.append((4**k - 1) // 3)
        k += 1
    return out


def doorway(n: int) -> int | None:
    """The last odd number before 1 on the orbit of odd ``n > 1`` (always a pass-one number);
    ``None`` for ``n = 1``.  Loops forever if the orbit never reaches 1."""
    if n == 1:
        return None
    while True:
        s = syracuse(n)
        if s == 1:
            return n
        n = s


def odd_steps_to_one(n: int) -> int:
    """Number of odd steps from odd ``n`` to 1 -- the pass at which rule L2 crosses ``n`` out."""
    c = 0
    while n != 1:
        n = syracuse(n)
        c += 1
    return c


def odd_steps_table(N: int) -> list[int]:
    """``table[(n - 1)//2] = odd_steps_to_one(n)`` for odd ``n < N`` (memoised by stopping time)."""
    size = N // 2
    t = [0] * size
    for i in range(1, size):
        n = 2 * i + 1
        x, c = n, 0
        while x >= n:
            x = syracuse(x)
            c += 1
        t[i] = c + t[(x - 1) // 2]
    return t


def pass_histogram(N: int) -> Counter:
    """How many odd ``n < N`` are crossed out at each pass (pass 0 is ``n = 1``)."""
    return Counter(odd_steps_table(N))


def survivors_after(N: int, d: int, *, t0: bool = True) -> int:
    """Odd ``n < N`` still standing after passes ``0..d``; with ``t0`` the multiples of 3 are
    crossed out at pass 0 as well (rule L0)."""
    t = odd_steps_table(N)
    return sum(1 for i, s in enumerate(t) if s > d and not (t0 and (2 * i + 1) % 3 == 0))


def last_survivor(N: int) -> tuple[int, int]:
    """The odd ``n < N`` crossed out last, and its pass (ties: the smallest ``n``)."""
    t = odd_steps_table(N)
    best = max(t)
    return 2 * t.index(best) + 1, best


def pass_records(N: int) -> list[tuple[int, int]]:
    """Odd ``n < N`` needing more passes than every smaller odd number (OEIS A033958/A033959)."""
    out, best = [], -1
    for i, s in enumerate(odd_steps_table(N)):
        if s > best:
            best = s
            out.append((2 * i + 1, s))
    return out


def pass_two_closed_form(limit: int) -> list[int]:
    """Pass-two numbers below ``limit`` from the closed form ``(2^x (4^k - 1) - 3)/9``.

    The target ``s = (4^k - 1)/3`` is ``= k (mod 3)``: ``k = 0 (mod 3)`` is a dead end, ``k = 1``
    needs ``x`` even, ``k = 2`` needs ``x`` odd.  Sources of ``s`` can exceed ``limit`` only if
    ``s`` does, so ``s < limit`` suffices; ``n = s`` itself (``x = 2``, ``s = 1``) is excluded.
    """
    out = set()
    for s in pass_one(2 * limit):
        k = round(math.log(3 * s + 1, 4))
        if k % 3 == 0:
            continue
        x = 2 if k % 3 == 1 else 1
        while True:
            n = ((1 << x) * s - 1) // 3
            if n >= limit:
                break
            out.add(n)
            x += 2
    return sorted(out)


# ---------------------------------------------------------------------------
# L4: the shadow of the verified region
# ---------------------------------------------------------------------------


def shadow_survival(h: int, k: int) -> list[Fraction]:
    """Exact share of halving words that have not dipped below ``V`` after ``1..k`` odd steps,
    starting ``h`` bits above ``V`` (integer ``h >= 0``).

    A word survives step ``j`` iff ``X_j <= h + j log2 3`` iff ``2^{X_j - h} <= 3^j``; its
    weight is ``2^{-X}``.  ``1 - shadow_survival(h, k)[k-1]`` is the share crossed out.
    """
    if h < 0 or k < 1:
        raise ValueError("need h >= 0 and k >= 1")
    w: dict[int, Fraction] = {0: Fraction(1)}
    out = []
    for j in range(1, k + 1):
        cap = h + (3**j).bit_length() - 1  # largest X with 2^(X-h) <= 3^j
        nw: dict[int, Fraction] = {}
        acc = Fraction(0)
        for X in range(min(w) + 1, cap + 1):
            acc = (w.get(X - 1, 0) + acc) / 2
            if acc:
                nw[X] = acc
        w = nw
        out.append(sum(w.values(), Fraction(0)))
    return out


def shadow_survival_float(h: float, k: int) -> list[float]:
    """Floating version of :func:`shadow_survival` for real ``h >= 0`` (the page's chart)."""
    w: dict[int, float] = {0: 1.0}
    out = []
    for j in range(1, k + 1):
        cap = math.floor(h + j * LOG2_3 + 1e-12)
        nw: dict[int, float] = {}
        acc = 0.0
        for X in range(min(w) + 1, cap + 1):
            acc = 0.5 * (w.get(X - 1, 0.0) + acc)
            if acc > 0.0:
                nw[X] = acc
        w = nw
        out.append(sum(w.values()))
        if not w:
            out.extend([0.0] * (k - j))
            break
    return out


def shadow_rate() -> float:
    """``lambda/3`` with ``lambda = a^a/(a-1)^(a-1)``, ``a = log2 3``: the exponential rate of
    :func:`shadow_survival`, equal to ``min_t 3^t/(2^{t+1} - 1)`` (docs/LOOP_SIEVE.md, L4)."""
    a = LOG2_3
    return a**a / (a - 1) ** (a - 1) / 3


# ---------------------------------------------------------------------------
# L5: rational loops pass through every class except the multiples of 3
# ---------------------------------------------------------------------------


def rational_loop_point(word: tuple[int, ...]) -> Fraction:
    """The rational number whose halving word is ``word`` repeated: ``c / (2^B - 3^L)`` with
    ``c = sum_i 3^{L-1-i} 2^{X_i}`` (Boehm-Sontacchi; Lagarias 1990)."""
    L, B = len(word), sum(word)
    c, X = 0, 0
    for i, x in enumerate(word):
        c += 3 ** (L - 1 - i) * 2**X
        X += x
    return Fraction(c, 2**B - 3**L)


def rational_syracuse(x: Fraction) -> tuple[Fraction, int]:
    """``S`` on a rational with odd denominator and odd numerator: ``((3x+1)/2^v, v)``."""
    t = 3 * x + 1
    num = t.numerator
    v = (num & -num).bit_length() - 1
    return t / 2**v, v


def rational_loop(word: tuple[int, ...]) -> list[Fraction]:
    """The members of the rational loop with halving word ``word``, in orbit order (checked)."""
    x = rational_loop_point(word)
    out = [x]
    for i, want in enumerate(word):
        x, v = rational_syracuse(x)
        if v != want:
            raise AssertionError(f"halving {v} != {want} at step {i}")
        out.append(x)
    if out[-1] != out[0]:
        raise AssertionError("did not close")
    return out[:-1]


def compositions(B: int):
    """All tuples of positive integers summing to ``B``, in lexicographic order."""
    if B == 0:
        yield ()
        return
    for first in range(1, B + 1):
        for rest in compositions(B - first):
            yield (first,) + rest


def _residue(x: Fraction, m: int) -> int:
    return x.numerator * pow(x.denominator, -1, m) % m


def loop_through_class(r: int, m: int, b_max: int = 16) -> tuple[tuple[int, ...], Fraction] | None:
    """A halving word and loop member ``x`` with ``x = r (mod m)``, smallest total ``B`` first;
    ``m`` of the form ``2^a 3^b``.  ``None`` if no word with ``B <= b_max`` works."""
    for B in range(1, b_max + 1):
        for w in compositions(B):
            for i in range(len(w)):
                rot = w[i:] + w[:i]
                x = rational_loop_point(rot)
                if _residue(x, m) == r % m:
                    return rot, x
    return None


def classes_hit(m: int, b_max: int) -> set[int]:
    """Residues mod ``m`` (``m = 2^a 3^b``) of all rational loop members with ``B <= b_max``."""
    hit = set()
    for B in range(1, b_max + 1):
        for w in compositions(B):
            L, d = len(w), 2**B - 3 ** len(w)
            inv = pow(d, -1, m)
            for i in range(L):
                rot = w[i:] + w[:i]
                c, X = 0, 0
                for j, x in enumerate(rot):
                    c += 3 ** (L - 1 - j) * 2**X
                    X += x
                hit.add(c * inv % m)
    return hit
