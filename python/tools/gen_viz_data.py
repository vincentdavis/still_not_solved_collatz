#!/usr/bin/env python3
"""
gen_viz_data.py -- generate web/data.json for the COLLATZ max-odd visualisations.

Stdlib only.  Deterministic.  Run:

    python3 python/tools/gen_viz_data.py [--out web/data.json]

Everything emitted here is *computed*, not transcribed.  Where a number is
quoted from the literature it lives in LITERATURE below and is labelled as
such in the JSON.

Notation follows docs/GROUND_TRUTH.md:

    S_q(n) = (3n+q)/2^b,  b = v2(3n+q),  n odd, q odd, 3 nmid q
    cycle:  L odd elements, M = largest odd element, B = total halvings
    backward from M:  y_0 = M, 3*y_j + q = 2^{b_j} * y_{j-1},  B_k = b_1+...+b_k
    closed form:      y_k = (2^{B_k} M - c_k)/3^k,  c_k = 2^{b_k} c_{k-1} + 3^{k-1} q, c_0 = 0

IMPORTANT HONESTY NOTES (mirrored into web/DATA.md):
  * None of the underlying facts are new.  See docs/ and the `theorems[].prior_art`
    field.  T0/T1/T6/T7 are published; T2-T5 are one-line corollaries of folklore.
  * The deep sieve levels (mod 3^{k+1}, mod 2^a) are valid *exclusions* only above
    an M-threshold; the thresholds are computed here (`sieve_layers.floor_rule_thresholds`)
    and must be respected by any viz that labels a small number "excluded".
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from decimal import Decimal, getcontext

getcontext().prec = 90

LOG2_3 = math.log2(3.0)

# ---------------------------------------------------------------------------
# quoted constants (NOT computed here -- literature values)
# ---------------------------------------------------------------------------
LITERATURE = {
    "verification_limit": {
        "value": 2075 * 2**60,
        "approx": 2.3923121220592075e21,
        "source": "D. Barina, J. Supercomputing 81, 810 (2025); project page pcbarina.fit.vutbr.cz, retrieved 2026-08-26",
        "meaning": "all n < 2075*2^60 verified to reach 1; hence any nontrivial q=1 cycle has minimum element > this",
    },
    "min_odd_elements": {
        "value": 1.375e11,
        "source": "Hercher, J. Integer Seq. 26 (2023), Art. 23.3.5, Corollary 29 (hypothesis X0 >= 1536*2^60, met by Barina 2025)",
        "caveat": "the combination Barina-2025 + Hercher-Cor.29 was inferred, not found stated in print",
    },
    "min_m_cycles": {
        "value": 92,
        "source": "Hercher 2023: no nontrivial Collatz m-cycle with m <= 91",
    },
}

# ---------------------------------------------------------------------------
# small helpers
# ---------------------------------------------------------------------------


def r6(x: float) -> float:
    """Round to 6 significant digits (JSON-compact, plenty for plotting)."""
    if x == 0 or not math.isfinite(x):
        return x
    return float(f"{x:.6g}")


def v2(n: int) -> int:
    return (n & -n).bit_length() - 1


def floor_klog2_3(k: int) -> int:
    """exact floor(k*log2 3) -- 3^k is never a power of two for k>=1."""
    return (3**k).bit_length() - 1 if k >= 1 else 0


def ceil_klog2_3(k: int) -> int:
    """exact ceil(k*log2 3)."""
    return (3**k).bit_length() if k >= 1 else 0


# ---------------------------------------------------------------------------
# 1. mod-12 wheel
# ---------------------------------------------------------------------------

# rule codes used in the per-odd string
#   'a' = fails T1  (n = 3 mod 4): S_q(n) > n, so n ascends and cannot be the max
#   'b' = fails T0  (3 | n)      : n has NO odd predecessor at all
#   'c' = fails T2  (n = 1 mod 3): every odd predecessor of n exceeds n
#   '0'..'9'        : survives the mod-12 wheel; digit = deepest 3-adic level passed
RULE_PRIORITY = ("a", "b", "c")


def wheel_rule(n: int) -> str | None:
    if n % 4 == 3:
        return "a"
    if n % 3 == 0:
        return "b"
    if n % 3 == 1:
        return "c"
    return None


def build_wheel(n_odds: int, surv3: dict[int, tuple[int, list[int]]], max_level: int):
    """Per-odd classification string + counts."""
    surv_sets = {k: set(v[1]) for k, v in surv3.items()}
    chars = []
    counts = {"a": 0, "b": 0, "c": 0, "survive": 0}
    per_mod12 = {r: {"total": 0, "rule": None} for r in (1, 3, 5, 7, 9, 11)}
    level_counts = {}
    for i in range(n_odds):
        n = 2 * i + 1
        per_mod12[n % 12]["total"] += 1
        rule = wheel_rule(n)
        if rule is not None:
            per_mod12[n % 12]["rule"] = rule
            counts[rule] += 1
            chars.append(rule)
            continue
        counts["survive"] += 1
        per_mod12[n % 12]["rule"] = "survive"
        lvl = 0
        for k in range(1, max_level + 1):
            mod, _ = surv3[k]
            if n % mod in surv_sets[k]:
                lvl = k
            else:
                break
        lvl = min(lvl, 9)
        level_counts[lvl] = level_counts.get(lvl, 0) + 1
        chars.append(str(lvl))
    return "".join(chars), counts, per_mod12, level_counts


# ---------------------------------------------------------------------------
# 2. backward tree (T6 floor rule), q = 1, large M
# ---------------------------------------------------------------------------


def build_tree(max_depth: int):
    """
    Nodes = backward prefixes (b_1..b_k), b_j >= 1, with B_j <= floor(j*log2 3)
    for every j <= k.  b_1 = 1 is *forced* (B_1 <= 1), which is T2.

    Children of a node with prefix-sum B are exactly b = 1..(floor(k lg3) - B),
    so the whole tree is encoded by one digit per node: its child count.
    Returns (levels, child_count_strings) where levels[k] is the list of B_k.
    """
    levels = [[0]]  # depth 0: the root, B_0 = 0
    child_strings = []
    for k in range(1, max_depth + 1):
        cap = floor_klog2_3(k)
        nxt = []
        cs = []
        for B in levels[k - 1]:
            c = cap - B
            c = max(c, 0)
            cs.append(str(c))
            for b in range(1, c + 1):
                nxt.append(B + b)
        child_strings.append("".join(cs))
        levels.append(nxt)
    return levels, child_strings


def tree_counts_dp(max_k: int) -> list[int]:
    """N(k) by DP over prefix sums -- cheap far beyond the explicit tree."""
    cur = {0: 1}
    out = []
    for k in range(1, max_k + 1):
        cap = floor_klog2_3(k)
        nxt: dict[int, int] = {}
        for B, cnt in cur.items():
            for b in range(1, cap - B + 1):
                nxt[B + b] = nxt.get(B + b, 0) + cnt
        cur = nxt
        out.append(sum(cur.values()))
    return out


def growth_constant() -> float:
    a = LOG2_3
    return a**a / (a - 1) ** (a - 1)


# ---------------------------------------------------------------------------
# 2b.  How large must M be for the floor rule to be equivalent to T6's exact test?
# ---------------------------------------------------------------------------


def floor_rule_thresholds(max_depth: int, q: int = 1, extra_b: int = 30):
    """
    g(k) = max M that the exact T6 test  M(2^{B_k} - 3^k) <= c_k  still allows
    while the floor rule B_k <= floor(k lg3) already rejects, over all prefixes
    whose proper prefixes are floor-admissible.

    So `B_k <= floor(k lg3)`  <=>  T6  holds for every M > max_{j<=k} g(j).
    g(2) = 1 reproduces T5's "M >= 2"; the underlying ratio is the sharp 11q/7.
    """
    # depth-(k-1) admissible prefixes carried as (B, c)
    prefixes = [(0, 0)]
    out = {}
    for k in range(1, max_depth + 1):
        cap = floor_klog2_3(k)
        best = 0
        nxt = []
        for B, c in prefixes:
            bmax_ok = cap - B
            # floor-admissible children
            for b in range(1, bmax_ok + 1):
                nxt.append((B + b, (1 << b) * c + 3 ** (k - 1) * q))
            # floor-rejected children -- how big may M still be?
            for b in range(max(1, bmax_ok + 1), bmax_ok + 1 + extra_b):
                Bk = B + b
                ck = (1 << b) * c + 3 ** (k - 1) * q
                denom = (1 << Bk) - 3**k
                if denom <= 0:
                    continue
                best = max(best, ck // denom)
        out[k] = best
        prefixes = nxt
    return out


# ---------------------------------------------------------------------------
# 3. the 3-adic sieve:  surviving M mod 3^{k+1}
# ---------------------------------------------------------------------------


def mod3_sieve_vectors(max_depth: int, q: int = 1):
    """
    For every floor-admissible backward vector at depth k, M mod 3^k is pinned
    (2^{B_k} is invertible mod 3^k), then T0 (3 nmid y_k) kills exactly one of the
    three lifts to mod 3^{k+1}.  Survivors = union over vectors, with collisions.
    The whole (B_j, c_j) history is carried so every intermediate y_j can be
    tested too -- some floor-admissible vectors die at an intermediate j.

    Returns {k: (3^{k+1}, sorted residues)}.
    """
    out = {}
    # each state: list of (B_j, c_j) for j = 1..k
    states: list[list[tuple[int, int]]] = [[]]
    for k in range(1, max_depth + 1):
        cap = floor_klog2_3(k)
        nxt = []
        for hist in states:
            B = hist[-1][0] if hist else 0
            c = hist[-1][1] if hist else 0
            for b in range(1, cap - B + 1):
                nxt.append(hist + [(B + b, (1 << b) * c + 3 ** (k - 1) * q)])
        states = nxt
        mod_k = 3**k
        mod_k1 = 3 ** (k + 1)
        survivors = set()
        for hist in states:
            Bk, ck = hist[-1]
            inv = pow(pow(2, Bk, mod_k1), -1, mod_k1)
            base = (inv * ck) % mod_k
            for t in range(3):
                M = base + t * mod_k
                ok = True
                for j in range(1, k + 1):
                    Bj, cj = hist[j - 1]
                    num = (pow(2, Bj, mod_k1) * M - cj) % mod_k1
                    # 3^j | num must hold (implied); y_j mod 3 = (num/3^j) mod 3
                    if num % (3**j) != 0:
                        ok = False
                        break
                    if (num // (3**j)) % 3 == 0:
                        ok = False
                        break
                if ok:
                    survivors.add(M)
        out[k] = (mod_k1, sorted(survivors))
    return out


def honest_backward_check(M: int, depth: int, q: int = 1) -> bool:
    """
    No residue arithmetic, no floor rule, no b_1=1 assumption: does M admit a
    genuine backward chain y_1..y_depth of odd numbers with y_j <= M and 3 nmid y_j?
    """
    if M % 3 == 0:
        return False
    limit = 3 * M  # y_j <= M  <=>  2^b * y_{j-1} - q <= 3M

    def rec(y: int, j: int) -> bool:
        if j == depth:
            return True
        b = 1
        while True:
            val = (1 << b) * y - q
            if val > limit:
                return False
            if val > 0 and val % 3 == 0:
                z = val // 3
                if z % 3 != 0 and z <= M and rec(z, j + 1):
                    return True
            b += 1

    return rec(M, 0)


# ---------------------------------------------------------------------------
# 4. the 2-adic sieve:  surviving M mod 2^a  (forward "stay below M" condition)
# ---------------------------------------------------------------------------


def mod2_sieve(max_a: int, q: int = 1):
    """
    Forward orbit x_0 = M, x_j = (3 x_{j-1} + q)/2^{a_j}, A_j = a_1+...+a_j.
    For M large, x_j <= M  <=>  A_j >= ceil(j log2 3).  a_j is determined by
    finitely many low bits of M, so this is a genuine mod-2^a condition.
    A residue class is kept unless it *provably* violates.
    """
    out = {}
    for a in range(2, max_a + 1):
        surv = []
        for r in range(1, 1 << a, 2):
            cur, e, A, j = r, a, 0, 0
            ok = True
            while e >= 1:
                t = (3 * cur + q) % (1 << e)
                if t == 0:
                    # v2 >= e but its true value is unknown, so A_{j+1} is only
                    # bounded BELOW -- no violation is provable.  Stop, keep the class.
                    break
                v = v2(t)
                A += v
                j += 1
                if A < ceil_klog2_3(j):
                    ok = False
                    break
                # 3x+q = t + 2^e*s  =>  next = t>>v  (mod 2^{e-v})
                e -= v
                cur = (t >> v) % (1 << e) if e >= 1 else 0
            if ok:
                surv.append(r)
        out[a] = surv
    return out


def mod2_limit_density(depth: int = 4000, margin: int = 60) -> float:
    """
    Limiting density (among odd numbers) of the forward 2-adic sieve.

    Model the exact combinatorics: a_j = v with weight 2^{-v} (the exact measure
    on the low bits of M), and the constraint A_j >= ceil(j log2 3) for all j.
    Track the slack d_j = A_j - ceil(j log2 3) >= 0.  The step drops the ceiling
    increment w_j in {1,2}, so d_j = d_{j-1} + a_j - w_j.

    The walk has positive drift (E[a] = 2 > log2 3), so once the slack exceeds
    `margin` survival is certain to within ~2^-margin; those states are absorbed.
    """
    safe = 0.0
    mass = {0: 1.0}
    for j in range(1, depth + 1):
        w = ceil_klog2_3(j) - ceil_klog2_3(j - 1)
        nxt: dict[int, float] = {}
        for d, m in mass.items():
            for v in range(1, margin + w + 2):
                nd = d + v - w
                if nd < 0:
                    continue
                if nd >= margin:
                    safe += m * 2.0**-v
                else:
                    nxt[nd] = nxt.get(nd, 0.0) + m * 2.0**-v
            # tail v >= margin + w + 2 is certainly safe
            safe += m * 2.0 ** -(margin + w + 1)
        mass = nxt
        if sum(mass.values()) < 1e-18:
            break
    return safe + sum(mass.values())


# ---------------------------------------------------------------------------
# 5. real cycles of S_q
# ---------------------------------------------------------------------------


def forward_max_check(M: int, q: int = 1, step_cap: int = 4000):
    """Is M the maximum of its own forward Syracuse orbit (down to 1, q=1)?"""
    x = M
    for _ in range(step_cap):
        t = 3 * x + q
        x = t >> v2(t)
        if x > M:
            return False
        if x == 1:
            return True
    return True


def find_cycles(q: int, max_start: int, value_cap: int, step_cap: int):
    seen: set[int] = set()
    cycles = []
    for n0 in range(1, max_start + 1, 2):
        if n0 in seen:
            continue
        path: dict[int, int] = {}
        order: list[int] = []
        n = n0
        steps = 0
        while True:
            if n in path:
                cycles.append(order[path[n]:])
                break
            if n in seen or n > value_cap or steps > step_cap:
                break
            path[n] = len(order)
            order.append(n)
            n = (3 * n + q) // (1 << v2(3 * n + q))
            steps += 1
        seen.update(order)
    # canonicalise & dedupe by min element
    uniq = {}
    for cyc in cycles:
        key = min(cyc)
        if key not in uniq:
            uniq[key] = cyc
    return list(uniq.values())


def describe_cycle(q: int, cyc: list[int]):
    L = len(cyc)
    M = max(cyc)
    i = cyc.index(M)
    odds = cyc[i:] + cyc[:i]  # forward order starting at M
    a = []
    for x in odds:
        a.append(v2(3 * x + q))
    B = sum(a)
    # backward vector b_j = a_{L+1-j}
    b = list(reversed(a))
    b1 = b[0]
    b2 = b[1] if L >= 2 else None
    rec = {
        "q": q,
        "L": L,
        "M": M,
        "min": min(cyc),
        "B": B,
        "odds": odds,
        "a": a,
    }
    rec["chk"] = {
        "cmp": "gt" if M > q else ("eq" if M == q else "lt"),
        "r": r6(M / q),  # M/q, for the 11/7 and 49/5 thresholds
        "b1": b1,
        "b2": b2,
        "T0": all(x % 3 != 0 for x in cyc),
        "T1": (M - q) % 4 == 0,
        "T2": b1 == 1,
        "T3": (M - 5 * q) % 12 == 0,
        "T4": (M - 5 * q) % 9 != 0,
        "T5": (b2 <= 2) if b2 is not None else None,
    }
    return rec


# ---------------------------------------------------------------------------
# 6. Diophantine
# ---------------------------------------------------------------------------

DEC_LOG2_3 = Decimal(3).ln() / Decimal(2).ln()
DEC_LN2 = Decimal(2).ln()


def dio_row(L: int):
    """
    B = smallest B with 2^B > 3^L  (forced by T7: M(2^B - 3^L) = c_L > 0).
    excess = 2^{B/L} - 3 > 0.
    Any S_1 cycle with L odd elements has minimum element <= 1/excess,
    because 2^B = prod(3 + 1/n_i) <= (3 + 1/min)^L.
    Symmetrically its maximum M satisfies M >= 1/excess.
    """
    Ld = Decimal(L)
    B = int((DEC_LOG2_3 * Ld).to_integral_value(rounding="ROUND_FLOOR")) + 1
    e = Decimal(B) - DEC_LOG2_3 * Ld  # in (0, 1]
    excess = 3 * ((DEC_LN2 * e / Ld).exp() - 1)
    return B, e, excess


def diophantine_table(Lmax: int):
    rows = []
    for L in range(1, Lmax + 1):
        B, e, excess = dio_row(L)
        rows.append(
            {
                "L": L,
                "B": B,
                "drift": r6(float(e)),  # B - L*log2(3), in (0,1]
                "excess": r6(float(excess)),  # 2^{B/L} - 3
                "min_bound": r6(float(1 / excess)),  # cycle minimum must be <= this
            }
        )
    return rows


def diophantine_records(Lmax: int):
    """L where the bound on the cycle minimum sets a new record."""
    best = Decimal(-1)
    out = []
    for L in range(1, Lmax + 1):
        B, e, excess = dio_row(L)
        bound = 1 / excess
        if bound > best:
            best = bound
            out.append({"L": L, "B": B, "min_bound": r6(float(bound))})
    return out


def cf_log2_3(n_terms: int):
    x = DEC_LOG2_3
    terms = []
    for _ in range(n_terms):
        a = int(x.to_integral_value(rounding="ROUND_FLOOR"))
        terms.append(a)
        frac = x - a
        if frac == 0:
            break
        x = 1 / frac
    # convergents
    h0, h1 = 0, 1
    k0, k1 = 1, 0
    conv = []
    for a in terms:
        h0, h1 = h1, a * h1 + h0
        k0, k1 = k1, a * k1 + k0
        conv.append(
            {
                "a": a,
                "B": h1,
                "L": k1,
                "ratio": r6(h1 / k1),
                "err": r6(float(Decimal(h1) / Decimal(k1) - DEC_LOG2_3)),
                "from_above": h1 / k1 > LOG2_3,
            }
        )
    return terms, conv


# ---------------------------------------------------------------------------
# 7. trajectories
# ---------------------------------------------------------------------------


def trajectory(q: int, start: int, max_steps: int = 220):
    ns = [start]
    bs = []
    n = start
    seen = {start: 0}
    ending = "cap"
    for _ in range(max_steps):
        t = 3 * n + q
        b = v2(t)
        bs.append(b)
        n = t >> b
        if n in seen:
            ending = "cycle"
            ns.append(n)
            break
        ns.append(n)
        seen[n] = len(ns) - 1
    else:
        ending = "cap"
    rec = {
        "q": q,
        "start": start,
        "n": ns,
        "b": bs,
        "ending": ending,
        "max": max(ns),
        "argmax": ns.index(max(ns)),
        "steps": len(bs),
    }
    if ending == "cycle":
        rec["cycle_enters_at"] = seen[ns[-1]]
    return rec


# ---------------------------------------------------------------------------
# theorem metadata
# ---------------------------------------------------------------------------

THEOREMS = [
    {
        "id": "T0",
        "short": "3 | n  =>  n has no odd predecessor",
        "statement": "q odd, 3 nmid q.  If p is odd and 3|p then p has no odd S_q-predecessor, hence lies on no S_q-cycle.  Every element of every S_q-cycle is coprime to 3.",
        "status": "proved",
        "hypotheses": "q odd, 3 nmid q.  Nothing else.",
        "proof": "3y+q = 2^b p; mod 3 the LHS is q and the RHS is 0, so 3|q -- contradiction.",
        "prior_art": "textbook folklore.  Kaneda, Fib. Quart. 53(2) (2015) p.169; Brox, Acta Arith. 92 (2000); Tao, Forum of Math Pi 10 (2022) e12.  DO NOT CLAIM.",
    },
    {
        "id": "T1",
        "short": "M = q (mod 4)",
        "statement": "M the max of an S_q-cycle => v2(3M+q) >= 2, i.e. 4 | 3M+q, i.e. M = q (mod 4).  q=1: M = 1 (mod 4).",
        "status": "proved",
        "hypotheses": "NONE beyond q>0 odd, 3 nmid q, M the cycle max.  GROUND_TRUTH's 'M > q' is superfluous.",
        "proof": "S_q(M) <= M gives 2^b >= 3 + q/M > 3, so b >= 2.  Refinements: M < q forces b >= 3; M = q forces b = 2 exactly.",
        "prior_art": "Brox 2000 calls such an odd number 'descending' in his opening definitions; the local-max decomposition of Simons-de Weger (Acta Arith. 117 (2005)) builds it in.  DO NOT CLAIM.",
        "corrects_ground_truth": "GROUND_TRUTH says M>q is required for T1 and lists (q=17,{1,5}) and (q=23,{7,11}) as counterexamples.  Both satisfy T1 (v2(32)=5, v2(56)=3).  They are counterexamples to T2 only.",
    },
    {
        "id": "T2",
        "short": "b_1 = 1, so M = 2q (mod 3)",
        "statement": "M the max of an S_q-cycle with M >= q => b_1 = 1: the unique in-cycle odd predecessor of M is y_1 = (2M-q)/3.  Forces 3 | 2M-q, i.e. M = 2q (mod 3); q=1: M = 2 (mod 3).",
        "status": "proved",
        "hypotheses": "M >= q suffices.  'L >= 2' is redundant: M > q already forces L >= 2 (see FP).",
        "proof": "y_b = (2^b M - q)/3 < M <=> M(2^b - 3) < q; for b >= 2 that needs M < q.",
        "tightness": "TIGHT: q=17 cycle {5,1} has M=5<q and b_1=2; q=23 cycle {11,7} has M=11<q and b_1=2.  CONVERSE FALSE: b_1=1 does not imply M>q (e.g. q=11 cycle {7,1}).",
        "prior_art": "the standard local-maximum analysis; Brox's 'descendent', Kaneda 2015 Thm 2.1.  DO NOT CLAIM.",
    },
    {
        "id": "LEMMA-U",
        "short": "at most one odd predecessor below p",
        "statement": "q odd, 3 nmid q, p odd > 0 with 3 nmid p.  Odd predecessors of p are exactly y_b=(2^b p - q)/3 for b >= 1 in one fixed parity class (parity forced by p mod 3), 2^b p > q; y_b is automatically odd and strictly increasing in b.  Hence p has AT MOST ONE odd predecessor strictly below itself, for every q.",
        "status": "proved",
        "hypotheses": "none beyond the above; in particular no relation between p and q.",
        "proof": "y_b < p <=> q/p < 2^b < 3 + q/p, a window of additive length 3; 2^{b+2}-2^b = 3*2^b >= 6 > 3.",
        "prior_art": "elementary/folklore (backward Collatz tree).  DO NOT CLAIM.",
    },
    {
        "id": "T3",
        "short": "M = 5q (mod 12)",
        "statement": "M > q => M = 5q (mod 12).  q=1: M = 5 (mod 12).",
        "status": "proved",
        "hypotheses": "M > q.",
        "proof": "CRT on T1 (M = q mod 4) and T2 (M = 2q mod 3).",
        "prior_art": "not found verbatim in the literature, but it is CRT on two folklore facts.  Describe as 'a folklore corollary', never as a result.",
    },
    {
        "id": "T4",
        "short": "M != 5q (mod 9), i.e. M = 17q or 29q (mod 36)",
        "statement": "M > q => M != 5q (mod 9).  With T3: M = 17q or 29q (mod 36).  q=1: M = 17 or 29 (mod 36).",
        "status": "proved",
        "hypotheses": "M > q (needed: the proof uses b_1 = 1).",
        "proof": "y_1=(2M-q)/3 is on the cycle so 3 nmid y_1; 3|y_1 <=> 9|2M-q <=> M = 5q (mod 9).",
        "tightness": "TIGHT: cycles with M = 5q (mod 9) exist and all have M < q or L = 1 -- e.g. q=119 M=19, q=355 M=47, q=503 M=67, q=833 M=133.",
        "prior_art": "the 3-adic predecessor-set pruning is standard; Wirsching, Springer LNM 1681 (1998) is the book-length treatment.  Not found verbatim.",
        "corrects_ground_truth": "GROUND_TRUTH's 'recurses to higher powers of 3' is misleading.  T0 ALONE saturates at M = 2,8 (mod 9): the surviving set mod 3^{k+1} stays exactly 2*3^{k-1} classes (density 2/9) at every depth.  Every further 3-adic gain comes from the SIZE condition T6, not from T0.",
    },
    {
        "id": "T5",
        "short": "b_2 <= 2 once M > 11q/7",
        "statement": "CORRECTED: M the max of an S_q-cycle with M > 11q/7 => b_2 <= 2.  (GROUND_TRUTH's q=1, M>=2 version is true; its 'L >= 3' hypothesis is wrong.)",
        "status": "proved",
        "hypotheses": "M > 11q/7, strict.  NO length hypothesis.",
        "proof": "y_2 = (2^{1+b_2}M - (2^{b_2}+3)q)/9 <= M gives M(2^{1+b_2}-9) <= (2^{b_2}+3)q; for b_2>=3 this forces M <= (2^{b_2}+3)q/(2^{1+b_2}-9) <= 11q/7.",
        "tightness": "SHARP: 7M = 11q admits b_2 = 3 -- (q=7,M=11), (q=35,M=55), (q=49,M=77), (q=77,M=121), ...",
        "corrects_ground_truth": "GROUND_TRUTH says T5 needs L >= 3 'else y_2 = M wraps'.  FALSE: q=37, cycle 53 -> 49 -> 23 -> 53 has L=3, M=53>q=37, y_2=49<M (no wrap) and b_2=3.  And the q=7,M=11 example is not a wrap artifact: there the exact inequality holds with EQUALITY (77 <= 77) because 7M = 11q.",
        "prior_art": "the local-max neighbourhood arithmetic of Steiner (1977) / Simons (Math. Comp. 74 (2005)).  Not found verbatim; a trivial sharpening.",
    },
    {
        "id": "T6",
        "short": "y_k <= M  <=>  M(2^{B_k} - 3^k) <= c_k",
        "statement": "Exact.  For M above a (small!) threshold this is equivalent to B_k <= floor(k log2 3).",
        "status": "proved",
        "hypotheses": "the floor form needs M > max_{j<=k} g(j); see sieve_layers.floor_rule_thresholds.",
        "corrects_ground_truth": "GROUND_TRUTH's 'M >= 2^68' is wildly over-conservative: for all k <= 20 the floor rule is equivalent to the exact test as soon as M > 17344, and g(2) = 1 reproduces T5's 'M >= 2'.",
        "prior_art": "standard.  Kaneda 2015 Thm 2.1 inequality (2.3) is the mirror image (from the minimum); same device in Eliahou (Discrete Math. 118 (1993)), Halbeisen-Hungerbuehler (Acta Arith. 78 (1997)), Simons-de Weger (2005).  DO NOT CLAIM.",
    },
    {
        "id": "T7",
        "short": "M(2^B - 3^L) = c_L > 0",
        "statement": "The cycle equation; forces 2^B > 3^L and B/L > log2 3, and closing a cycle needs 2^B/3^L within ~1/M of 1.",
        "status": "proved",
        "prior_art": "Boehm & Sontacchi, Atti Accad. Naz. Lincei 64 (1978) 260-264 (already Lean-formalised at ccchallenge.org); the Diophantine consequence is Crandall, Math. Comp. 32 (1978) 1281-1292, via Baker 1968 / Rhin 1987.  ABSOLUTELY NOT NEW.",
    },
    {
        "id": "T8",
        "short": "M != 9 (mod 16)",
        "statement": "q=1: the max odd of a cycle satisfies M != 9 (mod 16).  With T3: M = 5, 17 or 29 (mod 48).",
        "status": "proved",
        "hypotheses": "none (no size hypothesis).",
        "proof": "M=16s+9 => 3M+1 = 4(12s+7), v2 = 2 exactly, x_1 = 12s+7; 3x_1+1 = 2(18s+11), v2 = 1 exactly, x_2 = 18s+11 > 16s+9 = M for every s >= 0, contradicting maximality.",
        "prior_art": "elementary; almost certainly folklore.  This is the j=2 case of the standard forward coefficient-stopping-time sieve (Terras, Acta Arith. 30 (1976)).",
    },
    {
        "id": "FP",
        "short": "M > q  =>  L >= 2",
        "statement": "Every S_q fixed point satisfies n(2^b - 3) = q with b >= 2, hence n <= q.  So the 'L >= 2' hypothesis in T2/T3/T4 is redundant given M > q.",
        "status": "proved",
    },
    {
        "id": "FALSE-1",
        "short": "B_k <= floor(k log2 3) unconditionally",
        "statement": "FALSE.  c_k grows like 2^{B_k}, not O(1).  Real counterexample: q=5, cycle 49 -> 19 -> 31 -> 49 has M=49 and B_3 = 5 > 4 = floor(3 log2 3).",
        "status": "refuted",
    },
    {
        "id": "FALSE-2",
        "short": "the T4 recursion is a forced chain at every depth",
        "statement": "FALSE from depth 4 on.  The prefix (b_1,b_2,b_3,b_4) = (1,1,1,3) has B_4 = 6 and 2^6 = 64 < 81 = 3^4, so the size test y_4 <= M is vacuous there and b_4 is not determined.  The recursion is a BRANCHING sieve, not a forced chain.",
        "status": "refuted",
    },
]

NOVELTY_NOTE = (
    "Nothing in T0-T8 is new.  T0/T1/T6/T7 are published (some 45+ years ago); "
    "T2 is the literature's standard local-maximum analysis; T3/T4/T5/T8 are one-line "
    "corollaries of folklore that were not found written verbatim -- the weakest "
    "possible form of novelty, and not to be presented as a result.  The floor "
    "(backward) / ceiling (forward) parity-vector machinery is the standard "
    "Eliahou / Simons-de Weger apparatus.  Cautionary precedent: Kaneda's own "
    "acknowledgements (Fib. Quart. 53(2), p.174) record that Lagarias and a referee "
    "told him his Section 2 results were not new, only the proofs."
)


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=None)
    ap.add_argument("--tree-depth", type=int, default=13)
    ap.add_argument("--sieve3-depth", type=int, default=10)
    ap.add_argument("--sieve2-bits", type=int, default=14)
    ap.add_argument("--wheel-odds", type=int, default=10000)
    ap.add_argument("--dio-L", type=int, default=200)
    ap.add_argument("--dio-records-L", type=int, default=20000)
    ap.add_argument("--verify-odds", type=int, default=60000)
    args = ap.parse_args()

    here = __file__
    repo = here[: here.index("/python/tools/")]
    out_path = args.out or (repo + "/web/data.json")

    data: dict = {}

    # ---- meta ------------------------------------------------------------
    data["meta"] = {
        "title": "Collatz max-odd sieve -- visualisation data",
        "generated_by": "python/tools/gen_viz_data.py",
        "generated_date": "2026-08-26",
        "python": sys.version.split()[0],
        "map": "S_q(n) = (3n+q)/2^b, b = v2(3n+q), n odd, q odd, 3 nmid q",
        "notation": {
            "L": "number of odd elements of a cycle",
            "M": "largest odd element of a cycle",
            "B": "total halvings around the cycle",
            "y_k": "k-th odd predecessor going backward from M (y_0 = M)",
            "b_k": "halvings on the k-th backward hop: 3 y_k + q = 2^{b_k} y_{k-1}",
            "B_k": "b_1 + ... + b_k",
            "c_k": "c_k = 2^{b_k} c_{k-1} + 3^{k-1} q, c_0 = 0; y_k = (2^{B_k} M - c_k)/3^k",
            "a_j": "forward halvings: x_j = (3 x_{j-1} + q)/2^{a_j}, x_0 = M.  b_j = a_{L+1-j}",
        },
        "log2_3": r6(LOG2_3),
        "novelty_note": NOVELTY_NOTE,
        "literature": LITERATURE,
    }

    data["theorems"] = THEOREMS

    # ---- 3-adic sieve (needed by the wheel) ------------------------------
    surv3 = mod3_sieve_vectors(args.sieve3_depth)
    # depth-0 layer: T2 alone, M = 2 (mod 3)
    surv3_full = {0: (3, [2])}
    surv3_full.update(surv3)

    # ---- 1. mod-12 wheel -------------------------------------------------
    wheel_str, wheel_counts, per_mod12, level_counts = build_wheel(
        args.wheel_odds, surv3_full, min(args.sieve3_depth, 9)
    )
    data["wheel"] = {
        "description": (
            "Classification of odd n = 1,3,5,... as candidates for being the largest odd "
            "element M of a q=1 cycle.  One character per odd number, index i <-> n = 2i+1."
        ),
        "n_odds": args.wheel_odds,
        "max_n": 2 * args.wheel_odds - 1,
        "legend": {
            "a": {
                "rule": "T1",
                "cond": "n = 3 (mod 4)",
                "why": "3n+1 = 2 (mod 4), so v2 = 1 and S(n) = (3n+1)/2 > n: n ascends, cannot be the max",
                "density_of_odds": 0.5,
            },
            "b": {
                "rule": "T0",
                "cond": "3 | n",
                "why": "3y+1 is never divisible by 3, so n has no odd predecessor at all",
                "density_of_odds": r6(1 / 3),
            },
            "c": {
                "rule": "T2",
                "cond": "n = 1 (mod 3)",
                "why": "then (2n-1)/3 is not an integer; the parity of b is forced even, and every odd predecessor (4n-1)/3, (16n-1)/3, ... exceeds n",
                "density_of_odds": r6(1 / 3),
            },
            "digit": "survives the mod-12 wheel (n = 5 mod 12); the digit is the deepest 3-adic sieve level k it also survives (see sieve_layers.mod3)",
        },
        "priority": list(RULE_PRIORITY),
        "codes": wheel_str,
        "counts": wheel_counts,
        "per_mod12": {str(k): v for k, v in per_mod12.items()},
        "deep_level_counts": {str(k): v for k, v in sorted(level_counts.items())},
        "survivor_class": {"modulus": 12, "residues": [5]},
        "caveat": (
            "Rules a/b/c are exclusions for the maximum of a q=1 cycle with M > q = 1, i.e. for "
            "n >= 3.  n = 1 IS the maximum of the trivial cycle {1} and is nevertheless labelled "
            "'c' -- that single index is the one place the wheel over-claims, because T2 needs "
            "M > q strictly (at M = q the 'predecessor' of M is M itself).  "
            "The DIGIT (deep level) is only a valid exclusion for M above the corresponding "
            "threshold in sieve_layers.floor_rule_thresholds -- do not colour a small n "
            "'excluded at level 6' without saying so."
        ),
        "known_exception_index": 0,
    }

    # ---- 2. backward tree ------------------------------------------------
    levels, child_strings = build_tree(args.tree_depth)
    depth_stats = []
    for k in range(1, args.tree_depth + 1):
        Bs = levels[k]
        hist: dict[int, int] = {}
        for B in Bs:
            hist[B] = hist.get(B, 0) + 1
        bmin = min(hist)
        depth_stats.append(
            {
                "k": k,
                "N": len(Bs),
                "cap": floor_klog2_3(k),
                "B_min": bmin,
                "B_max": max(hist),
                "B_hist_from": bmin,
                "B_hist": [hist.get(B, 0) for B in range(bmin, max(hist) + 1)],
                "drift_min": r6(bmin - k * LOG2_3),
                "drift_max": r6(max(hist) - k * LOG2_3),
            }
        )
    Nk = tree_counts_dp(40)
    lam = growth_constant()
    data["backward_tree"] = {
        "description": (
            "Surviving backward halving-vectors (b_1..b_k) from M, for q=1 and M large "
            "enough that T6's exact test is the floor rule.  b_1 = 1 is forced (that is T2)."
        ),
        "rule": "b_j >= 1 and B_j <= floor(j*log2 3) for every j <= k",
        "max_depth": args.tree_depth,
        "encoding": (
            "child_counts[k-1] is a digit string, one digit per node at depth k-1 (in canonical "
            "order), giving how many children it has.  A node at depth k-1 with prefix sum B has "
            "exactly children b = 1..(floor(k*log2 3) - B), in that order.  Root = depth 0, B_0 = 0. "
            "Reconstruct: B_k = B_{k-1} + b.  drift_k = B_k - k*log2(3) (always <= 0); "
            "ratio 2^{B_k}/3^k = 2^{drift_k}."
        ),
        "child_counts": child_strings,
        "depth_stats": depth_stats,
        "N_k": Nk,
        "N_k_note": "N(k) for k = 1..40, by DP over prefix sums; matches the explicit tree for k <= max_depth.  Unconstrained would be 8^k-ish.",
        "growth": {
            "lambda": r6(lam),
            "log2_lambda": r6(math.log2(lam)),
            "formula": "lambda = a^a/(a-1)^(a-1) with a = log2 3",
            "fit": "N(k) ~ 1.235 * lambda^k * k^(-1.51) empirically over k = 100..300 (the k^(-3/2) is the standard ballot/first-passage correction)",
            "ratios": [r6(Nk[i] / Nk[i - 1]) for i in range(1, len(Nk))],
        },
        "sturmian": {
            "note": "the step word w_k = floor(k lg3) - floor((k-1) lg3) in {1,2} is Sturmian with slope lg3 - 1",
            "word": "".join(
                str(floor_klog2_3(k) - floor_klog2_3(k - 1)) for k in range(1, 61)
            ),
        },
    }

    # ---- 2b/3. sieve layers ---------------------------------------------
    g = floor_rule_thresholds(min(args.tree_depth, 20))
    surv2 = mod2_sieve(args.sieve2_bits)
    lim2 = mod2_limit_density(3000, 60)

    mod3_layers = []
    for k in range(1, args.sieve3_depth + 1):
        mod, res = surv3[k]
        row = {
            "k": k,
            "modulus": mod,
            "count": len(res),
            "density_of_all": r6(len(res) / mod),
            "N_k": len(levels[k]) if k < len(levels) else None,
        }
        if k <= 6:
            row["residues"] = res
        mod3_layers.append(row)

    mod2_layers = []
    for a in range(2, args.sieve2_bits + 1):
        res = surv2[a]
        row = {
            "a": a,
            "modulus": 1 << a,
            "count": len(res),
            "density_of_odds": r6(len(res) / (1 << (a - 1))),
        }
        if a <= 8:
            row["residues"] = res
        mod2_layers.append(row)
    # newly killed classes
    for i in range(1, len(mod2_layers)):
        a = mod2_layers[i]["a"]
        prev = set(surv2[a - 1])
        killed = [r for r in range(1, 1 << a, 2) if (r % (1 << (a - 1))) in prev and r not in set(surv2[a])]
        mod2_layers[i]["newly_killed_count"] = len(killed)
        if len(killed) <= 10:
            mod2_layers[i]["newly_killed"] = killed

    combined = []
    for k in range(1, args.sieve3_depth + 1):
        a = min(args.sieve2_bits, 2 * k + 2)
        d3 = len(surv3[k][1]) / surv3[k][0]
        d2 = len(surv2[a]) / (1 << (a - 1))
        # d3 is a density among ALL integers; among odd integers the 3-adic
        # condition has the same density (3^{k+1} is odd), so the joint density
        # among odds is d3 * 3^{k+1}/3^{k+1} ... = d3 * (density among odds is d3
        # since residues mod an odd modulus are equidistributed on the odds)
        combined.append(
            {
                "k": k,
                "a": a,
                "modulus_bits": r6((k + 1) * LOG2_3 + a),
                "density_among_odds": r6(d3 * d2),
                "bits_removed": r6(-math.log2(d3 * d2)),
                "one_in": r6(1 / (d3 * d2)),
            }
        )

    data["sieve_layers"] = {
        "description": "Two independent sieves on the residue of M, plus their CRT product.",
        "mod3": {
            "what": (
                "3-adic: for each floor-admissible backward vector at depth k, M mod 3^k is pinned "
                "and T0 (3 nmid y_k) kills one of the three lifts to mod 3^{k+1}.  Survivors = union."
            ),
            "requires": "M > max_{j<=k} floor_rule_thresholds[j] (else use T6's exact test)",
            "layers": mod3_layers,
            "t0_only_saturates": {
                "note": (
                    "WITHOUT the size condition, T0 alone gives nothing past mod 9: the survivor set "
                    "is always exactly M = 2, 8 (mod 9) lifted, i.e. 2*3^{k-1} of 3^{k+1} classes, "
                    "density 2/9 at every depth.  Reason: 2 has order 6 mod 9, so both parities of "
                    "b_{j+1} still realise all three residues of y_{j+1} mod 3, and a legal b_{j+1} "
                    "always exists.  GROUND_TRUTH's 'T4 recurses to higher powers of 3' is misleading."
                ),
                "density": r6(2 / 9),
            },
        },
        "mod2": {
            "what": (
                "2-adic: the forward mirror.  x_j = (3 x_{j-1}+1)/2^{a_j} <= M for all j <=> "
                "A_j >= ceil(j log2 3); a_j depends only on low bits of M, so this is a mod-2^a "
                "condition.  a=2 is T1; the first genuine refinement is at a=4 (T8: M != 9 mod 16)."
            ),
            "layers": mod2_layers,
            "limiting_density_among_odds": r6(lim2),
            "limit_note": (
                "SATURATES.  The whole forward 2-adic sieve is worth about "
                f"{-math.log2(lim2):.4f} bits, forever; extra depth buys nothing.  "
                "This is the negative-drift random-walk survival probability "
                "(Terras coefficient-stopping-time framework)."
            ),
            "hard_classes": {
                "mod16": [1, 5, 13],
                "mod48": [5, 17, 29],
                "note": "mod48 = mod16 refinement intersected with T3 (M = 5 mod 12)",
            },
        },
        "combined_crt": {
            "note": (
                "The moduli 2^a and 3^{k+1} are coprime so the densities multiply.  CAVEAT: this is "
                "exact as a statement about residue classes surviving two independently defined "
                "sieves; it is a joint statement about an actual cycle only when L >= k + j + 1, so "
                "that the k backward and j forward elements from M are distinct."
            ),
            "rows": combined,
            "verdict": (
                "The sieve cannot close the problem: the 2-adic half caps at "
                f"{-math.log2(lim2):.2f} bits and the 3-adic half decays at best geometrically in k "
                "while the modulus grows 1.585 bits per k.  The surviving-class COUNT grows."
            ),
        },
        "floor_rule_thresholds": {
            "note": (
                "g(k) = the largest M for which T6's exact test M(2^{B_k}-3^k) <= c_k still admits a "
                "vector that the floor rule B_k <= floor(k lg3) rejects.  So the floor rule is "
                "equivalent to T6 for all depths <= k as soon as M > max_{j<=k} g(j).  "
                "g(2) = 1 reproduces T5's 'M >= 2' (sharp ratio 11q/7); GROUND_TRUTH's 2^68 is "
                "wildly over-conservative."
            ),
            "g": {str(k): v for k, v in g.items()},
            "running_max": {
                str(k): max(g[j] for j in range(1, k + 1)) for k in sorted(g)
            },
        },
    }

    # ---- verification ----------------------------------------------------
    ver_depth = 4
    lo = 1_000_001
    observed = {k: set() for k in range(1, ver_depth + 1)}
    n_checked = 0
    for i in range(args.verify_odds):
        M = lo + 2 * i
        if M % 4 != 1 or M % 3 == 0:
            continue
        n_checked += 1
        for k in range(1, ver_depth + 1):
            if honest_backward_check(M, k):
                observed[k].add(M % (3 ** (k + 1)))
            else:
                break
    ver_rows = []
    for k in range(1, ver_depth + 1):
        pred = set(surv3[k][1])
        obs = observed[k]
        ver_rows.append(
            {
                "k": k,
                "modulus": 3 ** (k + 1),
                "predicted": len(pred),
                "observed": len(obs),
                "extra": sorted(obs - pred),
                "missing": sorted(pred - obs),
                "match": obs == pred,
            }
        )
    # forward / 2-adic empirical check on real integers
    f_lo = (1 << 24) + 1
    f_n = 120_000
    f_hits = 0
    f_obs = {a: set() for a in range(2, 11)}
    for i in range(f_n):
        M = f_lo + 2 * i
        if forward_max_check(M):
            f_hits += 1
            for a in f_obs:
                f_obs[a].add(M % (1 << a))
    fwd_rows = []
    for a in sorted(f_obs):
        pred = set(surv2[a])
        fwd_rows.append(
            {
                "a": a,
                "predicted": len(pred),
                "observed": len(f_obs[a]),
                "observed_subset_of_predicted": f_obs[a] <= pred,
                "extra": sorted(f_obs[a] - pred),
            }
        )

    data["verification"] = {
        "forward_2adic": {
            "method": (
                f"For {f_n} real odd M starting at 2^24+1, run the full forward Syracuse orbit "
                "to 1 and keep M iff no x_j exceeds M.  Compare the observed residues mod 2^a "
                "against the predicted survivor sets, and the observed density against the "
                "DP limit."
            ),
            "M_checked": f_n,
            "M_kept": f_hits,
            "observed_density": r6(f_hits / f_n),
            "predicted_limit": r6(lim2),
            "rows": fwd_rows,
            "all_subset": all(r["observed_subset_of_predicted"] for r in fwd_rows),
        },
        "backward_3adic": {
            "method": (
                "Honest backward DFS on REAL integers M in [1000001, 1000001+2*"
                f"{args.verify_odds}), q=1, using only the exact tests y_j <= M, 3 nmid y_j and "
                "integrality.  No residue arithmetic, no floor rule, and b_1 = 1 is NOT assumed "
                "(it comes out as an output).  Compared against the residue-derived "
                "mod-3^{k+1} survivor sets."
            ),
            "M_checked": n_checked,
            "rows": ver_rows,
            "all_match": all(r["match"] for r in ver_rows),
        },
        "self_checks": {
            "N_k_matches_ground_truth_1_2_3_7_12": Nk[:5] == [1, 2, 3, 7, 12],
            "mod12_survivor_is_5": sorted(
                r for r in range(1, 12, 2) if wheel_rule(r) is None
            )
            == [5],
            "T8_mod16_survivors": surv2[4] == [1, 5, 13],
            "g2_reproduces_T5_threshold": g[1] == 1 and g[2] == 1,
        },
    }

    # ---- 4. real cycles --------------------------------------------------
    qs = [q for q in range(1, 102, 2) if q % 3 != 0]
    qs += [119, 143, 161, 169, 175, 185, 299, 355, 503, 595, 833, 877]
    cycles = []
    for q in qs:
        max_start = max(400, 30 * q)
        for cyc in find_cycles(q, max_start, 5_000_000, 4000):
            rec = describe_cycle(q, cyc)
            if rec["L"] > 60:
                rec["odds"] = rec["odds"][:60]
                rec["a"] = rec["a"][:60]
                rec["truncated"] = True
            cycles.append(rec)
    cycles.sort(key=lambda r: (r["q"], r["M"]))

    def summarise(pred, field):
        sel = [c for c in cycles if pred(c)]
        good = [c for c in sel if c["chk"][field] is True]
        return {"applicable": len(sel), "holds": len(good), "fails": len(sel) - len(good)}

    data["cycles"] = {
        "description": (
            "All S_q cycles found by exhaustive forward search from every odd start <= "
            "max(400, 30q), value cap 5e6, step cap 4000, for the listed q.  This finds every "
            "cycle having an element in that range; it is NOT a proof that no other cycle exists "
            "for these q."
        ),
        "q_values": qs,
        "count": len(cycles),
        "fields": {
            "odds": "the cycle's odd elements in FORWARD order starting at M",
            "a": "forward halvings, a_j = v2(3*odds[j-1]+q); sum = B",
            "b": "backward halvings = reverse(a); b_1 = a[L-1] is the hop into M",
            "chk": (
                "per-cycle theorem verdicts, null = not applicable (L = 1).  "
                "cmp = sign of M-q; r = M/q; b1,b2 = first two BACKWARD halvings; "
                "T0: every element coprime to 3.  T1: (M-q)%4 == 0.  T2: b1 == 1 "
                "(claimed only when M > q).  T3: (M-5q)%12 == 0 (only when M > q).  "
                "T4: (M-5q)%9 != 0 (only when M > q).  T5: b2 <= 2 (only when 7M > 11q)."
            ),
        },
        "list": cycles,
        "summary": {
            "T1_M_eq_q_mod4_all": summarise(lambda c: True, "T1"),
            "T0_all": summarise(lambda c: True, "T0"),
            "T2_given_M_gt_q": summarise(lambda c: c["M"] > c["q"], "T2"),
            "T2_given_M_ge_q_INCLUDING_FIXED_POINTS": summarise(
                lambda c: c["M"] >= c["q"], "T2"
            ),
            "T3_given_M_gt_q": summarise(lambda c: c["M"] > c["q"], "T3"),
            "T4_given_M_gt_q": summarise(lambda c: c["M"] > c["q"], "T4"),
            "T5_given_M_gt_11q_7": summarise(
                lambda c: 7 * c["M"] > 11 * c["q"] and c["L"] >= 2, "T5"
            ),
            "T5_bad_hypothesis_L_ge_3": summarise(
                lambda c: c["L"] >= 3 and c["M"] > c["q"], "T5"
            ),
        },
        "size_refinements": {
            "note": (
                "T1's refinements by the sign of M - q.  The hypothesis M > q works the OPPOSITE "
                "way from what GROUND_TRUTH suggests: M < q gives a STRICTLY STRONGER conclusion."
            ),
            "M_lt_q": {
                "count": sum(1 for c in cycles if c["M"] < c["q"]),
                "all_v2_ge_3": all(c["a"][0] >= 3 for c in cycles if c["M"] < c["q"]),
                "claim": "M < q => v2(3M+q) >= 3, i.e. 8 | 3M+q",
            },
            "M_eq_q": {
                "count": sum(1 for c in cycles if c["M"] == c["q"]),
                "all_L_1": all(c["L"] == 1 for c in cycles if c["M"] == c["q"]),
                "all_v2_eq_2": all(c["a"][0] == 2 for c in cycles if c["M"] == c["q"]),
                "claim": "M = q => M is a fixed point (L = 1) and v2(3M+q) = 2 exactly",
            },
            "fixed_points": {
                "count": sum(1 for c in cycles if c["L"] == 1),
                "all_M_le_q": all(c["M"] <= c["q"] for c in cycles if c["L"] == 1),
                "claim": "FP: n(2^b - 3) = q with b >= 2, so every fixed point has M <= q; hence M > q => L >= 2",
            },
            "sharp_T5_threshold": {
                "note": "cycles with 7M = 11q exactly -- the sharp T5 threshold; all have b_2 = 3",
                "count": sum(1 for c in cycles if 7 * c["M"] == 11 * c["q"]),
                "all_b2_is_3": all(
                    c["chk"]["b2"] == 3 for c in cycles if 7 * c["M"] == 11 * c["q"]
                ),
                "examples": [
                    [c["q"], c["M"]] for c in cycles if 7 * c["M"] == 11 * c["q"]
                ],
            },
        },
        "summary_note": (
            "T2_given_M_ge_q_INCLUDING_FIXED_POINTS fails exactly on the M = q fixed points "
            "(L = 1, b = 2), where the 'predecessor' of M is M itself -- so the honest hypothesis "
            "for T2 is M > q (equivalently M >= q AND L >= 2).  "
            "T5_bad_hypothesis_L_ge_3 is the row that REFUTES GROUND_TRUTH's 'T5 needs L >= 3': "
            "there are cycles with L >= 3, M > q and b_2 = 3.  The size hypothesis M > 11q/7 "
            "has no failures."
        ),
        "T5_L_ge_3_counterexamples": [
            {"q": c["q"], "M": c["M"], "L": c["L"], "b2": c["chk"]["b2"], "M_over_q": c["chk"]["r"]}
            for c in cycles
            if c["L"] >= 3 and c["M"] > c["q"] and c["chk"]["T5"] is False
        ],
        "highlights": {
            "q17_1_5": "M = 5 < q = 17, b_1 = 2 -- T2 fails, but T1 holds (v2(3*5+17)=v2(32)=5)",
            "q23_7_11": "M = 11 < q = 23, b_1 = 2 -- same story (v2(3*11+23)=v2(56)=3)",
            "q7_5_11": "M = 11 > q = 7 but 7M = 11q exactly, the SHARP T5 threshold: b_2 = 3",
            "q37_23_49_53": "L = 3, M = 53 > q = 37, y_2 = 49 < M (no wrap), b_2 = 3 -- kills the 'L >= 3' hypothesis",
            "q5_49_19_31": "M = 49, B_3 = 5 > 4 = floor(3 lg3) -- the FALSE-1 counterexample",
        },
    }

    # ---- 5. Diophantine --------------------------------------------------
    cf_terms, conv = cf_log2_3(14)
    rows = diophantine_table(args.dio_L)
    recs = diophantine_records(args.dio_records_L)
    best = max(rows, key=lambda r: r["min_bound"])
    data["diophantine"] = {
        "description": (
            "T7 forces 2^B > 3^L, so B = floor(L log2 3) + 1 at best.  Writing "
            "2^B = prod over the cycle of (3 + q/n_i) and using min <= n_i <= M gives "
            "1/excess >= min  and  M >= 1/excess, with excess = 2^{B/L} - 3.  So a cycle of "
            "length L is possible only if its minimum element is at most 1/excess(L)."
        ),
        "columns": ["L", "B", "drift = B - L*log2 3", "excess = 2^{B/L} - 3", "min_bound = 1/excess"],
        "rows": rows,
        "records": recs,
        "records_note": (
            f"Every L <= {args.dio_records_L} at which min_bound sets a new record.  The best of "
            f"them, L = {recs[-1]['L']}, still only permits a cycle minimum of "
            f"{recs[-1]['min_bound']:.3g} -- about "
            f"1e{math.log10(LITERATURE['verification_limit']['approx'] / recs[-1]['min_bound']):.0f} "
            "times below the verified bound.  Note L = 1 gives min_bound = 1: the only q=1 "
            "fixed point is 1 itself (the L=1 case of Steiner's no-nontrivial-circuit theorem)."
        ),
        "records_max": recs[-1],
        "best_in_table": best,
        "verdict": (
            "For every L <= "
            f"{args.dio_L} the bound on the cycle minimum is at most {best['min_bound']:.0f} "
            f"(at L = {best['L']}), which is ~1e{math.log10(LITERATURE['verification_limit']['approx'] / best['min_bound']):.0f} "
            "times below Barina's verified bound of 2075*2^60.  So no q=1 cycle of any of these "
            "lengths exists -- the approximation B/L to log2 3 has to be astronomically good."
        ),
        "verification_limit": LITERATURE["verification_limit"],
        "cf_log2_3": {"terms": cf_terms, "convergents": conv},
    }

    # ---- 6. trajectories -------------------------------------------------
    traj_specs = [
        (1, 1, "the only known q=1 cycle: fixed point 1 -> 1"),
        (1, 5, "5 = 5 (mod 12) survives the wheel, yet falls: 5 -> 1"),
        (1, 7, "the user's seed: 3*7+1 = 22, next odd is 11 > 7, so 7 ascends.  7 = 3 (mod 4) = T1"),
        (1, 9, "T8 in action: 9 = 9 (mod 16), and 9 -> 7 -> 11 with 11 > 9, so 9 cannot be a maximum.  Generally M=16s+9 gives x_1 = 12s+7 then x_2 = 18s+11 > M"),
        (1, 11, "11 = 3 (mod 4) so T1 excludes it -- NOT because 'you need a bigger odd to reach 11' (7 -> 11 with 7 < 11)"),
        (1, 27, "the classic: 41 odd steps, peaks at 3077"),
        (1, 41, "41 = 5 (mod 12), survives the wheel"),
        (1, 97, "97 = 1 (mod 12) -- excluded by T2 (rule c)"),
        (1, 703, "long climb, peaks high"),
        (1, 871, "another long one"),
        (5, 49, "q=5 cycle 49 -> 19 -> 31 -> 49; B_3 = 5 > floor(3 lg3) = 4 (FALSE-1)"),
        (7, 5, "q=7 cycle 5 -> 11 -> 5; 7M = 11q exactly, the sharp T5 threshold"),
        (17, 1, "q=17 cycle 1 -> 5 -> 1; M = 5 < q so T2 fails, b_1 = 2"),
        (23, 7, "q=23 cycle 7 -> 11 -> 7; M = 11 < q, b_1 = 2"),
        (37, 53, "q=37 cycle 53 -> 49 -> 23 -> 53: L=3, M=53>q=37, y_2=49<M (no wrap), b_2=3 -- refutes the 'L>=3' hypothesis for T5"),
    ]
    trajs = []
    for q, s, note in traj_specs:
        t = trajectory(q, s)
        t["note"] = note
        trajs.append(t)
    data["trajectories"] = {
        "description": (
            "Odd-step (Syracuse) trajectories.  n[i] are the odd values, b[i] = v2(3*n[i]+q) the "
            "halvings, n[i+1] = (3*n[i]+q)>>b[i].  Step i ASCENDS iff n[i+1] > n[i] iff "
            "2^{b[i]} < 3 + q/n[i] (for q=1 and n>1 that is exactly b[i] == 1)."
        ),
        "tag_rule": "ascend iff 2^b < 3 + q/n; descend otherwise",
        "list": trajs,
    }

    # ---- write -----------------------------------------------------------
    with open(out_path, "w") as f:
        json.dump(data, f, separators=(",", ":"))
    size = len(json.dumps(data, separators=(",", ":")))
    print(f"wrote {out_path}  ({size} bytes, {size/1024:.1f} KiB)")
    print("top-level keys:", ", ".join(data.keys()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
