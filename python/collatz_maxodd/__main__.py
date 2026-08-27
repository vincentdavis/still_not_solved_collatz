"""``python -m collatz_maxodd`` -- a readable report on the max-odd sieve.

Everything printed is computed from scratch by this package.  See the honesty
banner at the top of the output: none of these facts are new.
"""

from __future__ import annotations

import argparse

from . import backtree, cycleeq, cycles, sieve

BANNER = """\
================================================================================
collatz_maxodd -- residue restrictions on the largest ODD element M of a 3n+q cycle
================================================================================
S_q(n) = (3n + q) / 2^b,  b = v2(3n + q) >= 1,  n odd, q odd, 3 does not divide q
L = #odd elements, M = largest odd element, B = total halvings.  q = 1 is Collatz.

HONESTY BANNER.  Nothing in this package is new mathematics.
  T0 (no odd multiple of 3 has an odd predecessor) is stated verbatim by
     Kaneda, Fibonacci Quart. 53(2) (2015) 168-174, and is why Tao's Syracuse
     map is defined on the odds coprime to 3.
  T1 (the cycle max needs >= 2 halvings) is Brox's "descending" condition,
     Acta Arith. 92 (2000) 181-188, and the local-max structure of
     Simons & de Weger, Acta Arith. 117 (2005) 51-70.
  T6/T7 (the exponent-vector inequality and the cycle equation) are
     Boehm & Sontacchi 1978, Crandall 1978, Eliahou 1993 -- the cycle equation
     is already formalised in Lean at ccchallenge.org.
  T3/T4/T5 and the mod-16 refinement are one-line corollaries of that folklore.
  This sieve CANNOT close the problem: the 2-adic half saturates at 1.80 bits,
  and the 3-adic half decays only geometrically while the modulus grows faster.
================================================================================
"""


def _rule(title: str) -> str:
    return f"\n--- {title} " + "-" * max(0, 76 - len(title)) + "\n"


def report(q_max: int, bound: int, depth: int, mod2_depth: int) -> str:
    out: list[str] = [BANNER]

    # ------------------------------------------------------------------ cycles
    qs = [q for q in range(1, q_max + 1, 2) if q % 3]
    found = cycles.find_cycles_multi(qs, bound)
    multi = [c for c in found if c.L >= 2]
    out.append(
        _rule("CYCLES FOUND")
        + f"q odd, 3 does not divide q, q <= {q_max}; all cycles with M <= {bound}\n"
        f"{len(found)} cycles ({len(multi)} with L >= 2, "
        f"{len(found) - len(multi)} fixed points)\n"
        f"{sum(1 for c in found if c.M > c.q)} with M > q, "
        f"{sum(1 for c in found if c.M < c.q)} with M < q, "
        f"{sum(1 for c in found if c.M == c.q)} with M = q\n"
    )
    out.append("  q=1  : " + ", ".join(str(c.elements) for c in found if c.q == 1) + "\n")
    for qq in (5, 7, 17, 23, 37):
        sel = [c for c in found if c.q == qq]
        if sel:
            out.append(f"  q={qq:<4}: " + ", ".join(str(c.elements) for c in sel) + "\n")

    # ------------------------------------------------------------------ claims
    def frac(pred, hyp) -> str:
        sub = [c for c in found if hyp(c)]
        good = sum(1 for c in sub if pred(c))
        return f"{good}/{len(sub)}"

    always = lambda c: True  # noqa: E731
    mgtq = lambda c: c.M > c.q  # noqa: E731
    out.append(
        _rule("CLAIMS CHECKED AGAINST EVERY CYCLE FOUND")
        + f"T0  every element coprime to 3                : "
        f"{frac(lambda c: all(z % 3 for z in c.elements), always)}\n"
        f"T1  M = q (mod 4)              [no hypothesis]  : "
        f"{frac(lambda c: sieve.t1_ok(c.M, c.q), always)}\n"
        f"T1' M < q  =>  8 | 3M + q                       : "
        f"{frac(lambda c: (3 * c.M + c.q) % 8 == 0, lambda c: c.M < c.q)}\n"
        f"T2  b_1 = 1                    [M > q]          : "
        f"{frac(lambda c: c.b1 == 1, mgtq)}\n"
        f"T2x b_1 = 1                    [M >= q]         : "
        f"{frac(lambda c: c.b1 == 1, lambda c: c.M >= c.q)}"
        "   <-- M >= q is NOT enough (M = q is a fixed point)\n"
        f"T3  M = 5q (mod 12)            [M > q]          : "
        f"{frac(lambda c: sieve.t3_ok(c.M, c.q), mgtq)}\n"
        f"T4  M != 5q (mod 9)            [M > q]          : "
        f"{frac(lambda c: sieve.t4_ok(c.M, c.q), mgtq)}\n"
        f"T5  b_2 <= 2                   [M > 11q/7]      : "
        f"{frac(lambda c: c.b(2) <= 2, lambda c: 7 * c.M > 11 * c.q)}\n"
        f"T5x b_2 <= 2                   [L >= 3, M > q]  : "
        f"{frac(lambda c: c.b(2) <= 2, lambda c: c.L >= 3 and c.M > c.q)}"
        "   <-- the doc's hypothesis; FALSE\n"
        f"T7  M(2^B - 3^L) = c_L = d_L, 2^B > 3^L         : "
        f"{frac(cycleeq.check_cycle_equation, always)}\n"
        f"T7' prod (3 + q/z) = 2^B                        : "
        f"{frac(cycleeq.product_identity, always)}\n"
        f"FP  L = 1  =>  M <= q                           : "
        f"{frac(lambda c: c.M <= c.q, lambda c: c.L == 1)}\n"
    )
    counter = [c for c in found if c.L >= 3 and c.M > c.q and c.b(2) > 2]
    if counter:
        c = counter[0]
        out.append(
            f"  T5x counterexample: q={c.q} cycle {c.elements} "
            f"L={c.L} M={c.M} > q, b_2={c.b(2)} > 2 "
            f"({len(counter)} such cycles here)\n"
            f"  The correct hypothesis is the SIZE condition M > 11q/7, not L >= 3.\n"
        )

    # ------------------------------------------------------------------- sieve
    lines = [_rule("3-ADIC SIEVE ON M (backward, uses the size bound y_k <= M)")]
    lines.append(f"{'k':>3} {'floor(k lg3)':>13} {'N(k)':>10} {'survivors':>10} "
                 f"{'mod 3^(k+1)':>14} {'density':>11}\n")
    for k in range(1, depth + 1):
        m3, s3 = sieve.surviving_residues_mod3(k)
        lines.append(
            f"{k:>3} {backtree.floor_bound(k):>13} "
            f"{backtree.count_admissible_halving_vectors(k):>10} "
            f"{len(s3):>10} {m3:>14} {len(s3) / m3:>11.9f}\n"
        )
    lines.append(f"  depth 1 survivors mod 9 : {list(sieve.surviving_residues_mod3(1)[1])}\n")
    lines.append("  with M = 1 (mod 4) that is exactly T4:  M = 17, 29 (mod 36)\n")
    k0 = min(depth, 5)
    m0, s0 = sieve.surviving_residues_mod3_no_size(k0)
    lines.append(
        f"  T0-ONLY control at depth {k0} (no size bound): {len(s0)} classes mod {m0}, "
        f"density {len(s0) / m0:.9f} = 2/9\n"
        "  -> the doc's 'T4 recurses to higher powers of 3' is WRONG: T0 alone\n"
        "     saturates at M = 2, 8 (mod 9).  All further gain comes from T6.\n"
    )
    out.append("".join(lines))

    lines = [_rule("2-ADIC SIEVE ON M (forward, x_j <= M)")]
    lines.append(f"{'a':>3} {'survivors':>10} {'of 2^(a-1)':>12} {'density':>11}  newly killed\n")
    prev = {1}  # a = 1: the odd residue class mod 2
    for a in range(2, mod2_depth + 1):
        m2, s2 = sieve.surviving_residues_mod2(a)
        cur = set(s2)
        new = sorted(
            r for r in range(1, m2, 2) if r not in cur and (r % (m2 >> 1)) in prev
        )
        lines.append(
            f"{a:>3} {len(s2):>10} {1 << (a - 1):>12} {len(s2) / (1 << (a - 1)):>11.7f}"
            f"  {new if len(new) <= 8 else str(len(new)) + ' classes'}\n"
        )
        prev = cur
    lines.append("  a=2 kills {3}: that is T1.   a=4 kills {9}: that is T8 (mod-16).\n")
    lines.append("  T8 proof (q=1, no hypothesis): M = 16s+9 => x_1 = 12s+7 => "
                 "x_2 = 18s+11 > M.\n")
    lines.append("  This sieve SATURATES: limiting density 0.2863153965 of the odds "
                 "(1.80 bits, forever).\n")
    out.append("".join(lines))

    out.append(
        _rule("COMBINED (CRT)")
        + f"depth {depth} x mod 2^{mod2_depth}: joint density among odd M = "
        f"{sieve.combined_surviving_density(depth, mod2_depth):.10f}\n"
        "  Caveat: exact as a statement about residue classes; a joint statement\n"
        "  about one cycle only when L exceeds the two depths used.\n"
    )

    # --------------------------------------------------------------- backtree
    lines = [_rule("BACKWARD PREFIX COUNTS AND THE FLOOR RULE")]
    lines.append(
        "N(k) = # halving vectors (b_1..b_k) with B_j <= floor(j*log2 3) for all j:\n  "
        + ", ".join(str(backtree.count_admissible_halving_vectors(k)) for k in range(1, 16))
        + "\n"
    )
    lines.append(
        "floor_rule_threshold(k) = largest M for which B_k > floor(k*log2 3) still\n"
        "passes the EXACT test M(2^{B_k} - 3^k) <= c_k:\n  "
        + ", ".join(f"k={k}:{backtree.floor_rule_threshold(k)}" for k in range(1, 10))
        + "\n  (k=2 gives 1, i.e. M >= 2 -- an independent cross-check of T5.)\n"
    )
    lines.append(
        "The unconditional version of the floor rule is FALSE.  Real counterexample:\n"
        "  q=5 cycle (49, 19, 31): B_3 = 5 > 4 = floor(3*log2 3).\n"
    )
    lines.append(
        "Depths where the T6 budget is tightest (record-min frac(k*log2 3)):\n  "
        + str(cycleeq.cf_record_depths(700))
        + "   -- convergent/semiconvergent denominators of log2 3.\n"
    )
    out.append("".join(lines))

    # ---------------------------------------------------------------- cycleeq
    lines = [_rule("CYCLE EQUATION AND THE 2^B/3^L DIOPHANTINE CONDITION")]
    lines.append("log2 3 = " + str(cycleeq.log2_3(30))[:32] + "\n")
    lines.append("CF terms : " + str(list(cycleeq.log2_3_cf(16))) + "\n")
    lines.append(
        "convergents: "
        + ", ".join(f"{p}/{r}" for p, r in cycleeq.log2_3_convergents(9))
        + "\n"
    )
    lines.append(
        "Crandall squeeze: 0 < B/L - log2 3 <= log2(1 + q/(3m)) for min element m.\n"
    )
    for m in (10**6, 10**12, cycleeq.BARINA_2025_LIMIT):
        L, B, margin = cycleeq.smallest_admissible_length(m)
        lines.append(f"  min element > {m:>25,}  =>  L >= {L:,}  (B = {B:,})\n")
    lines.append(
        f"  {cycleeq.BARINA_2025_LIMIT:,} = 2075 * 2^60 is Barina's 2025 verification limit\n"
        "  (J. Supercomputing 81 (2025) art. 810), so a nontrivial q=1 cycle has a\n"
        "  minimum element above it.  The published bound is STRONGER than what this\n"
        "  elementary computation gives: Hercher, JIS 26 (2023) Art. 23.3.5, gets\n"
        "  K > 1.375e11 odd elements and m >= 92 circuits using Baker's theorem.\n"
    )
    out.append("".join(lines))

    # ------------------------------------------------------- can_be_max_odd
    lines = [_rule("can_be_max_odd: exact, unconditional test on small odd M (q=1)")]
    for m in (3, 7, 9, 11, 13, 17, 21, 25, 29, 41, 53, 65, 101, 161):
        v = sieve.can_be_max_odd(m, 1, back_depth=6, forward_depth=6)
        lines.append(f"  M={m:>4}: {'survives' if v else 'excluded'}"
                     + (f" -- {v.reason}" if v.reason else "") + "\n")
    lines.append(
        "  (`survives` means only `not excluded at this depth`.  No M is ever\n"
        "   *proved* to be a cycle maximum by this package.)\n"
    )
    out.append("".join(lines))
    return "".join(out)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python -m collatz_maxodd", description=__doc__)
    ap.add_argument("--q-max", type=int, default=199, help="largest q to search (default 199)")
    ap.add_argument("--bound", type=int, default=3000, help="largest M to search (default 3000)")
    ap.add_argument("--depth", type=int, default=8, help="3-adic sieve depth (default 8)")
    ap.add_argument("--mod2-depth", type=int, default=12, help="2-adic sieve depth (default 12)")
    args = ap.parse_args(argv)
    print(report(args.q_max, args.bound, args.depth, args.mod2_depth))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
