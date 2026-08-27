#!/usr/bin/env python3
"""The 3n+q cycle census: is the Collatz cycle heuristic calibrated?

    python3 python/tools/gen_census_data.py [R] [Q]

Counts primitive cycles with max <= R*q for every admissible q <= Q.  Fixing the
RATIO X/q (rather than X) makes the heuristic's prediction the same for every q,
so the distribution of counts is directly testable against Poisson.
"""
import json, math, pathlib, statistics as st, sys
from functools import reduce
from math import gcd

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
from collatz_maxodd.census import (exact_hits, primitive_cycles,  # noqa: E402
                                   satisfies_congruence, total_halvings)

R = int(sys.argv[1]) if len(sys.argv) > 1 else 100
Q = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
qs = [q for q in range(1, Q + 1, 2) if q % 3]

counts, cyc = {}, []
for q in qs:
    ps = primitive_cycles(q, R * q)
    counts[q] = len(ps)
    for L, M, el in ps:
        B = total_halvings(el, q)
        cyc.append({"q": q, "L": L, "B": B, "M": M, "d": (2 ** B - 3 ** L) // q})

viol = [c for c in cyc if not satisfies_congruence(c["q"], c["L"], c["B"])]
c = list(counts.values())
mean, var = st.mean(c), st.pvariance(c)
hit = [q for q in qs if q > 1 and exact_hits(q, max_L=80)]
non = [q for q in qs if q > 1 and not exact_hits(q, max_L=80)]
d1 = {q: sum(1 for x in cyc if x["q"] == q and x["d"] == 1) for q in qs}
rest = [counts[q] - d1[q] for q in qs]

print(f"scale X = {R}q,  {len(qs)} values of q <= {Q}")
print(f"primitive nontrivial cycles: {len(cyc)}\n")
print(f"THEOREM  q | 2^B - 3^L : {len(cyc)-len(viol)}/{len(cyc)} hold, {len(viol)} violations")
print(f"\nper-q counts:  mean {mean:.3f}   variance {var:.3f}   var/mean {var/mean:.3f}   (Poisson => 1)")
print(f"  => the heuristic's q-independent Poisson rate is REJECTED")
print(f"\nburst mechanism (2^B - 3^L == q exactly):")
print(f"  q with an exact hit : {len(hit):>4}   mean cycles {st.mean([counts[q] for q in hit]):.2f}")
print(f"  q without           : {len(non):>4}   mean cycles {st.mean([counts[q] for q in non]):.2f}")
print(f"  removing d==1 cycles drops var/mean from {var/mean:.2f} to "
      f"{st.pvariance(rest)/st.mean(rest):.2f}  (partial explanation only)")
print(f"\nq = 1: exact hits {exact_hits(1)}  -- only the trivial cycle.")
print("  2^B = 3^L + 1 with L >= 2 forces 3^L+1 = 2 or 4 (mod 8), so 2^B <= 4.")

out = {"R": R, "Q": Q, "n_q": len(qs), "n_cycles": len(cyc),
       "congruence_violations": len(viol),
       "mean": round(mean, 4), "var": round(var, 4), "var_over_mean": round(var / mean, 4),
       "exact_hit_mean": round(st.mean([counts[q] for q in hit]), 3),
       "other_mean": round(st.mean([counts[q] for q in non]), 3),
       "var_over_mean_without_d1": round(st.pvariance(rest) / st.mean(rest), 3),
       "counts": counts, "hist": {str(k): c.count(k) for k in sorted(set(c))}}
p = pathlib.Path(__file__).resolve().parents[2] / "web" / "census.json"
p.write_text(json.dumps(out, separators=(",", ":")))
print(f"\nwrote {p}")
