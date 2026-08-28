#!/usr/bin/env python3
"""Data for the 'what the maximum tells you' section.

    python3 python/tools/gen_structure_data.py  ->  web/structure.json
"""
import json, math, pathlib, statistics as st, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
from collatz_maxodd.census import primitive_cycles, total_halvings  # noqa: E402
from collatz_maxodd.structure import (ascent_bound, max_cycle_length,  # noqa: E402
                                      min_single_halving_fraction, reachable_set,
                                      single_halving_bound)

ROOT = pathlib.Path(__file__).resolve().parents[2]
VERIFIED = 2392312122059207475200


def S(n, q):
    m = 3 * n + q
    while m % 2 == 0:
        m //= 2
    return m


def v2(n):
    b = 0
    while n % 2 == 0:
        n //= 2; b += 1
    return b


rows, viol = [], {"reach": 0, "ascent": 0, "halving": 0}
for q in [q for q in range(1, 600, 2) if q % 3]:
    for L, M, el in primitive_cycles(q, 40 * q):
        m = min(el)
        if m <= q:
            continue
        R = reachable_set(M, q)
        if not set(el) <= R or L > len(R):
            viol["reach"] += 1
        up, x = 0, m
        while x != M:
            x = S(x, q); up += 1
        down, x = 0, M
        while x != m:
            x = S(x, q); down += 1
        if up < ascent_bound(m, M, q) - 1e-9:
            viol["ascent"] += 1
        B = total_halvings(el, q)
        u = sum(1 for y in el if v2(3 * y + q) == 1)
        if u < single_halving_bound(L, B):
            viol["halving"] += 1
        rows.append({"q": q, "L": L, "m": m, "M": M, "R": len(R), "up": up,
                     "down": down, "bound": round(ascent_bound(m, M, q), 2),
                     "B": B, "u": u})
assert sum(viol.values()) == 0, viol

# R(O) for ordinary q = 1 numbers
sizes = [max_cycle_length(O) for O in range(10 ** 6 + 1, 10 ** 6 + 4001, 2)]

out = {
    "cycles": len(rows), "violations": viol,
    "examples": [r for r in rows if r["q"] in (5, 11, 47)][:6],
    "reach_stats": {"n": len(sizes), "mean": round(st.mean(sizes), 2),
                    "median": st.median(sizes), "max": max(sizes),
                    "hist": {str(k): sizes.count(k) for k in range(1, 7)}},
    "ascent": {"share_mean": round(st.mean([r["up"] / r["L"] for r in rows]), 3),
               "share_min": round(min(r["up"] / r["L"] for r in rows), 3),
               "share_max": round(max(r["up"] / r["L"] for r in rows), 3),
               "single_step_descents": sum(1 for r in rows if r["down"] == 1)},
    "halving": {
        "q1_fraction": round(min_single_halving_fraction(VERIFIED), 5),
        "limit": round(2 - math.log2(3), 5),
        "census_min_share": round(min(r["u"] / r["L"] for r in rows), 3),
    },
    "verified": VERIFIED,
}
(ROOT / "web" / "structure.json").write_text(json.dumps(out, separators=(",", ":")))
print(f"wrote web/structure.json  ({len(json.dumps(out))/1024:.1f} KB)")
print(f"  {len(rows)} cycles, violations {viol}")
print(f"  R(O) for q=1: mean {out['reach_stats']['mean']}, median {out['reach_stats']['median']}")
print(f"  ascent share mean {out['ascent']['share_mean']}, "
      f"{out['ascent']['single_step_descents']} single-step descents")
print(f"  q=1 single-halving floor: {out['halving']['q1_fraction']}")
