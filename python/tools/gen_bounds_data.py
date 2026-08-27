#!/usr/bin/env python3
"""Data for the 'both ends' and 'residue-class certificate' sections.

    python3 python/tools/gen_bounds_data.py    ->  web/bounds.json

Everything is recomputed and asserted against the values recorded elsewhere in
the project, so the page cannot drift from the repo.
"""
import json, math, pathlib, sys, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
from collatz_maxodd.bounds import (can_be_min_odd, drops_below,  # noqa: E402
                                   min_residues_mod12, sandwich_holds, scale)
from collatz_maxodd.census import primitive_cycles, total_halvings  # noqa: E402
from collatz_maxodd.certify import (backward_depth, class_coverage,  # noqa: E402
                                    class_threshold)

ROOT = pathlib.Path(__file__).resolve().parents[2]
A_K = [1, 2, 3, 6, 10, 22, 50, 104, 254, 538, 1302, 3202, 7553, 19206]
VERIFIED = 2392312122059207475200

# --- the mirror, checked over the census -----------------------------------
rows, viol = [], 0
for q in [q for q in range(1, 600, 2) if q % 3]:
    for L, M, el in primitive_cycles(q, 40 * q):
        m = min(el)
        if m <= q or M <= q:
            continue
        B = total_halvings(el, q)
        if not can_be_min_odd(m, q):
            viol += 1
        if not sandwich_holds(q, L, B, m, M):
            viol += 1
        rows.append({"q": q, "L": L, "B": B, "m": m, "M": M,
                     "S": round(scale(q, L, B), 2)})
assert viol == 0, f"{viol} mirror/sandwich violations"

# the q=47 family: several cycles, one shared scale
fam = [r for r in rows if r["q"] == 47 and r["L"] == 4 and r["B"] == 7]
assert len(fam) >= 4 and len({r["S"] for r in fam}) == 1

# --- certifying from either end --------------------------------------------
LO, N = 10 ** 7 + 1, 100_000
odds = range(LO, LO + 2 * N, 2)
t0 = time.time(); w_min = sum(drops_below(m) for m in odds); t_min = time.time() - t0
t0 = time.time(); w_max = sum(backward_depth(M)[1] for M in odds); t_max = time.time() - t0
one_step = sum(1 for m in range(3, 40001, 2) if drops_below(m) == 1)
assert all(m % 4 == 1 for m in range(3, 40001, 2) if drops_below(m) == 1)

# --- residue-class certificate ---------------------------------------------
cov = []
for k in range(1, 9):
    c = class_coverage(k)
    assert c["alive"] == A_K[k - 1], (k, c["alive"], A_K[k - 1])
    cov.append({"k": k, "modulus": c["modulus"], "alive": c["alive"],
                "certified": round(100 * c["certified_fraction"], 3),
                "threshold": c["threshold"]})
cov.append({"k": 24, "modulus": 3 ** 24, "alive": 182840849,
            "certified": round(100 * (1 - 182840849 / 3 ** 24), 3),
            "threshold": class_threshold(24), "stored": True})

k_max = max(k for k in range(1, 200) if class_threshold(k) <= VERIFIED)

out = {
    "mirror": [
        {"end": "maximum", "hop_in": "1 halving", "hop_out": "≥ 2",
         "residue": "M ≡ 1 (mod 4), ≡ 5 (mod 12)"},
        {"end": "minimum", "hop_in": "≥ 2", "hop_out": "1 halving",
         "residue": "m ≡ 3 (mod 4), ≡ 7 or 11 (mod 12)"},
    ],
    "min_residues_q1": list(min_residues_mod12(1)),
    "cycles_checked": len(rows), "violations": viol,
    "sandwich_examples": sorted(rows, key=lambda r: (r["q"], r["m"]))[:4] + fam[:4],
    "family_q47": {"n": len(fam), "L": 4, "B": 7, "scale": fam[0]["S"],
                   "ranges": [[r["m"], r["M"]] for r in fam]},
    "ends": {"window": N, "from": LO,
             "min_work": w_min, "max_work": w_max,
             "min_seconds": round(t_min, 3), "max_seconds": round(t_max, 3),
             "max_cheaper_by": round(w_min / w_max, 2),
             "one_step_fraction": round(one_step / len(range(3, 40001, 2)), 4)},
    "classes": cov,
    "threshold_growth": [{"k": k, "T": class_threshold(k)}
                         for k in (5, 10, 20, 40, 60, 80, 100, 118, 119)],
    "k_max_under_verified": k_max,
    "verified": VERIFIED,
    "a_k": A_K,
    "diophantine_wall": round(1 / (3 * math.log(2)) / VERIFIED, 24),
}
(ROOT / "web" / "bounds.json").write_text(json.dumps(out, separators=(",", ":")))
print(f"wrote web/bounds.json  ({len(json.dumps(out))/1024:.1f} KB)")
print(f"  mirror + sandwich: {len(rows)} cycles, {viol} violations")
print(f"  ends: min {w_min:,} vs max {w_max:,} units -> max {out['ends']['max_cheaper_by']}x cheaper")
print(f"  classes: k=8 certifies {cov[7]['certified']}%, k=24 certifies {cov[8]['certified']}%")
print(f"  threshold allows depth up to k = {k_max} (T={class_threshold(k_max):.3e} <= {VERIFIED:.3e})")
