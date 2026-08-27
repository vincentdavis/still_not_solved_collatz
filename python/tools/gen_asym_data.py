#!/usr/bin/env python3
"""Data for the 'pinning down the constant' section of web/index.html.

Writes web/asym.json.   python3 python/tools/gen_asym_data.py

Two counts:
  N_k  admissible halving vectors -- scalar state B_j, so an O(k^2) DP exists
  a_k  surviving residues mod 3^k -- no finite transfer matrix (see deathdepth)

a_1..a_18 are recomputed live and checked against the stored list; a_19..a_24
are stored because the DFS costs minutes at that depth (a_24 took ~6 min).
"""
import json, math, pathlib, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
from collatz_maxodd.backtree import count_admissible_halving_vectors as Nk  # noqa: E402
from collatz_maxodd.deathdepth import surviving_residue_count  # noqa: E402

WEB = pathlib.Path(__file__).resolve().parents[2] / "web"
KMAX_DATA, KMAX_MODEL = 24, 40

A = [1, 2, 3, 6, 10, 22, 50, 104, 254, 538, 1302, 3202, 7553, 19206, 44732,
     113034, 262243, 660954, 1693714, 4204015, 10995110, 26812105, 69626820,
     182840849]
assert surviving_residue_count(18) == A[:18], "stored a_k disagrees with the DFS"

N = [Nk(k) for k in range(1, KMAX_MODEL + 1)]
R = [A[i] / N[i] for i in range(len(A))]

a = math.log2(3)
LAM = a ** a / (a - 1) ** (a - 1)


def lsq(xs, ys):
    n = len(xs); sx = sum(xs); sy = sum(ys)
    sxx = sum(x * x for x in xs); sxy = sum(x * y for x, y in zip(xs, ys))
    m = (n * sxy - sx * sy) / (n * sxx - sx * sx); b = (sy - m * sx) / n
    ss = sum((y - (m * x + b)) ** 2 for x, y in zip(xs, ys))
    tot = sum((y - sy / n) ** 2 for y in ys)
    return m, b, 1 - ss / tot


def fits(hi):
    ks = list(range(6, hi + 1)); Y = [math.log(R[k - 1]) for k in ks]
    mg, bg, r2g = lsq([float(k) for k in ks], Y)
    mp, bp, r2p = lsq([math.log(k) for k in ks], Y)
    return (mg, bg, r2g), (mp, bp, r2p)


(mg, bg, r2g), (mp, bp, r2p) = fits(KMAX_DATA)
(_, _, r2g23), (_, _, r2p23) = fits(23)

# out-of-sample: fit on k<=20, score 21..24
(g20, gb20, _), (p20, pb20, _) = fits(20)
oos = []
for k in range(21, KMAX_DATA + 1):
    act = A[k - 1]
    pg = N[k - 1] * math.exp(g20 * k + gb20)
    pp = N[k - 1] * math.exp(p20 * math.log(k) + pb20)
    oos.append({"k": k, "actual": act,
                "geo_err": round(100 * (pg - act) / act, 2),
                "poly_err": round(100 * (pp - act) / act, 2)})

curves = [{"k": k,
           "geo": N[k - 1] * math.exp(mg * k + bg),
           "poly": N[k - 1] * math.exp(mp * math.log(k) + bp)}
          for k in range(6, KMAX_MODEL + 1)]
osc = max(abs(math.log(R[k - 1]) - (mp * math.log(k) + bp)) for k in range(15, KMAX_DATA + 1))

out = {
    "lambda": round(LAM, 10),
    "lambda_confirmed": {"digits": 6, "k_max": 8000, "rel_err_joint_fit": 8.4e-6,
                         "power_recovered": -1.46, "power_expected": -1.5,
                         "note": "N_k has a scalar state B_j, so an O(k^2) DP settles it"},
    "a_k": A, "N_k": N, "ratio": [round(x, 6) for x in R],
    "k_data": KMAX_DATA, "k_model": KMAX_MODEL,
    "models": {
        "geometric":  {"rho": round(math.exp(mg), 5), "lambda_a": round(LAM * math.exp(mg), 5),
                       "rate": round(LAM * math.exp(mg) / 3, 5), "r2": round(r2g, 5),
                       "r2_at23": round(r2g23, 5)},
        "polynomial": {"q": round(-mp, 5), "lambda_a": round(LAM, 5),
                       "rate": round(LAM / 3, 5), "r2": round(r2p, 5),
                       "r2_at23": round(r2p23, 5)},
    },
    "curves": [{"k": c["k"], "geo": round(c["geo"]), "poly": round(c["poly"])} for c in curves],
    "oos": oos,
    "oos_mean": {"geo": round(sum(abs(o["geo_err"]) for o in oos) / len(oos), 2),
                 "poly": round(sum(abs(o["poly_err"]) for o in oos) / len(oos), 2)},
    "bracket": [round(LAM * math.exp(mg) / 3, 4), round(LAM / 3, 4)],
    "oscillation_pct": round(100 * (math.exp(osc) - 1), 1),
    "k_decide": None,          # filled in below
    "nodes_at_k_decide": None,
    "compute_at_k_decide": None,
    "no_transfer_matrix": ("the state governing a node is the SET of (B_j, y_j mod 3) over its "
                           "live chains; B_j ranges over ~0.585k values, so the state space grows "
                           "like 2^(1.76k)"),
}
# k at which the model separation clears 3x the residual oscillation
need = 3 * (math.exp(osc) - 1)
kd = next((c["k"] for c in curves if c["poly"] / c["geo"] - 1 >= need), None)
out["k_decide"] = kd
if kd:
    growth = A[-1] / A[-2]
    nodes = A[-1] * growth ** (kd - KMAX_DATA)
    out["nodes_at_k_decide"] = f"{nodes:.0e}"
    days = nodes * 1.8e-6 / 86400
    out["compute_at_k_decide"] = (f"about {days/365:.0f} year" + ("s" if days/365 >= 1.5 else "") if days > 400 else
                                  f"about {days:.0f} days" if days > 1.5 else "hours")
    out["separation_now_pct"] = round(100 * (curves[KMAX_DATA - 6]["poly"] / curves[KMAX_DATA - 6]["geo"] - 1), 1)

(WEB / "asym.json").write_text(json.dumps(out, separators=(",", ":")))
print(f"wrote {WEB/'asym.json'}  ({len(json.dumps(out))/1024:.1f} KB)")
print(f"  lambda={LAM:.10f}  bracket={out['bracket']}  oscillation=+/-{out['oscillation_pct']}%")
print(f"  R^2 through k=23: poly {r2p23:.4f} vs geo {r2g23:.4f}  -> polynomial")
print(f"  R^2 through k=24: poly {r2p:.4f} vs geo {r2g:.4f}  -> geometric  (the flip)")
