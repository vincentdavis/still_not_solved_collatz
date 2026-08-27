#!/usr/bin/env python3
"""Data for the closing section: why a congruence sieve can never finish.

    python3 python/tools/gen_padic_data.py   ->  web/padic.json
"""
import json, math, pathlib, sys
from fractions import Fraction

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
from collatz_maxodd.census import primitive_cycles  # noqa: E402
from collatz_maxodd.padic import (constant_pattern_point,  # noqa: E402
                                  minus_one_survives, periodic_point)

ROOT = pathlib.Path(__file__).resolve().parents[2]


def v2(n):
    b = 0
    while n % 2 == 0:
        n //= 2; b += 1
    return b


def S(n, q):
    m = 3 * n + q
    while m % 2 == 0:
        m //= 2
    return m


# --- reproduce every real cycle from its halving vector --------------------
repro, mismatch, examples = 0, 0, []
for q in [q for q in range(1, 200, 2) if q % 3]:
    for L, M, el in primitive_cycles(q, 40 * q):
        bs, y = [], M
        for _ in range(L):
            pred = next(x for x in el if S(x, q) == y)
            bs.append(v2(3 * pred + q)); y = pred
        val = periodic_point(bs, q)
        if val == M:
            repro += 1
            if q in (5, 7, 37) and len(examples) < 4:
                examples.append({"q": q, "bs": bs, "value": int(val),
                                 "elements": sorted(el)})
        else:
            mismatch += 1
assert mismatch == 0, mismatch

# --- constant patterns ------------------------------------------------------
const = []
for b in range(1, 8):
    f = constant_pattern_point(b)
    const.append({"b": b, "num": f.numerator, "den": f.denominator,
                  "pos_int": f.denominator == 1 and f > 0})
pos_only = [c["b"] for c in const if c["pos_int"]]
assert pos_only == [2], pos_only

# --- the witness ------------------------------------------------------------
witness = [{"k": k, "alive": minus_one_survives(k)} for k in range(1, 13)]
assert all(w["alive"] for w in witness)

# --- all-ones at several lengths -------------------------------------------
ones = [{"L": L, "value": int(periodic_point([1] * L))} for L in range(1, 7)]
assert all(o["value"] == -1 for o in ones)

a = math.log2(3); LAM = a ** a / (a - 1) ** (a - 1)
A_K = [1, 2, 3, 6, 10, 22, 50, 104, 254, 538, 1302, 3202, 7553, 19206, 44732,
       113034, 262243, 660954, 1693714, 4204015, 10995110, 26812105, 69626820,
       182840849]
dim_hi = math.log(LAM) / math.log(3)
dim_est = (math.log(A_K[23]) + 1.5 * math.log(24)) / (24 * math.log(3))

out = {
    "reproduced": repro, "mismatches": mismatch, "examples": examples,
    "constants": const, "only_positive_integer_b": pos_only[0],
    "witness": witness, "ones": ones,
    "dimension": {"estimate_at_k24": round(dim_est, 4),
                  "predicted": round(dim_hi, 4),
                  "lo": round(dim_est, 2), "hi": round(dim_hi, 2)},
    "a_k_head": A_K[:8],
}
(ROOT / "web" / "padic.json").write_text(json.dumps(out, separators=(",", ":")))
print(f"wrote web/padic.json  ({len(json.dumps(out))/1024:.1f} KB)")
print(f"  reproduced {repro} real cycles, {mismatch} mismatches")
print(f"  only constant pattern giving a positive integer: b = {pos_only[0]}")
print(f"  -1 alive at every depth 1..12: {all(w['alive'] for w in witness)}")
print(f"  dimension: {dim_est:.4f} (k=24 estimate) -> {dim_hi:.4f} (predicted)")
