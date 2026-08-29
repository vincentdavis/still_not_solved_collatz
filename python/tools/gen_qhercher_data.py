#!/usr/bin/env python3
"""The two direction-survey results: q-transfer and the Hercher ladder re-run.

    uv run python python/tools/gen_qhercher_data.py   ->  web/qhercher.json

Everything is recomputed live from the package and asserted against the values
docs/GROUND_TRUTH.md records, so the page can never drift from the repo.

1. Q-TRANSFER.  The magnitude-free sieve cannot see `q`: S_k(q) = q*S_k(1)
   mod 3^k, so every sieve statistic is identical between q = 1 and q = 5 —
   and q = 5 has a real cycle.  Verified here for k <= 10, six q either sign,
   plus the forward 2-adic mirror and the corollary's careful phrasing (49
   dies at depth 8).

2. THE HERCHER LADDER AT BARINA 2025.  Regression against the paper's printed
   iterates, then the new-X0 verdict: m = 92 still stands, its exact
   verification cost, the four improved Table-1 rows, and the all-m rung
   economics (Remark 28 reproduced).
"""
import json
import pathlib
import sys
from fractions import Fraction

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
from collatz_maxodd.deathdepth import surviving_residues, survives  # noqa: E402
from collatz_maxodd.hercher import (  # noqa: E402
    BARINA_PAGE_X0,
    BARINA_PAPER_X0,
    HERCHER_PUBLICATION_X0,
    allm_bound,
    eliminate,
    ladder,
    required_x0_for_next_m,
    rung_table,
    sdw_ceiling,
)
from collatz_maxodd.sieve import surviving_residues_mod2  # noqa: E402

OUT = pathlib.Path(__file__).resolve().parents[2] / "web" / "qhercher.json"

# ---------------------------------------------------------------- q-transfer
K_MAX = 10
QS = [5, 7, 11, 25, -1, -5]
s1 = surviving_residues(K_MAX, 1)
a_k = [len(level) for level in s1]
assert a_k == [1, 2, 3, 6, 10, 22, 50, 104, 254, 538]
for q in QS:
    sq = surviving_residues(K_MAX, q)
    for k in range(1, K_MAX + 1):
        assert sq[k - 1] == sorted((q * r) % 3**k for r in s1[k - 1]), (q, k)

# forward 2-adic mirror
A_MAX = 12
for q in (5, 7, 11, 25):
    for a in range(1, A_MAX + 1):
        base = surviving_residues_mod2(a, 1)[1]
        assert surviving_residues_mod2(a, q)[1] == tuple(
            sorted((q * r) % 2**a for r in base)
        )

# the corollary, phrased correctly: 49 (q=5 cycle max) dies at depth 8
assert survives(49 % 3**7, 7, 5) and not survives(49 % 3**8, 8, 5)

qtransfer = {
    "k_max": K_MAX,
    "qs": QS,
    "a_k": a_k,
    "forward_a_max": A_MAX,
    "q5_cycle": [19, 31, 49],
    "q5_max_death_depth": 8,
    "lean_depth": 4,
    "lean_offsets": ["5", "7", "25", "−1 (encoded 80 mod 3⁴)"],
    "sign_cycles": [[1], [5, 7], [17, 25, 37, 55, 41, 61, 91]],
}

# ---------------------------------------------------------------- the ladder
lad = ladder(91, HERCHER_PUBLICATION_X0, 700_000_000_000, stop_at=sdw_ceiling(91))
m2_seq = [r.m2 for r in lad]
rungs = [r.K for r in lad]
assert m2_seq == [47, 67, 77, 82, 86, 88, 91]
assert rungs[0] == 5_267_319_278_509_397
assert rungs[-1] == 7_941_964_418_702_608_664_581
assert rungs[-1] > sdw_ceiling(91)

v92 = eliminate(92, BARINA_PAPER_X0)
assert not v92.dead and v92.K_final == 205_632_218_873_398_596_256
assert not eliminate(92, BARINA_PAGE_X0).dead
assert eliminate(92, HERCHER_PUBLICATION_X0).K_final == 77_692_117_359_936_589_403
cost92 = required_x0_for_next_m(92)
assert cost92 == 15905

rows = []
for m_hi, expect in ((100, 205_632_218_873_398_596_256),
                     (124, 77_692_117_359_936_589_403),
                     (187, 27_444_133_206_411_171_953)):
    assert eliminate(m_hi, BARINA_PAPER_X0).K_final == expect
    assert eliminate(m_hi + 1, BARINA_PAPER_X0).K_final != expect
    rows.append({"m_le": m_hi, "K": str(expect), "K_float": float(expect)})

for x0 in (HERCHER_PUBLICATION_X0, BARINA_PAPER_X0, BARINA_PAGE_X0):
    assert allm_bound(x0)[0] == 72_057_431_991

next_rung = next(r for r in rung_table(10**12) if r["K"] > 137_400_000_000)
assert next_rung["K"] == 137_528_045_312
units = next_rung["x0_needed_2p60"]
assert 2835 < units < 2836  # Hercher Remark 28: he prints the round-up 2836

hercher = {
    "x0": {
        "hercher": "695·2⁶⁰",
        "paper": "2⁷¹ = 2048·2⁶⁰",
        "page": "2075·2⁶⁰",
    },
    "regression": {
        "m2": m2_seq,
        "rungs": [str(k) for k in rungs],
        "rungs_float": [float(k) for k in rungs],
        "ceiling_91": float(sdw_ceiling(91)),
    },
    "m92": {
        "stall": str(v92.K_final),
        "stall_float": float(v92.K_final),
        "ceiling": float(v92.ceiling),
        "cost_units_2p60": cost92,
        "cost_float": float(cost92 * 2**60),
    },
    "new_rows": rows,
    "published_rows": [
        {"m_le": 98, "K_float": 7.76e19},
        {"m_le": 117, "K_float": 2.74e19},
        {"m_le": 276, "K_float": 4.68e18},
    ],
    "allm": 72_057_431_991,
    "next_rung": {"K": 137_528_045_312, "x0_units": float(units), "x0_printed": 2836},
    "cor29_condition_units": 1536,
}

OUT.write_text(json.dumps({"qtransfer": qtransfer, "hercher": hercher}, indent=1))
print(f"wrote {OUT}")
