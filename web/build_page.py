#!/usr/bin/env python3
"""Build web/index.html: inline a trimmed slice of data.json into page.template.html.

Reproducible:  python3 web/build_page.py
"""
import json, pathlib, sys

HERE = pathlib.Path(__file__).resolve().parent
data = json.loads((HERE / "data.json").read_text())
equiv = json.loads((HERE / "equiv.json").read_text())

N_STRIP = 2000          # odds 1..3999 drawn in the hero strip
w, sl, cy, di = data["wheel"], data["sieve_layers"], data["cycles"], data["diophantine"]

slim = {
    "meta": {
        "log2_3": data["meta"]["log2_3"],
        "novelty": data["meta"]["novelty_note"],
        "literature": data["meta"]["literature"],
    },
    "theorems": data["theorems"],
    "wheel": {
        "legend": w["legend"],
        "codes": w["codes"][:N_STRIP],
        "counts": w["counts"],
        "deep_level_counts": w["deep_level_counts"],
        "per_mod12": w["per_mod12"],
        "caveat": w["caveat"],
    },
    "mod3": sl["mod3"]["layers"],
    "mod2": {
        "layers": sl["mod2"]["layers"],
        "limit": sl["mod2"]["limiting_density_among_odds"],
        "note": sl["mod2"]["limit_note"],
    },
    "crt": {"rows": sl["combined_crt"]["rows"], "verdict": sl["combined_crt"]["verdict"]},
    "tree": {
        "depth_stats": data["backward_tree"]["depth_stats"],
        "growth": data["backward_tree"]["growth"],
        "sturmian": data["backward_tree"]["sturmian"],
    },
    "cycles": {
        "list": [
            {k: c[k] for k in ("q", "L", "M", "min", "B", "odds", "a", "chk")}
            for c in cy["list"]
        ],
        "summary": cy["summary"],
        "highlights": cy["highlights"],
        "t5_counter": cy["T5_L_ge_3_counterexamples"],
    },
    "dio": {
        "rows": di["rows"],
        "records": di["records"],
        "records_max": di["records_max"],
        "best": di["best_in_table"],
        "verification_limit": di["verification_limit"],
        "cf": di["cf_log2_3"],
        "verdict": di["verdict"],
    },
    "traj": data["trajectories"]["list"],
    "equiv": equiv,
    "verification": {
        "fwd": {k: data["verification"]["forward_2adic"][k]
                for k in ("M_checked", "M_kept", "observed_density", "predicted_limit")},
        "bwd": {k: data["verification"]["backward_3adic"][k] for k in ("M_checked", "all_match")},
    },
}

blob = json.dumps(slim, separators=(",", ":"))
assert "</script" not in blob, "JSON would terminate the script tag"

html = (HERE / "page.template.html").read_text().replace("__COLLATZ_DATA__", blob)
out = HERE / "index.html"
out.write_text(html)
print(f"wrote {out}  ({len(html)/1024:.0f} KB, data {len(blob)/1024:.0f} KB)")
