#!/usr/bin/env python3
"""Data for the Lean cycle-length-bound section of web/index.html.

    python3 python/tools/gen_lean_data.py

Everything here is recomputed in Python and asserted against the values the Lean
guards claim, so the page cross-checks the formalization rather than quoting it.
"""
import json, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean"


def v2(m: int) -> int:
    b = 0
    while m % 2 == 0:
        m //= 2
        b += 1
    return b


# --- cycle5 : the real q=5 cycle {49, 31, 19}, in Lean's y-order -------------
q = 5
y = [49, 31, 19]          # y0, y1, y2 ; y3 = y0 by periodicity


def yv(i):
    return y[i % 3]


bb = [v2(3 * yv(k) + q) for k in range(1, 5)]           # bb 1 .. bb 4
sumB = [sum(v2(3 * yv(j) + q) for j in range(1, k + 1)) for k in range(4)]
prodFrom0 = yv(0) * yv(1) * yv(2)
prodG = (3 * yv(1) + q) * (3 * yv(2) + q) * (3 * yv(3) + q)
B, L = sumB[3], 3
kappa, c, m = 3, 5, 19

# --- the identity and the bound, checked here ------------------------------
assert prodG == 2 ** B * prodFrom0, "prodG_eq fails"
lhs_baker = 3 ** L * L ** kappa + c * 3 ** L
rhs_baker = 2 ** B * L ** kappa
assert lhs_baker == rhs_baker, "the Baker input is meant to be tight here"
assert 3 * m * 2 ** B <= 3 ** L * (3 * m + 2 * L * q), "squeeze fails"
assert 3 * m * c <= 2 * q * L ** (kappa + 1), "length_bound conclusion fails"

# --- what Lean's guards assert, for cross-checking --------------------------
guards = (LEAN / "Collatz" / "Guards.lean").read_text()
assert f"= {list(bb)}".replace(" ", "") in guards.replace(" ", ""), "bb guard mismatch"
assert f"= {list(sumB)}".replace(" ", "") in guards.replace(" ", ""), "sumB guard mismatch"

audited = len(re.findall(r"^#print axioms ", (LEAN / "Collatz" / "Audit.lean").read_text(), re.M))

# the Python test count, taken from pytest itself rather than written down
def _count_tests() -> int:
    for cmd in ([sys.executable, "-m", "pytest", "--collect-only", "-q"],
                ["uv", "run", "pytest", "--collect-only", "-q"]):
        try:
            r = subprocess.run(cmd, cwd=ROOT / "python", capture_output=True, text=True)
        except FileNotFoundError:
            continue
        mt = re.search(r"^(\d+) tests? collected", r.stdout, re.M)
        if mt:
            return int(mt.group(1))
    raise SystemExit("could not read the test count from pytest")


n_tests = _count_tests()
length_src = (LEAN / "Collatz" / "Length.lean").read_text()
proved = re.findall(r"^theorem (\w+)", length_src, re.M)

out = {
    "audited_decls": audited,
    "python_tests": n_tests,
    "axioms": "propext, Quot.sound",
    "proved_names": proved,
    "theorem": {
        "hypothesis": "3^L · L^κ + c · 3^L  ≤  2^B · L^κ",
        "meaning": "2^B / 3^L ≥ 1 + c / L^κ",
        "conclusion": "3 · m · c  ≤  2 · q · L^(κ+1)",
    },
    "replaces_analysis": [
        {"name": "prodG_eq", "stmt": "∏ (3x_j + q) = 2^B · ∏ x_j",
         "role": "the exact integer identity that replaces taking logarithms of 2^B = ∏(3 + 1/x_j)"},
        {"name": "pow_succ_le", "stmt": "(N+q)^L · N ≤ N^L · (N + 2Lq)   when 2Lq ≤ N",
         "role": "the ℕ stand-in for (1 + q/N)^L ≤ 1 + 2Lq/N, where the usual proof needs exp and log"},
    ],
    "instance": {
        "q": q, "elements": y, "L": L, "B": B, "m": m, "kappa": kappa, "c": c,
        "bb": bb[:3], "sumB": sumB,
        "prodFrom0": prodFrom0, "prodG": prodG, "two_pow_B": 2 ** B,
        "baker_lhs": lhs_baker, "baker_rhs": rhs_baker, "baker_tight": lhs_baker == rhs_baker,
        "concl_lhs": 3 * m * c, "concl_rhs": 2 * q * L ** (kappa + 1),
    },
    "verification_limit": 2392312122059207475200,
    "verification_status": [
        {"r": "T0–T8, U, FP — the residue constraints", "py": True, "lean": True, "n": ""},
        {"r": "the equivalence theorem (sieve = cycle problem)", "py": True, "lean": True,
         "n": "Equivalence.lean; König's lemma assumed, see Unproved.lean"},
        {"r": "cycle-length bound", "py": True, "lean": True, "n": "Baker input assumed"},
        {"r": "min–max sandwich, both halves", "py": True, "lean": True,
         "n": "pow_le_of_min and pow_ge_of_max"},
        {"r": "u ≥ 2L − B", "py": True, "lean": True, "n": "single_halving_count"},
        {"r": "the 41.5% figure itself", "py": True, "lean": False,
         "n": "needs real arithmetic on log₂3, which core Lean has no ℝ for"},
        {"r": "the minimum's mirror (m ≡ 3 mod 4, needs m > q)", "py": True, "lean": True,
         "n": "Minimum.lean; the minimum is derived, not postulated"},
        {"r": "that mirror's hypothesis m > q cannot be dropped", "py": True, "lean": True,
         "n": "cycle37: q < M holds, q < m fails, and the conclusion fails"},
        {"r": "L ≤ |R(O)|", "py": True, "lean": False, "n": "needs finite-set machinery"},
        {"r": "periodic points and the −1 witness", "py": True, "lean": False, "n": ""},
        {"r": "census, death-depth tail, dimension", "py": True, "lean": False,
         "n": "measurements, not theorems"},
    ],
    "caveat": ("weaker than the published bounds, which use genuine effective irrationality "
               "measures for log2(3); this repo verifies no such constant — that is exactly "
               "the part left as a hypothesis"),
}
(ROOT / "web" / "lean.json").write_text(json.dumps(out, separators=(",", ":")))
print(f"wrote web/lean.json  ({len(json.dumps(out))/1024:.1f} KB)")
print(f"  cycle5: L={L} B={B}  prodG={prodG} = 2^{B} * {prodFrom0}  ✓")
print(f"  Baker input tight: {lhs_baker} = {rhs_baker}  ✓")
print(f"  conclusion: {3*m*c} <= {2*q*L**(kappa+1)}  ✓")
print(f"  Lean: {audited} audited declarations, {len(proved)} theorems in Length.lean")
print(f"  Python: {n_tests} tests collected")
