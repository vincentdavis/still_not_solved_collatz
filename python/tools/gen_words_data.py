#!/usr/bin/env python3
"""The word -> residue classification data: lemma pack, sign law, collisions.

    uv run python python/tools/gen_words_data.py   ->  web/words.json

Everything is recomputed live from the package and asserted against the values
docs/WORDS.md records, so the page can never drift from the repo.

1. REALIZATION.  Every admissible word is live at exactly one residue; the
   survivor set is the image of Phi; chains number N_k; a_k = image size.
2. THE SIGN LAW.  sign(N_k^2 - N_{k-1}N_{k+1}) = +1 iff jump(k) = 1 --
   re-verified HERE from a fresh DP out to k = 2216 (the audit's range);
   Theorem A (jump-1 half) is proved, Conjecture B (deficit < 2) is checked
   exactly to n = 400.
3. COLLISIONS.  First collision, k=12 fiber histogram, the window-1 closed
   form, forced-doubling equality levels, phase lock, Zarubin's recursion.
"""
import json
import pathlib
import sys
from fractions import Fraction

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
from collatz_maxodd.backtree import floor_bound  # noqa: E402
from collatz_maxodd.deathdepth import surviving_residues  # noqa: E402
from collatz_maxodd.words import (  # noqa: E402
    binomial_moments,
    bump_last,
    dyadic_live_mass,
    moment_step,
    mu_c,
    fibers,
    jump,
    n_words,
    phi,
    sign_law_violations,
    window1_bound,
    word_profiles,
    words,
    zarubin_rhs,
)

OUT = pathlib.Path(__file__).resolve().parents[2] / "web" / "words.json"

N_21 = [1, 2, 3, 7, 12, 30, 85, 173, 476, 961, 2652, 8045, 17637, 51033,
        108950, 312455, 663535, 1900470, 5936673, 13472296, 39993895]
A_24 = [1, 2, 3, 6, 10, 22, 50, 104, 254, 538, 1302, 3202, 7553, 19206, 44732,
        113034, 262243, 660954, 1693714, 4204015, 10995110, 26812105,
        69626820, 182840849]

# ------------------------------------------------------------- realization
assert n_words(21) == N_21
levels = surviving_residues(10)
for k in range(1, 11):
    fib = fibers(k)
    assert sorted(fib) == levels[k - 1]
    assert sum(len(f) for f in fib.values()) == N_21[k - 1]
    assert len(fib) == A_24[k - 1]

fib4 = fibers(4)
assert {r: f for r, f in fib4.items() if len(f) > 1} == {
    80: [(1, 1, 1, 1), (1, 1, 1, 3)]
}
hist12: dict[int, int] = {}
for f in fibers(12).values():
    hist12[len(f)] = hist12.get(len(f), 0) + 1
assert hist12 == {1: 1181, 2: 864, 3: 339, 4: 408, 5: 197, 6: 86, 7: 66,
                  8: 39, 9: 8, 10: 14}

# bump law spot check (k = 6): even bumps preserve phi, odd bumps move it
for w in words(6):
    if w[-1] + 2 + sum(w[:-1]) <= floor_bound(6):
        assert phi(bump_last(w, 2)) == phi(w)
    p = phi(bump_last(w, 1))
    assert p != phi(w) and (p - phi(w)) % 3**5 == 0

# ---------------------------------------------------------------- sign law
LAW_K = 2216
assert sign_law_violations(LAW_K + 2) == []  # zero violations, zero ties

DEF_K = 400
sup_c = Fraction(0)
profiles = word_profiles(DEF_K)
for n in range(2, DEF_K + 1):
    m = floor_bound(n)
    s0 = s1 = s2 = 0
    for B, cnt in profiles[n - 1].items():
        x = m - B
        s0 += cnt
        s1 += cnt * x
        s2 += cnt * x * x
    w_int = 2 * s1 * s1 + s1 * s0 - s2 * s0
    assert 0 < w_int < 2 * s0 * s0, n  # 0 < c_n < 2
    sup_c = max(sup_c, Fraction(w_int, s0 * s0))

# ------------------------------------------------------------- collisions
collisions = [N_21[i] - A_24[i] for i in range(21)]
assert collisions[:12] == [0, 0, 0, 1, 2, 8, 35, 69, 222, 423, 1350, 4843]
assert collisions[18:] == [4242959, 9268281, 28998785]

assert window1_bound(13) == 13438
assert window1_bound(15) == 84429
assert window1_bound(16) == 217900
for k in range(2, 17):
    assert A_24[k - 1] <= window1_bound(k)

doubling_eq = [k for k in range(1, 24) if jump(k) == 2 and A_24[k] == 2 * A_24[k - 1]]
assert doubling_eq == [1, 3]
for k in range(1, 24):
    if jump(k) == 2:
        assert A_24[k] >= 2 * A_24[k - 1]

phase_hits = 0
for k in range(8, 22):
    rises = A_24[k - 1] * N_21[k - 2] < A_24[k - 2] * N_21[k - 1]
    assert rises == (jump(k - 1) == 2)
    phase_hits += 1

NZ = n_words(121)
for k in range(1, 121):
    assert zarubin_rhs(k, NZ) == NZ[k - 1]

# ------------------------------------------------- section 11: exact dynamics
N_all = [1] + n_words(61)
for n in range(1, 60):
    assert moment_step(binomial_moments(n, 6), jump(n)) == binomial_moments(n + 1, 5)
    assert dyadic_live_mass(n) + sum(Fraction(N_all[i], 2 ** floor_bound(i + 1)) for i in range(1, n)) == Fraction(1, 2)
mu22_max = Fraction(0); mu12_max = Fraction(0); kappa_u_max = Fraction(0)
for n in range(30, 601):
    mu, c = mu_c(n)
    assert c <= Fraction(2, 3) * mu * (mu + 1)          # nonincreasing-profile bound
    if jump(n) == 2 and jump(n + 1) == 2:
        mu22_max = max(mu22_max, mu)
    if jump(n) == 1 and jump(n + 1) == 2:
        mu12_max = max(mu12_max, mu)
    if jump(n - 1) == 1:
        kappa_u_max = max(kappa_u_max, c / (mu * (mu + 1)))
assert mu22_max * (mu22_max + 1) < 3                     # the V-free target, in range
assert mu12_max < 3

# --------------------------------------------------------------------- out
out = {
    "dyn": {
        "mass_checked_to": 59,
        "mu22_max_600": round(float(mu22_max), 4),
        "mu12_max_600": round(float(mu12_max), 4),
        "mu22_threshold": 1.30278,
        "kappa_u_max_600": round(float(kappa_u_max), 4),
    },
    "N": N_21,
    "a": A_24,
    "collisions": collisions,
    "sign_law_checked_to": LAW_K,
    "deficit_checked_to": DEF_K,
    "deficit_sup": round(float(sup_c), 4),
    "first_collision": {"words": [[1, 1, 1, 1], [1, 1, 1, 3]], "residue": 80,
                        "mod": 81},
    "fiber_hist_12": {str(k): v for k, v in sorted(hist12.items())},
    "doubling_equality_levels": doubling_eq,
    "window1": {"E13": 13438, "E16": 217900, "a16": A_24[15]},
    "phase_lock": {"lo": 8, "hi": 21, "hits": phase_hits},
    "zarubin_checked_to": 120,
    "neg1_chains": [1, 1, 1, 2, 2, 2, 3, 3, 4, 4, 5, 7, 8],
    "lean_decls": 22,
}
OUT.write_text(json.dumps(out, indent=1) + "\n")
print(f"wrote {OUT} (sign law to {LAW_K}, deficit sup {float(sup_c):.4f})")
