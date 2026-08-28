#!/usr/bin/env python3
"""Three explorations proposed in the code review, and what they returned.

    uv run python python/tools/gen_explore_data.py   ->  web/explore.json

Two of the three refute the guess that motivated them.  That is recorded rather
than smoothed over, because the guesses were mine and they were wrong in
informative ways.

1. WHERE THE OVER-DISPERSION LIVES.  Guess: the unexplained excess sits in the
   `m <= q` cycles, the least Collatz-like regime.  It does not -- it is
   CONCENTRATED in `m > q`, the regime that most resembles `q = 1`.

2. A CERTIFIED BOUND ON THE TAIL RATE.  Guess: finite-memory relaxations would
   give rigorous UPPER bounds.  `a_k` turns out to be supermultiplicative and
   not submultiplicative, so Fekete runs the other way: a rigorous LOWER bound,
   and no upper bound at all.  Supermultiplicativity is now PROVED (see
   docs/EXPLORE.md), so lim a_k^(1/k) exists and the lower bound 0.7364 is
   rigorous.  The published bracket's lower end is a model fit; the rigorous
   bracket [0.736, 0.947] is wider and both ends are theorems.

3. THE HERCHER PINCER.  Guess: `L <= |R(O)|` plus a published lower bound on `L`
   is a cheap size-based certificate.  This one holds up.
"""
import json, pathlib, statistics, sys, time
from collections import defaultdict

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
from collatz_maxodd.census import primitive_cycles, total_halvings  # noqa: E402
from collatz_maxodd.deathdepth import splice, survives  # noqa: E402
from collatz_maxodd.structure import reachable_set  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[2]
HERCHER_L = 137_500_000_000          # Hercher 2023, odd elements of a cycle

# --- 1. where the over-dispersion lives -------------------------------------
ADM = [q for q in range(1, 1001, 2) if q % 3]
big, small = defaultdict(int), defaultdict(int)
k_of_cycle = defaultdict(int)
for q in ADM:
    for L, M, el in primitive_cycles(q, 100 * q):
        (big if min(el) > q else small)[q] += 1
        B = total_halvings(el, q)
        k_of_cycle[(2 ** B - 3 ** L) // q] += 1


def disp(d):
    c = [d[q] for q in ADM]
    mean = sum(c) / len(c)
    var = sum((x - mean) ** 2 for x in c) / len(c)
    return {"mean": round(mean, 3), "var": round(var, 3),
            "var_over_mean": round(var / mean, 3), "max": max(c),
            "nonzero_q": sum(1 for x in c if x)}


allq = {q: big[q] + small[q] for q in ADM}
d_all, d_big, d_small = disp(allq), disp(big), disp(small)
assert d_big["var_over_mean"] > d_all["var_over_mean"] > d_small["var_over_mean"], \
    "the m>q regime is supposed to be the MORE dispersed one"

# the quotient k = (2^B - 3^L)/q is always odd and prime to 3 -- same
# admissibility as q itself, since 2^B - 3^L is odd and never 0 mod 3
assert all(k % 2 == 1 and k % 3 for k in k_of_cycle), "k must be odd and prime to 3"
n_cycles = sum(k_of_cycle.values())

# --- 2. the tail rate: which way does Fekete run? ---------------------------
a = json.loads((ROOT / "web" / "asym.json").read_text())["a_k"]
n = len(a)
ratios = [a[j + k - 1] / (a[j - 1] * a[k - 1])
          for j in range(1, n) for k in range(1, n - j + 1)]
super_mult = min(ratios) >= 1.0
sub_mult = max(ratios) <= 1.0
assert super_mult and not sub_mult, "expected supermultiplicative, not sub"
# supermultiplicativity is now PROVED (docs/EXPLORE.md); check the construction
# the proof is built on, so a mistake in it fails here rather than in the prose
spliced = 0
for j in range(1, 4):
    for k in range(1, 4):
        for r in (x for x in range(3 ** j) if survives(x, j)):
            for s_ in (x for x in range(3 ** k) if survives(x, k)):
                assert survives(splice(r, j, s_, k), j + k), (r, j, s_, k)
                spliced += 1
assert spliced == 36
# Fekete on a supermultiplicative sequence: lim a_k^(1/k) = sup_k a_k^(1/k),
# so EVERY term is a rigorous lower bound and the last is the best.
best_lower = max(a[k - 1] ** (1 / k) for k in range(1, n + 1))
bracket = json.loads((ROOT / "web" / "asym.json").read_text())["bracket"]

# --- 3. the Hercher pincer ---------------------------------------------------
pincer = []
for e in (5, 6, 7, 8, 9, 10):
    lo, N, sizes = 10 ** e + 1, 6000, []
    t0 = time.time()
    for M in range(lo, lo + 2 * N, 2):
        if M % 36 in (17, 29):
            sizes.append(len(reachable_set(M, 1)))
    sizes.sort()
    pincer.append({"e": e, "n": len(sizes),
                   "median": sizes[len(sizes) // 2],
                   "mean": round(sum(sizes) / len(sizes), 2),
                   "p99": sizes[int(0.99 * len(sizes))],
                   "max": sizes[-1], "sec": round(time.time() - t0, 3)})
worst = max(p["max"] for p in pincer)
assert worst < HERCHER_L, "an R(O) that large would be a cycle candidate"
# no growth trend across five orders of magnitude
meds = [p["median"] for p in pincer]
assert max(meds) - min(meds) <= 2, "median |R(M)| is supposed to be flat"

out = {
    "dispersion": {"all": d_all, "m_gt_q": d_big, "m_le_q": d_small,
                   "n_q": len(ADM), "n_cycles": n_cycles,
                   "guess": "the excess sits in m <= q",
                   "result": "it is concentrated in m > q -- the opposite"},
    "quotients": {"k_counts": dict(sorted(k_of_cycle.items())[:8]),
                  "exact_hit_share": round(100 * k_of_cycle[1] / n_cycles, 1),
                  "all_odd_prime_to_3": True},
    "fekete": {"supermultiplicative": super_mult, "submultiplicative": sub_mult,
               "min_ratio": round(min(ratios), 4), "max_ratio": round(max(ratios), 4),
               "k_max": n, "best_rigorous_lower_rate": round(best_lower / 3, 4),
               "published_bracket": bracket,
               "proved": True, "splice_checked": spliced,
               "guess": "finite-memory relaxations give rigorous UPPER bounds",
               "result": "Fekete runs the other way -- and supermultiplicativity "
                         "is now PROVED, so the lower bound is rigorous"},
    "pincer": {"rows": pincer, "hercher_L": HERCHER_L, "worst_seen": worst,
               "headroom": round(HERCHER_L / worst),
               "result": "|R(M)| is flat in M and ~9 orders below what a cycle needs"},
}
(ROOT / "web" / "explore.json").write_text(json.dumps(out, separators=(",", ":")))
print(f"wrote web/explore.json  ({len(json.dumps(out))/1024:.1f} KB)")
print(f"  dispersion: all {d_all['var_over_mean']}, m>q {d_big['var_over_mean']}, "
      f"m<=q {d_small['var_over_mean']}  -> concentrated in m>q")
print(f"  fekete: supermultiplicative={super_mult} (PROVED; splice checked on "
      f"{spliced} pairs)  -> rigorous lower rate {best_lower/3:.4f} "
      f"vs fitted bracket {bracket}")
print(f"  pincer: worst |R(M)| = {worst}, Hercher needs {HERCHER_L:,}"
      f"  -> {HERCHER_L//worst:,}x headroom")
