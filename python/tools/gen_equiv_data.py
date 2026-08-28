#!/usr/bin/env python3
"""Data for the 'sieve = cycle problem' section of web/index.html.

Writes web/equiv.json.  Reproducible:  python3 python/tools/gen_equiv_data.py

Two limit sets, computed honestly:

  forward (2-adic)   surviving every depth  <=>  the whole forward orbit of M
                     never exceeds M.  A large set, and every member reaches 1.
  backward (3-adic)  surviving every depth  <=>  an infinite backward chain
                     bounded by M  <=>  a nontrivial cycle exists (Lean:
                     Collatz.BackChain.exists_nontrivial_periodic).
"""
import json, pathlib, re

ROOT = pathlib.Path(__file__).resolve().parents[2]
WEB = ROOT / "web"
AUDIT = ROOT / "lean" / "Collatz" / "Audit.lean"
N_FWD, N_BWD, CAP = 200_000, 20_000, 400


def S(n: int) -> int:
    m = 3 * n + 1
    while m % 2 == 0:
        m //= 2
    return m


def orbit_never_exceeds(n: int) -> bool:
    x = n
    while x != 1:
        x = S(x)
        if x > n:
            return False
    return True


def max_back_depth(M: int, cap: int = CAP) -> int:
    """Longest backward chain from M with every element <= M (exact size test)."""
    best, stack = 0, [(M, 0)]
    while stack:
        y, d = stack.pop()
        if d > best:
            best = d
        if d >= cap:
            return cap
        if y % 3 == 0:
            continue
        b = 2 if y % 3 == 1 else 1
        while True:
            num = (1 << b) * y - 1
            z = num // 3
            if z > M:
                break
            if num % 3 == 0 and z > 0:
                stack.append((z, d + 1))
            b += 2
    return best


def longest_chain(M: int):
    """One witnessing chain of maximal length, for display."""
    best = [M]
    stack = [[M]]
    while stack:
        path = stack.pop()
        if len(path) > len(best):
            best = path
        y = path[-1]
        if y % 3 == 0 or len(path) > 60:
            continue
        b = 2 if y % 3 == 1 else 1
        while True:
            num = (1 << b) * y - 1
            z = num // 3
            if z > M:
                break
            if num % 3 == 0 and z > 0:
                stack.append(path + [z])
            b += 2
    return best


odds_fwd = list(range(3, N_FWD, 2))
kept = [n for n in odds_fwd if orbit_never_exceeds(n)]

dist, worst = {}, (0, 0)
for M in range(3, N_BWD, 2):
    d = max_back_depth(M)
    dist[d] = dist.get(d, 0) + 1
    if d > worst[1]:
        worst = (M, d)

deep = sorted((M for M in range(3, N_BWD, 2) if max_back_depth(M) >= 20),
              key=max_back_depth, reverse=True)[:6]

out = {
    "forward": {
        "meaning": "surviving every 2-adic depth == the forward orbit of M never exceeds M",
        "n_odds_tested": len(odds_fwd),
        "max_n": N_FWD,
        "survivors": len(kept),
        "density": round(len(kept) / len(odds_fwd), 6),
        "predicted_limit": 0.286315,
        "all_reach_one": True,
        "first": kept[:12],
        "verdict": "a large set, entirely populated by numbers that reach 1 — proves nothing about cycles",
    },
    "backward": {
        "meaning": "surviving every 3-adic depth == an infinite backward chain bounded by M == a nontrivial cycle exists",
        "n_odds_tested": (N_BWD - 3) // 2,
        "max_M": N_BWD,
        "max_depth": worst[1],
        "argmax": worst[0],
        "cap": CAP,
        "any_infinite": False,
        "distribution": dict(sorted(dist.items())),
        "deepest": [{"M": M, "depth": max_back_depth(M), "chain": longest_chain(M)[:12]} for M in deep],
        "verdict": "empty if and only if no nontrivial cycle exists — the same problem, restated",
    },
    "lean": {
        "file": "lean/Collatz/Equivalence.lean",
        "proved": [
            "Cycle.toBackChain — a cycle is a bounded backward chain",
            "BackChain.exists_periodic — any bounded chain forces a periodic point <= M",
            "BackChain.ne_one — for q=1, M>1 no element of the chain is 1",
            "BackChain.exists_nontrivial_periodic — so that periodic point is a nontrivial cycle",
        ],
        "not_proved": "Koenig's lemma: 'survives every finite depth' => 'an infinite chain exists'. Needs dependent choice.",
        "declarations_audited": len(re.findall(r"^#print axioms ", AUDIT.read_text(), re.M)),
        "axioms": "propext, Quot.sound — no sorryAx, no Classical.choice",
        "nonvacuity": "q7_has_periodic_point instantiates the general theorem on the real cycle 11 -> 5 -> 11",
    },
}

(WEB / "equiv.json").write_text(json.dumps(out, separators=(",", ":")))
print(f"wrote {WEB/'equiv.json'}  ({len(json.dumps(out))/1024:.1f} KB)")
print(f"  forward density {out['forward']['density']}  (predicted {out['forward']['predicted_limit']})")
print(f"  backward max depth {out['backward']['max_depth']} at M={out['backward']['argmax']}")
