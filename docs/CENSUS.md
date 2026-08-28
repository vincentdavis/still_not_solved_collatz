# Is the Collatz cycle heuristic calibrated?

Reproduce with:

```bash
python3 python/tools/gen_census_data.py 100 1000
uv run pytest python/tests/test_census.py
```

## The question

Belief that Collatz has no nontrivial cycle rests on a heuristic: the expected
number of bounded backward chains decays like `(λ/3)^k` with `λ/3 ≈ 0.9465`, so
cycles "should not" exist. Subcritical — but by only **5.4 %**.

`3n+q` is the only place that heuristic can be checked against a world where
cycles genuinely exist. If it systematically mispredicts there, that is direct
evidence about whether to trust it at `q = 1`.

**Design.** Count *primitive* cycles (`gcd(q, elements) = 1`, so scaled copies of
smaller systems aren't double-counted) with maximum `≤ R·q`. Fixing the **ratio**
`X/q` rather than `X` makes the heuristic's prediction the same for every `q`, so
the counts become directly comparable. Census: `R = 100`, all admissible
`q ≤ 1000` — 333 systems, **1080 primitive cycles**.

## Formalized (`lean/Collatz/Census.lean`)

This section's *theorems* are machine-checked; its *measurements* are not, and
the distinction is the point.

| Lean name | statement |
|---|---|
| `Cycle.q_dvd_sub` | a cycle with `gcd(M, q) = 1` forces `q ∣ 2^B − 3^L` |
| `Cycle.burst` | if `2^B − 3^L = q` exactly then `M·q = c_L` |
| `q1_burst` | `2^B = 3^L + 1` with `L ≥ 1` forces `(L, B) = (1, 2)` |

`q_dvd_sub` is the engine of the whole effect: cycles do not scatter across `q`,
they concentrate on the `q` dividing some `2^B − 3^L`, and those are sparse.
`q1_burst` is why `q = 1` is unlike every other `q` here, and its proof is a
mod-8 count — `3^L + 1` is `2` or `4` mod `8`, never `0`, so `2^B ≤ 4`.

`Census.lean` also formalizes the *exact* half of the death-depth row:
`Cycle.aa k` counts the residues mod `3^k` surviving the magnitude-free sieve,
and the kernel checks `a₁…a₄ = 1, 2, 3, 6` directly. The ceiling is mechanical
(`countLE` recurses once per residue, so `k = 5` exceeds Lean's default
`maxRecDepth` and `set_option` is banned), not mathematical.

**Not formalized — and the three reasons are different, which matters.**

- **Over-dispersion.** The statistic *is* a proposition about integers:
  `N·Σc² − (Σc)² > 4·N·Σc` needs no reals. The obstacle is **infeasibility** —
  reducing a 333-system census inside the kernel is out of reach with
  `native_decide` banned. Calling this a category error would be wrong.
- **"Poisson is rejected"** is a modelling judgement on top of that statistic,
  and is not a proposition about the integers at all.
- **The tail rate** is genuinely **open**, not merely unformalized: separating
  the two candidate models needs `k ≈ 36` (`DEATH_DEPTH.md`). Note this is the
  *rate*; the `a_k` underneath it are formalized, per above.
- **The box dimension** rests on an unresolved limit, so it would not be a
  theorem even with `ℝ` in hand.

The project's accounting table used to carry all of this on one line marked
"measurements, not theorems". It now carries three, because some of it was
theorems — and an earlier draft of this very file made the same bundling
mistake one level down, declining `a_k` because the *rate* is open.

## Result 1 — the heuristic is not calibrated

| | value |
|---|---|
| mean cycles per `q` | 3.243 |
| variance | 14.965 |
| **variance / mean** | **4.614** |

Poisson would give 1. Some `q` carry 22–31 cycles where Poisson predicts
essentially none. The over-dispersion survives every control: it holds
separately for prime `q` (var/mean 4.2) and composite `q` (5.0), is not
explained by the number of divisors, and — the sharpest clue — is **extreme
within a single cycle length** (var/mean up to 13.9 at fixed `L`) while counts
at *different* lengths are essentially **uncorrelated** (|r| < 0.23).

So it is not that some `q` are globally "rich". Something acts per-`(L, B)`.

## Result 2 — the congruence that acts per-`(L,B)`

> **Theorem.** For a primitive cycle of `3n+q` with `L` odd elements and `B`
> total halvings, `q | 2^B − 3^L`, i.e. `2^B ≡ 3^L (mod q)`.

*Proof.* For a prime `p | q`: from `2^{a_j} x_j = 3x_{j−1} + q`, if `p | x_{j−1}`
then `p | 2^{a_j} x_j`, and `p` is odd, so `p | x_j`. Going once around, `p`
divides every element or none; primitivity rules out "every", so
`gcd(x_0, q) = 1`. Telescoping the same relation gives the cycle equation
`x_0(2^B − 3^L) = qS`, so `q | x_0(2^B − 3^L)`, and coprimality gives
`q | 2^B − 3^L`. ∎

Verified exactly: **1080/1080 cycles**, with the supporting lemma checked on all
**23 325 elements**. (Standard in the `3n+q` literature; reproduced because it is
what makes the census interpretable.)

## Result 3 — the burst mechanism

The strongest configuration is `2^B − 3^L = q` **exactly**. Then the cycle
equation collapses to `x_0 = S`, so *every* admissible halving vector of that
`(L, B)` yields an integer candidate — one hit can produce a burst of cycles.

| | count | mean cycles |
|---|---|---|
| `q` admitting `2^B − 3^L = q` | 28 | **7.64** |
| `q` not | 304 | 2.85 |

A 2.7× enrichment. `q = 5`'s cycle `{19, 31, 49}` has `L = 3, B = 5` — which *is*
its exact hit, `2⁵ − 3³ = 5`.

Removing the `d = 1` cycles drops var/mean from 4.61 to 3.01: the mechanism
explains roughly a third of the excess dispersion, **not all of it**. The
remainder is unexplained.

## Result 4 — and why `q = 1` is different

`2^B − 3^L = 1` has, for `L ≥ 1`, the single solution `(L, B) = (1, 2)` — which is
exactly the trivial cycle `{1}`. Elementary: for `L ≥ 2`, `3^L + 1 ≡ 2` or
`4 (mod 8)`, so `2^B ≤ 4`. No Catalan needed.

**So `q = 1` gets exactly one burst, and it is the cycle we already know about.**

## The verdict — including on this experiment

The heuristic's Poisson assumption is **rejected** for `3n+q`. But the reason it
fails does **not** transfer to `q = 1`, and that cuts against the experiment
itself:

- For `q > 1`, cycles are largely manufactured by the arithmetic condition
  `q | 2^B − 3^L`, which is satisfiable with a modest `2^B − 3^L`.
- For `q = 1` that condition is **vacuous** — and correspondingly useless. What
  constrains `q = 1` instead is `x_0 = S/(2^B − 3^L)` with `x_0 > 2.39×10²¹`,
  forcing `2^B − 3^L` to be *minuscule* relative to `2^B`. That is a Diophantine
  condition of a completely different character.

**Conclusion: `3n+q` is a poor proxy for `q = 1`.** Cycle abundance there is
driven by a mechanism `q = 1` structurally lacks, so it says little about whether
to trust the heuristic for Collatz itself. The experiment answers its own
question in the negative — the test is confounded.

What it does leave behind: a clean congruence, a measured mechanism, a 2.7×
effect, and an elementary reason why `2^B − 3^L = q` singles `q = 1` out.

## Prior art

None of this is claimed as new. The congruence `2^B ≡ 3^L (mod q)` is folklore in
the `3n+q` literature; the dispersion statistics are measurements, not theorems.
