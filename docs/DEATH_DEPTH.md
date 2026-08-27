# `d(M)` — how deep the backward sieve has to dig

Companion to [`GROUND_TRUTH.md`](GROUND_TRUTH.md) § 4a. Reproduce everything here with

```bash
python3 python/tools/gen_tail_data.py 12
uv run pytest python/tests/test_deathdepth.py
```

## The quantity

For odd `M`, let **`d(M)`** be the length of the longest backward chain from `M`
whose every element stays at or below `M`:

    M = y₀,  y₁,  y₂,  …      S(y_{j+1}) = y_j ,    y_j ≤ M

"`M` survives the backward sieve at depth `k`" is exactly `d(M) ≥ k`.

**Why it is the right quantity.** `lean/Collatz/Equivalence.lean` proves that an
*infinite* such chain exists precisely when a nontrivial cycle does. So a
counterexample to Collatz is exactly an odd `M > 1` with `d(M) = ∞`, and a
uniform bound on `d` would settle the conjecture. Everything below measures how
`d` is distributed. **It proves nothing.**

## The exact result

For `M` large enough that the size test has entered its asymptotic regime,
`d(M)` depends **only on `M mod 3^k`**. The tail is therefore an exact rational:

    P(d ≥ k) = a_k / 3^k

| k | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|---|---|----|----|----|----|----|
| `a_k` | 1 | 2 | 3 | 6 | 10 | 22 | 50 | 104 | 254 | 538 | 1302 | 3202 | 7553 | 19206 |

These are **exact, not sampled**. Scanning `3^K` consecutive odd numbers hits
every residue mod `3^K` exactly once (2 is invertible mod `3^K`), and every
count came out divisible by `3^{K−k}`. Verified at `K = 14`, base `10^18`, and
independently at base `10^12`.

## Why the distribution ignores the size of `M`

Because for large `M` the exact size test

    M (2^{B_k} − 3^k) ≤ c_k

degenerates into the pure halving-budget condition `2^{B_k} ≤ 3^k`, which never
mentions `M`'s magnitude. `deathdepth.death_depth_congruence_only` implements
that magnitude-free model, and it agrees with the exact computation on every
large `M` tested. Measured tails at `10^6`, `10^9`, `10^12`, `10^18` agree to
six decimals.

## The asymptotics — a conjecture, not a measurement

The ratios `a_k / a_{k−1}` climb slowly and oscillate:

    2.00  1.50  2.00  1.67  2.20  2.27  2.08  2.44  2.12  2.42  2.46  2.36  2.54

They appear to be heading for the backward-tree growth constant already used in
[`backtree`](../python/collatz_maxodd/backtree.py),

    λ = aᵃ / (a−1)^(a−1)  with  a = log₂3  ,   λ ≈ 2.83951

which would give

    P(d ≥ k)  ≈  C · (λ/3)^k · k^(−3/2) ,      λ/3 ≈ 0.94650

**Not established.** At `k = 14` the ratio is only 2.54, and a `k^(−3/2)` fit
over `k = 12…30` returns ρ ≈ 0.909, about 4 % below the predicted 0.9465. The
conditional rate `r_k = P(d≥k+1)/P(d≥k)` is still rising at `k = 30` (≈ 0.89).
Consistent with the conjecture; not a confirmation of it.

⚠️ **A correction.** An earlier fit of `λ ≈ 0.705` over `k = 3…10` was simply
pre-asymptotic and is **wrong**. The tail is substantially heavier than that
suggested.

## What it does not show

The rate is below 1, so almost every `M` dies at finite depth. That is a
**density** statement, and density zero is not emptiness — the same wall as the
residue sieve itself (`GROUND_TRUTH.md` § 4c). Deepest observed: `d = 121` over
8 × 10⁶ samples; `d(3077) = 48` is the deepest below 20 000. Nothing has ever
approached the cutoff, which by the equivalence theorem is what a cycle would
look like.

## Prior art

The backward tree, its growth constant, and the whole sieve setup are standard —
see the citations in `GROUND_TRUTH.md`. The `a_k` sequence above was **not found
in OEIS** (full sequence and prefixes, checked 2026-08-26; the API was validated
against A000045 in the same session). That is weak evidence it has not been
tabulated. It is **not** evidence that anything here is new mathematics: `a_k`
is an elementary counting statistic of a well-known object.
