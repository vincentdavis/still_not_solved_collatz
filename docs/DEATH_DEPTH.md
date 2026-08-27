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

## The asymptotics — attempted, and still unresolved

Two different counts matter:

- **`N_k`** — the number of admissible halving vectors `(b₁…b_k)` with `b_j ≥ 1`
  and `B_j ≤ ⌊j·log₂3⌋`. Its state is the scalar `B_j`, so it has a genuine
  **O(k²) transfer-matrix DP** (`backtree.count_admissible_halving_vectors`).
- **`a_k`** — the number of surviving *residues*. Each vector pins one residue,
  but one `M` can carry several chains, so `a_k ≤ N_k` with equality only for
  `k ≤ 3`.

### Confirmed: the tree constant

`N_k ~ C·λ^k·k^(−3/2)` with

    λ = aᵃ/(a−1)^(a−1),  a = log₂3,  λ = 2.8395137305

Verified to **six significant figures** by running the DP to `k = 8000`:
long-baseline estimates give relative error `1.4×10⁻⁵`, a joint fit for both
`λ` and the power gives `8.4×10⁻⁶` (recovered power `−1.46` vs `−1.5`).

### Not confirmed: whether `a_k` shares that rate

`a_k` was computed **exactly to k = 23** by DFS over the 3-adic tree of
surviving residues (`deathdepth.surviving_residue_count`), which visits `a_k`
nodes instead of `3^k`:

    1, 2, 3, 6, 10, 22, 50, 104, 254, 538, 1302, 3202, 7553, 19206, 44732,
    113034, 262243, 660954, 1693714, 4204015, 10995110, 26812105, 69626820

(`a_21 = 10 995 110` independently reproduces the "classes mod 3²¹" figure
`GROUND_TRUTH.md` § 4a obtained by a different route.)

`a_k` was extended to **k = 24** (`a_24 = 182 840 849`). `a_k/N_k` declines
from 1 to 0.29, and two models fit it **indistinguishably**:

| model | form | ⇒ `λ_a` | ⇒ tail rate |
|---|---|---|---|
| polynomial | `a_k/N_k ~ C·k^(−0.74)` | `λ` = 2.8395 | **0.9465** |
| geometric | `a_k/N_k ~ C·(0.946)^k` | 2.6874 | **0.8958** |

Neither leads stably. **The ranking reverses on a single extra term:**

| data through | in-sample R² | out-of-sample mean err | ahead |
|---|---|---|---|
| `k = 23` | 0.941 vs 0.928 | 6.5 % vs 7.6 % | polynomial |
| `k = 24` | 0.937 vs 0.934 | 7.1 % vs 11.0 % | **geometric** |

Out-of-sample (fitted on `k ≤ 20`, scoring 21–24) the models split two wins
each. That reversal *is* the result: the computed range cannot separate them.

### Why it could not be settled

There is **no finite transfer matrix for `a_k`**. The state governing a node's
future is the *set* of `(B_j, y_j mod 3)` over its live chains; `B_j` ranges over
about `0.585·j` values, so the state space grows like `2^(1.76 j)`. `N_k` escapes
this because its state is the single number `B_j`.

And enumeration runs out. At `k = 24` the two model predictions differ by only
**9.6 %**, while the residual Sturmian oscillation in `a_k/N_k` is **±18.5 %**.
The separation grows ~3 %/step, so it clears three times the oscillation only
near **`k = 36`** — roughly `2×10¹³` tree nodes, on the order of **a year** of
compute. Not attempted. (These figures come from
`python/tools/gen_asym_data.py`, which computes them rather than assuming them.)

**Bracketed result:** `0.897 ≤ tail rate ≤ 0.947`.

⚠️ **A second correction.** Even if the rate is the conjectured `λ/3`, the
polynomial factor is `k^(−2.2)`, **not** the `k^(−3/2)` recorded earlier —
since `a_k ~ N_k·k^(−0.70) ~ λ^k·k^(−3/2−0.70)`.

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
