# Why a congruence sieve can never finish

Reproduce with `uv run pytest python/tests/test_padic.py`.

Five separate routes in this project end at the same wall. Each ends by
measuring a density that fails to reach zero. This is the same fact stated
without any analysis, densities, or limits — and with an explicit witness.

## Periodic points are the cycle equation

Run the backward map with a fixed halving pattern `(b₁,…,b_L)` and look for a
fixed point. Telescoping gives exactly one, and it is a rational:

```
y  =  c_L / (2^B − 3^L)
```

That **is** the cycle equation. So the periodic points of the backward map are
precisely the candidate cycles — one per halving pattern — and a genuine cycle is
a periodic point that happens to land on a **positive integer**.

`periodic_point` reproduces all **136** real `3n+q` cycles in the census exactly,
from their halving vectors alone, with 0 mismatches.

## The witness: −1

Take the pattern with every `b_j = 1`. Then `3y = 2y − 1`, so **`y = −1`** — for
every length `L`.

In `Z₃` the number `−1` is `…2222`: every digit of its base-3 expansion is a 2, so
`−1 ≡ 3^k − 1 (mod 3^k)` ends in a 2 at every depth — exactly the residue an odd
`b` requires at every step. So

> the class `−1 (mod 3^k)` survives the backward sieve at **every** depth

verified for `k = 1…12`. Hence `a_k ≥ 1` for all `k` — **provably, with a
witness**. The sieve can never empty.

And `−1` is not a natural number.

### Formalized (`lean/Collatz/Periodic.lean`)

The *algebra* of this section is now machine-checked — and it is the first file
in the development to leave `ℕ`, because the witness is negative. Core `Int`
only; still no Mathlib, still no `ℝ`.

Read the scope carefully, because it is narrower than the section around it:

- **Proved.** Any periodic point satisfies the cycle equation; the all-ones
  pattern's point is `−1`; `−1 mod 3^k = 3^k − 1` and every base-3 digit of that
  is a 2; only `b = 2` among constant patterns reaches a positive integer; a real
  cycle is a positive-integer periodic point.
- **Not proved.** *Existence* of a periodic point for an arbitrary pattern. Over
  `ℤ` that is false — `b = (3)`, `q = 1` gives `1/5`, and only 12 of the 340
  patterns of length `≤ 4` with entries `≤ 4` have an integer point. The general
  statement lives in `ℚ`/`ℤ₃`, which this development does not build.
- **Not proved.** Anything about the sieve itself: `a_k`, class survival, "the
  sieve never empties". `all_digits_two` is the *ingredient* for that argument,
  not the argument. `a_k ≥ 1` remains measured, not machine-checked.

| Lean name | statement |
|---|---|
| `IsPeriodic` | a point the pattern returns to itself, written without division |
| `IsPeriodic.closed` | the closed form `3^k z_k + c_k = 2^{B_k} y`, over `ℤ` |
| `IsPeriodic.cycle_equation` | **`y(2^B − 3^L) = c_L`, with no cycle in the hypotheses** |
| `periodic_unique` | off `2^B = 3^L` the periodic point is unique |
| `minus_one_of_ones` | the all-ones pattern's point is `−1`, at every length |
| `Pc_ones` | `c_L = 3^L − 2^L` for that pattern |
| `ones_not_a_cycle` | and `−1` is not a natural number |
| `neg_one_residue` | `−1 mod 3^k = 3^k − 1`, over `ℤ` |
| `all_digits_two` | every base-3 digit of `3^k − 1` is a 2 |
| `const_positive_integer` | `q=1`: only `b = 2` gives a positive integer, namely 1 |
| `Cycle.toPeriodic` | a real cycle *is* a periodic point |
| `Cycle.T7_from_periodic` | so `T7_eq` is the special case that lands on `ℕ` |

The shape of the argument is worth stating: `cycle_equation` needs no cycle in
its hypotheses. What distinguishes a cycle is that its solution is a *positive
integer* — and `Cycle.T7_from_periodic` derives the cycle-only `T7_eq` from the
general statement. (`T7_eq`'s own proof still stands; the two now sit beside
each other, with the general one showing the special one was never really about
cycles.)

A note for anyone extending this file: running `induction d` with a hypothesis
`a ≤ a + d` in scope makes Lean generalize that hypothesis and pulls
`Classical.choice` into the certificate. `check.sh` now rejects that (it used to
only warn), and the fix is to state the lemma in the `a + d` form and specialize
afterwards — see `two_pow_int_le_add`.

## The constant patterns, in full

`y = q/(2^b − 3)`:

| b | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| `y` (q=1) | **−1** | **1** | 1/5 | 1/13 | 1/29 |

`b = 2` gives `1` — the trivial cycle, and the **only** constant pattern whose
periodic point is a positive integer (checked for `b ≤ 30`).

## The point

A congruence sieve tests membership in `Z₃`. It cannot see **sign** or
**integrality**. Its limit set is full of 3-adic points like `−1` and `1/5` that
pass every congruence test at every depth and are not natural numbers.

Collatz is the statement that **no periodic point other than 1 lands on a
positive integer** — and that is not a congruence question at all. No amount of
sieving addresses it, which is why all five routes in this project stop in the
same place.

It also explains the shape of the earlier measurements. The surviving set has
box dimension `log₃λ`, somewhere in `[0.87, 0.95]` on the computed range —
**positive**, hence uncountable, hence never empty; and **below 1**, hence
density zero. Both halves of "density zero but nonempty" in one number.

## The sieve cannot even see `q` — the transfer theorem

Added after the direction survey; reproduce with
`uv run pytest python/tests/test_qtransfer.py`. This section upgrades the wall
above from "the sieve never empties" to something stronger: **the sieve's
statistics cannot distinguish a cycling system from a conjecturally cycle-free
one.**

> **Theorem (q-transfer).** For every odd `q` with `3 ∤ q`, either sign,
> `S_k(q) = q · S_k(1) (mod 3^k)` — so `a_k(q) = a_k(1)` for all `k`.

*Proof.* Liveness of `M` to depth `k` is `3^t | 2^{B_t} M − c_t(q)` for
`t ≤ k` plus the q-free caps `2^{B_t} ≤ 3^t`. The constant is linear in `q`
(`c_t = 2^{b_t} c_{t−1} + 3^{t−1} q`, `c_0 = 0`, so `c_t(q) = q·c_t(1)`);
hence `M` is live for `q` iff `q^{−1}M` is live for `1`, and multiplication by
the unit `q` bijects `Z/3^k`. ∎

Checked as *set equality* for `k ≤ 10`, `q ∈ {5, 7, 11, 25, −1, −5}`;
machine-checked exhaustively at `k ≤ 4` for `q = 5, 7, 25` and `q ≡ −1`
(`lean/Collatz/QTransfer.lean`, kernel only). The forward 2-adic sieve scales
the same way (`a ≤ 12` checked), so its 1.80-bit ceiling is q-blind too.

Every number this project's sieve produces — `a_k`, `μ`, the death-rate
bracket, the `0.2863` forward density — is therefore **identical at `q = 5`**,
where the real cycle `{19, 31, 49}` exists. A hypothesis expressible in sieve
statistics alone is q-uniform, and at `q = 5` it would prove a falsehood.

Phrase the corollary correctly: the `q = 5` cycle does **not** survive the
magnitude-free sieve — its maximum `49` dies at depth 8, because its own
halving vector violates the cap (the §6 ✗1 counterexample). The cycle lives
*below the sieve's asymptotic regime*, which is the sharpest possible statement
of where magnitude enters: the exact sieve transfers only along `M ↦ qM`, and
that map has no integrality-preserving inverse.

The executable five-test gate built from this theorem (and its sign, completion,
density and uniformity cousins) is **docs/FILTER.md**.

## Prior art

The rational form of a cycle is Böhm & Sontacchi (1978); the 3-adic reading of
the Collatz map is standard (Lagarias' survey). Nothing here is new. It is
recorded because it is the cleanest available answer to the question the rest of
the project keeps running into.
