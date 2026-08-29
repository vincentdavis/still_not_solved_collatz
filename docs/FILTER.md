# The strategy filter

Reproduce with `uv run pytest python/tests/test_qtransfer.py` (36 tests) and
`lean/check.sh` (`Collatz/QTransfer.lean`).

Five tests a proposed proof strategy must pass **before any work starts**. Each
carries one executable witness or one pinned citation — no folklore. A strategy
that fails a test is not necessarily worthless (it may still produce
measurements, models, or structure); it just cannot *finish*, and must never be
presented as if it could.

The tests exist because this project has now proved, not merely observed, that
whole classes of hypotheses are uniform across systems that behave differently.
An argument built from such hypotheses proves too much, and therefore proves
nothing.

## Test A — the q-transfer test

**Replace `q = 1` by `q = 5` everywhere. If every hypothesis survives, the
argument is dead: `q = 5` has the real cycle `{19, 31, 49}`.**

The engine is the **q-transfer theorem** (proved; the strongest no-go in this
project):

> For every odd `q` with `3 ∤ q`, either sign,
> `S_k(q) = q · S_k(1) (mod 3^k)`, hence `a_k(q) = a_k(1)` for all `k`.

*Proof.* A halving vector is live for `M` at offset `q` iff
`3^t | 2^{B_t} M − c_t(q)` for all `t ≤ k`, plus the q-free caps
`2^{B_t} ≤ 3^t`. The constant is linear in `q`: `c_t(q) = q · c_t(1)`, from
`c_t = 2^{b_t} c_{t−1} + 3^{t−1} q` with `c_0 = 0`. So `M` is live for `q` iff
`q^{−1} M` is live for `1`, and multiplication by the unit `q` is a bijection
of `Z/3^k`. ∎

Checked: set equality (not just counts) for `k ≤ 10` and
`q ∈ {5, 7, 11, 25, −1, −5}` in Python; exhaustively over all residues mod
`3^4` for `q = 5, 7, 25` and `q ≡ −1` in Lean, kernel-only
(`qtransfer_5` … `qtransfer_neg_one`). The **forward** (2-adic) sieve obeys the
same scaling — `S^fwd_a(q) = q · S^fwd_a(1) (mod 2^a)`, checked `a ≤ 12` — so
its 1.80-bit saturation ceiling is q-invariant too.

**Consequence.** Every magnitude-free sieve statistic — `a_k`, the growth rate
`μ`, the death-rate bracket `[0.7364, 0.9465]`, the forward density
`0.2863…` — is *identical* between `q = 1` and `q = 5`. A cycling system and
the conjecturally cycle-free one are indistinguishable to the sieve. So no
theorem whose hypotheses are sieve statistics alone proves `q = 1`
cyclelessness.

**State the corollary carefully** (a referee caught the wrong phrasing): the
`q = 5` cycle does *not* "survive the sieve" — its maximum `49` **dies at
depth 8** (its own halving vector violates the cap; the same counterexample
GROUND_TRUTH §6 ✗1 records). The correct statement is: *statistics-only
hypotheses are q-uniform, hence false at `q = 5`*. The cycle is invisible to
the asymptotic sieve, living below its regime — which sharpens the guardrail's
own boundary: any bridge from magnitude-free statistics to actual cyclelessness
must pass through the exact sieve, and the exact sieve transfers only along
`M ↦ qM`, which does not preserve integrality in reverse. That non-invertible
step **is** the magnitude input.

**Scope.** The theorem covers the *magnitude-free* sieve of
docs/DEATH_DEPTH.md. The exact-size sieve (GROUND_TRUTH §4a, thresholds
`M > C_k·q`) is genuinely q-sensitive — do not conflate the two (the §4a
mistake).

## Test B — the sign test

**Replace `3n + 1` by `3n − 1` (`q = −1`). It has three cycles: `{1}`,
`{5, 7}`, `{17, 25, 37, 55, 41, 61, 91}` — verified by iteration in
`test_qtransfer.py`.**

Anything blind to the sign of `q` holds in a system with three nontrivial
cycles. The audit's measured boundary is clean:

- **Sign-blind (hold verbatim at `q = −1`):** all congruence-shaped
  conclusions — `M ≡ q (mod 4)` holds on both nontrivial maxima; ≥ 2 halvings
  out of the max and exactly 1 out of the min survive for `M > |q|`; the entire
  magnitude-free sieve (test A covers `q ≡ −1`: `qtransfer_neg_one`).
- **Sign-sensitive (flip):** exactly the positivity chain — `c_L > 0`, hence
  `2^B > 3^L` (T7). At `q = −1` all three cycles have `2^B < 3^L`
  (`2 < 3`, `8 < 9`, `2048 < 2187`).

Entropy/drift/density arguments have the identical `3/4` log-drift in both
systems and fail this test. This is the classical `3x − 1` litmus test in
executable form; the package's own `check_q` insists on `q > 0` because every
finishing-relevant theorem in it consumes positivity.

## Test C — the completion test

**Still valid over `Z₃` or `Z₂`? Then it proves too much.**

`−1 ∈ Z₃` survives every congruence depth (docs/WHY_NOT.md, `all_digits_two`),
and over `Z₂` the 3x+1 map is conjugate to the shift (Bernstein & Lagarias,
*Canad. J. Math.* 48 (1996) 1154–1169), with uncountably many 2-adic cycles.
Any argument stable under either completion admits those points. "Must use
archimedean size" is a theorem-shaped constraint, not advice.

## Test D — the density test

**A conclusion of the form "for almost every M" (any density) never excludes a
finite cycle.** Cycles are finite sets — density zero in every sense. Terras
(*Acta Arith.* 30 (1976) 241–252) and Tao (*Forum Math. Pi* 10 (2022) e12,
logarithmic density, "almost bounded") both leave the exceptional set exactly
where a cycle would live. (Tao's method is also sign-blind — test B.)

## Test E — the uniformity test

**Would the method decide the generalized (Conway) family? Then it contradicts
undecidability and must consume something specific to the pair (2, 3).**

Pinned statements only: Conway 1972 ("Unpredictable Iterations", Boulder
conference) — reach-1 for a given input is undecidable over the affine-mod-P
family; Kurtz & Simon 2007 (LNCS 4484, 542–553) — the "every orbit reaches 1"
problem for that family is `Π⁰₂`-complete. **Not** in the record: "cycle
existence is undecidable for the family" — plausible folklore, no source found;
do not cite it. Note also this test only constrains *uniform* methods; for the
actual (2, 3) system the binding constraint is this project's own equivalence
theorem (deciding the sieve *is* the conjecture), not undecidability.

Admissible (2, 3)-specific inputs, by the routes that actually pass: the
continued fraction of `log₂ 3` (Hercher's ladder — see GROUND_TRUTH §8), the
verified convergence bound `X₀` (Barina), and archimedean/valuation bounds on
`|2^B − 3^L|` and its p-adic cousins (Baker, Yu).

## Verdicts for the currently proposed strategies

| strategy | A | B | C | D | E | verdict |
|---|---|---|---|---|---|---|
| spectral / transfer-operator bounds on `μ` | ✗ | — | ✗ | — | — | measurement only; can never finish |
| BRW / branching-model rates for the tail | ✗ | ✗ | — | ✗ | — | model only; its numbers are never bounds |
| automaticity of the sieve (`μ` algebraic) | ✗ | — | ✗ | — | ✗¹ | dead twice over (also killed empirically: no linear recurrence, order ≤ 11 at `k ≤ 24`) |
| residue-only factorization constraints | ✗ | — | ✗ | — | — | congruence sieve in disguise |
| magnitude factorization (largest-prime-factor) | ✓ | ✓ | ✓ | ✓ | ✓ | Baker in disguise — admissible, currently weak |
| Baker / continued-fraction elimination | ✓ | ✓ | ✓ | ✓ | ✓ | **the only known coupler** — see the Hercher ladder |

¹ also covered by the in-repo impossibility theorem: the sieve has no finite
transfer matrix (state grows like `2^{1.76j}` — `deathdepth.py`).

Nothing in this file advances cyclelessness by an inch. It is a gate, and the
cost of running it is two minutes per proposal — which is the point.
