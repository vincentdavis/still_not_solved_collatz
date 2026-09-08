# `lean/` — Mathlib-free formalization of the cycle-maximum constraints

Lean 4 **core only**. `lakefile.toml` has zero `require` lines; nothing is
downloaded to build this. Toolchain pinned in `lean-toolchain` to
`leanprover/lean4:v4.33.1`.

```
cd lean
lake build      # zero errors, zero warnings
./check.sh      # clean build + escape-hatch scan + axiom audit + coverage check
```

**Status: no `sorry` anywhere.** `#print axioms` runs at build time on **every
named declaration** — every theorem, every definition, the `Cycle` structure
itself, and every `Cycle` instance (341 declarations, `Collatz/Audit.lean`).
All report `[propext, Quot.sound]`, `[propext]`, or nothing — no `sorryAx`, and
no `Classical.choice`.

> ⚠️ **`lake build` succeeding is NOT evidence of no `sorry`.** A `sorry` only
> produces a *warning*; the build still prints "Build completed successfully".
> This was verified by injecting one. The real gates are `check.sh` step 1
> (zero **warnings**) and step 3 (the `sorryAx` audit). `check.sh` has been
> tested against four deliberate defects — a hard-error `sorry`, a silent
> build-passing `sorry`, a deleted `#print axioms` line, and a
> `set_option debug.skipKernelTC true` — and fails on all four.

---

## Files

| file | contents |
|---|---|
| `Collatz/Odd.lean` | `v2`, `oddPart`, `S` (the Syracuse map `S_q`), equation lemmas, bridge lemma, `S_spec` |
| `Collatz/Core.lean` | **cycle-free** lemmas — the actual mathematical content |
| `Collatz/Cycle.lean` | `structure Cycle`, `bb`/`BB`/`cc`, faithfulness, T0–T8 |
| `Collatz/Bridge.lean` | `iter`, and `Cycle.ofOrbit` — **every real `S_q`-cycle yields a `Cycle q`** |
| `Collatz/Examples.lean` | three hand-built `Cycle` instances + worked examples |
| `Collatz/Guards.lean` | `#guard` + `example` value pins; three bridge-built instances |
| `Collatz/Audit.lean` | `#print axioms` for every named declaration |
| `Collatz/Unproved.lean` | comments only — what is **not** formalized and why |
| `check.sh` | CI check (5 steps, all with tested negative controls) |

Notation is that of `docs/GROUND_TRUTH.md`: `S_q`, `L`, `M`, `B`, `y_k`, `b_k`,
`B_k`, `c_k`.

---

## Definitions (total, no fuel parameter)

```lean
def v2 : Nat → Nat                       -- 2-adic valuation, v2 0 = 0
def oddPart : Nat → Nat                  -- m / 2^v2 m, oddPart 0 = 0
def S (q n : Nat) : Nat := oddPart (3 * n + q)      -- S_q
```

Both recursive definitions are well-founded (`Nat.div_lt_self`); no `partial`.
Because well-founded definitions are *sealed*, `decide` and `rfl` cannot
evaluate them — the kernel reaches them only through the equation lemmas. So
`Collatz/Guards.lean` pins concrete values along **two independent paths**:

* `#guard …` — the **compiled/interpreted** definition (a false `#guard` is a
  build error; verified);
* `example … := by simp [S, oddPart]` — a **kernel-checked proof term** from
  the equation lemmas (verified negative control: `S 1 7 = 12` leaves `⊢ False`).

Agreement between the two rules out a compiled-vs-logical divergence. All
expected values come from an independent Python implementation: `v2` and
`oddPart` on `1…24`, `2^v2 m · oddPart m = m` on `1…500`, `S 1 / S 5 / S 7` on
the first 24 odd inputs, and `iter` along four concrete orbits.

Cycles are presented **backwards from the maximum**, matching GROUND_TRUTH's
`y_k`: `y 0 = M`, `y (k+1)` is the odd predecessor of `y k`, indices are plain
`Nat` with periodicity `hper`.

---

## FULLY PROVED (no `sorry`, no extra axioms)

### Cycle-free lemmas — `Collatz/Core.lean`, `Collatz/Odd.lean`

```lean
theorem two_pow_v2_mul_oddPart {m : Nat} (hpos : 0 < m) :
    2 ^ v2 m * oddPart m = m

theorem S_spec {q n : Nat} (hq : q % 2 = 1) (hn : n % 2 = 1) :
    ∃ b, 1 ≤ b ∧ 3 * n + q = 2 ^ b * S q n ∧ (S q n) % 2 = 1
```

**T0 — an odd multiple of 3 has no odd predecessor:**

```lean
theorem T0_core {q y x b : Nat} (hq3 : q % 3 ≠ 0) (h : 3 * y + q = 2 ^ b * x) :
    x % 3 ≠ 0

theorem no_odd_pred_of_three_dvd {q n y : Nat} (hq : q % 2 = 1) (hq3 : q % 3 ≠ 0)
    (hn3 : n % 3 = 0) (hy : y % 2 = 1) : S q y ≠ n
```

**T1 — one halving always increases, so `n ≡ 3 (mod 4)` is never a maximum:**

```lean
theorem T1_core {q n m : Nat} (hq : 0 < q) (h : 3 * n + q = 2 * m) : n < m

theorem T1_core_mod4 {q n : Nat} (hq : q % 2 = 1) (hn : n % 2 = 1) (hqp : 0 < q)
    (h4 : (3 * n + q) % 4 = 2) : n < S q n

theorem lt_S_of_three_mod_four {n : Nat} (h : n % 4 = 3) : n < S 1 n
```

**T2 — the incoming edge of the maximum has `b = 1`:**

```lean
theorem T2_core {q y x b : Nat} (_hq : 0 < q) (hxq : q < x) (hb1 : 1 ≤ b)
    (hyx : y ≤ x) (h : 3 * y + q = 2 ^ b * x) : b = 1

theorem T2_pred {q y x b : Nat} (hq : 0 < q) (hxq : q < x) (hb1 : 1 ≤ b)
    (hyx : y ≤ x) (h : 3 * y + q = 2 ^ b * x) : 3 * y + q = 2 * x
```

**Lemma U — the predecessor lemma** (uniqueness needs *no* hypothesis relating
`p` and `q`):

```lean
theorem pred_unique_core {q p y y' b b' : Nat} (hq3 : q % 3 ≠ 0)
    (hy : 0 < y) (hy' : 0 < y') (hyp : y ≤ p) (hyp' : y' ≤ p)
    (hb : 1 ≤ b) (hb' : 1 ≤ b')
    (h : 3 * y + q = 2 ^ b * p) (h' : 3 * y' + q = 2 ^ b' * p) : y = y'

theorem pred_unique {q p y y' : Nat} (hq : q % 2 = 1) (hq3 : q % 3 ≠ 0)
    (hy : 0 < y) (hy' : 0 < y') (hyo : y % 2 = 1) (hyo' : y' % 2 = 1)
    (hyp : y ≤ p) (hyp' : y' ≤ p)
    (hs : S q y = p) (hs' : S q y' = p) : y = y'

theorem pred_exists {q p : Nat} (hq : q % 2 = 1) (hp : p % 2 = 1)
    (hlt : q < 2 * p) (h3 : (2 * p) % 3 = q % 3) :
    ∃ y, 0 < y ∧ y % 2 = 1 ∧ y < p ∧ 3 * y + q = 2 * p ∧ S q y = p
```

`q = 1` packaging — *"the only odd predecessor of `n` below `n` is `(2n−1)/3`,
and it exists iff `n ≡ 2 (mod 3)`"*:

```lean
theorem pred_le_eq_q1 {p y : Nat} (hp1 : 1 < p) (hyo : y % 2 = 1)
    (hyp : y ≤ p) (hs : S 1 y = p) : 3 * y + 1 = 2 * p

theorem pred_le_unique_q1 {p y y' : Nat} (hy : 0 < y) (hy' : 0 < y')
    (hyo : y % 2 = 1) (hyo' : y' % 2 = 1) (hyp : y ≤ p) (hyp' : y' ≤ p)
    (hs : S 1 y = p) (hs' : S 1 y' = p) : y = y'

theorem pred_lt_exists_q1 {p : Nat} (hp : p % 2 = 1) (h3 : p % 3 = 2) :
    ∃ y, 0 < y ∧ y % 2 = 1 ∧ y < p ∧ 3 * y + 1 = 2 * p ∧ S 1 y = p

theorem pred_le_iff_q1 {p : Nat} (hp : p % 2 = 1) (hp1 : 1 < p) :
    (∃ y, 0 < y ∧ y % 2 = 1 ∧ y ≤ p ∧ S 1 y = p) ↔ p % 3 = 2
```

**T5 — the second backward hop:**

```lean
theorem T5_ineq {q x y1 y2 b2 : Nat}
    (h1 : 3 * y1 + q = 2 * x) (h2 : 3 * y2 + q = 2 ^ b2 * y1) (hy2 : y2 ≤ x) :
    2 ^ b2 * (2 * x) ≤ 9 * x + 3 * q + 2 ^ b2 * q

theorem T5_core_sharp {q x y1 y2 b2 : Nat} (hx : 11 * q < 7 * x)
    (h1 : 3 * y1 + q = 2 * x) (h2 : 3 * y2 + q = 2 ^ b2 * y1) (hy2 : y2 ≤ x) :
    b2 ≤ 2

theorem T5_core_q1 {x y1 y2 b2 : Nat} (hx : 2 ≤ x)
    (h1 : 3 * y1 + 1 = 2 * x) (h2 : 3 * y2 + 1 = 2 ^ b2 * y1) (hy2 : y2 ≤ x) :
    b2 ≤ 2
```

### Cycle-level theorems — `Collatz/Cycle.lean` (namespace `Collatz.Cycle`)

All take `(C : Cycle q)`; `C.M` is the maximum.

```lean
theorem T0 (i : Nat) : C.y i % 3 ≠ 0
theorem T1 : (3 * C.M + q) % 4 = 0                     -- NO hypothesis
theorem T1_mod4 : C.M % 4 = q % 4                      -- NO hypothesis
theorem T1_q1 (C : Cycle 1) : C.M % 4 = 1              -- NO hypothesis
theorem T2 (hMq : q < C.M) : 3 * C.y 1 + q = 2 * C.M
theorem T2_mod3 (hMq : q < C.M) : (2 * C.M) % 3 = q % 3
theorem T2_bb (hMq : q < C.M) : C.bb 1 = 1
theorem T2_unique {y : Nat} (hy : y % 2 = 1) (hyM : y ≤ C.M)
    (hs : S q y = C.M) : y = C.y 1                     -- NO hypothesis on M vs q
theorem T2_q1 (C : Cycle 1) (hMq : 1 < C.M) : C.M % 3 = 2
theorem T3_gen (hMq : q < C.M) : C.M % 12 = (5 * q) % 12          -- general q
theorem T4_mod9 (hMq : q < C.M) : (2 * C.M) % 9 ≠ q % 9           -- general q
theorem T4_base_gen (hMq : q < C.M) : C.M % 36 ≠ (5 * q) % 36     -- general q
theorem T3 (C : Cycle 1) (hMq : 1 < C.M) : C.M % 12 = 5
theorem T3_of_L (C : Cycle 1) (hL : 2 ≤ C.L) : C.M % 12 = 5
theorem T4_base (C : Cycle 1) (hMq : 1 < C.M) : C.M % 36 = 17 ∨ C.M % 36 = 29
theorem T4_base_of_L (C : Cycle 1) (hL : 2 ≤ C.L) : C.M % 36 = 17 ∨ C.M % 36 = 29
theorem T5_gen (hM : 11 * q < 7 * C.M) {b : Nat}
    (hb : 3 * C.y 2 + q = 2 ^ b * C.y 1) : b ≤ 2
theorem T5 (C : Cycle 1) (hM : 2 ≤ C.M) {b : Nat}
    (hb : 3 * C.y 2 + 1 = 2 ^ b * C.y 1) : b ≤ 2
theorem T5' (C : Cycle 1) (hM : 2 ≤ C.M) :
    ∃ b, 1 ≤ b ∧ b ≤ 2 ∧ 3 * C.y 2 + 1 = 2 ^ b * C.y 1
theorem T5_of_L (C : Cycle 1) (hL : 2 ≤ C.L) :
    ∃ b, 1 ≤ b ∧ b ≤ 2 ∧ 3 * C.y 2 + 1 = 2 ^ b * C.y 1
theorem T5_bb (C : Cycle 1) (hM : 2 ≤ C.M) : C.bb 2 ≤ 2
theorem T5_bb_gen (hM : 11 * q < 7 * C.M) : C.bb 2 ≤ 2
theorem T8 (C : Cycle 1) : C.M % 16 ≠ 9                -- NO hypothesis
theorem T8_mod16 (C : Cycle 1) : C.M % 16 = 1 ∨ C.M % 16 = 5 ∨ C.M % 16 = 13
theorem T3_T8 (C : Cycle 1) (hMq : 1 < C.M) :
    C.M % 48 = 5 ∨ C.M % 48 = 17 ∨ C.M % 48 = 29
```

Bonus (T6/T7 were reachable and are proved):

```lean
theorem closed_form (k : Nat) : 3 ^ k * C.y k + C.cc k = 2 ^ C.BB k * C.M
theorem T6 (k : Nat) : 2 ^ C.BB k * C.M ≤ 3 ^ k * C.M + C.cc k
theorem T6_iff (k : Nat) :
    2 ^ C.BB k * C.M ≤ 3 ^ k * C.M + C.cc k ↔ C.y k ≤ C.M   -- GROUND_TRUTH's ⟺
theorem T7_eq : 3 ^ C.L * C.M + C.cc C.L = 2 ^ C.BB C.L * C.M
theorem T7 : 3 ^ C.L < 2 ^ C.BB C.L
```

### Soundness bridge — `Collatz/Bridge.lean`

The encoding is no longer merely postulated. `ofOrbit` builds a `Cycle q` from
hypotheses that mention **only** the forward map `S_q` — the textbook
definition of "`n` is the largest element of an `S_q`-cycle of length `L`":

```lean
def iter (q : Nat) : Nat → Nat → Nat        -- k-th forward S_q-iterate

def Cycle.ofOrbit (q n L : Nat)
    (hL : 0 < L) (hqp : 0 < q) (hqo : q % 2 = 1) (hq3 : q % 3 ≠ 0)
    (hn : n % 2 = 1)
    (hcyc : iter q L n = n)                          -- n is periodic
    (hle  : ∀ k, k < L → iter q k n ≤ n)             -- n is the maximum
    (hne  : ∀ k, 0 < k → k < L → iter q k n ≠ n) :   -- L is the least period
    Cycle q

theorem Cycle.ofOrbit_M … : (ofOrbit q n L …).M = n
theorem Cycle.ofOrbit_L … : (ofOrbit q n L …).L = L
```

So **real cycle ⇒ `Cycle q` ⇒ T0…T8** is machine-checked end to end: every
theorem above is a theorem about every genuine cycle. The trick that keeps it
short is that stepping backwards once = stepping forwards `L-1` times, so
`y k := iter q ((L-1) * k) n` needs no modular arithmetic.

Conversely, the structure cannot be degenerate:

```lean
theorem Cycle.shift_zero : ∀ j d, C.y j = C.y (j + d) → C.y 0 = C.y d
theorem Cycle.y_ne_of_lt (hj : j < k) (hk : k < C.L) : C.y j ≠ C.y k
```

`y_ne_of_lt` says `y 0, …, y (L-1)` are **pairwise distinct**, so a `Cycle q`
really carries `L` distinct odd numbers on one closed orbit — it cannot be a
shorter orbit padded out to length `L`.

Infrastructure, also proved: `M_odd`, `M_pos`, `y_pos`, `step_mul`, `S_eq`,
`S_le_M`, `S_M_le_M`, `S_S_le_M`, `M_ge_three_of_L`, `bb_spec`, `bb_pos`,
`cc_pos`, and in `Odd.lean` `oddPart_of_odd/_of_even`, `v2_of_odd/_of_even`,
`oddPart_two_mul`, `oddPart_mod_two`, `oddPart_pos`, `three_mul_add_even`,
`S_odd`, `S_pos`; in `Core.lean` `two_pow_le`, `two_pow_split`, `two_pow_shift`.

**The task's four priorities, mapped:**

1. definitions — `v2`, `oddPart`, `S`, all total, all compiling ✅
2. cycle-free lemmas — `lt_S_of_three_mod_four`, `no_odd_pred_of_three_dvd`,
   `pred_le_iff_q1` + `pred_le_unique_q1` + `pred_le_eq_q1` ✅
3. `M ≡ 5 (mod 12)` for a `q = 1` cycle with `≥ 2` odd elements —
   `Cycle.T3_of_L` ✅
4. T5 (`b₂ ≤ 2`) — `Cycle.T5`, `Cycle.T5_bb`, and the sharp general-`q`
   `Cycle.T5_gen` ✅

---

## NOT PROVED — see `Collatz/Unproved.lean` for details

* **T4's recursion to higher powers of 3** (mod 108, mod 324, …). Only the base
  level `T4_base` (mod 36) is formalized. Read as a *uniform* forced-chain
  recursion the claim is **false** from depth 4 on, so there is nothing uniform
  to formalize; each level needs its own size threshold and a 3-adic induction.
* **T6's threshold form** `M ≥ 2^68 → B_k ≤ ⌊k log₂3⌋`. The exact inequality
  `T6` is proved; the threshold implication is not, and needs external input.
  The *unconditional* version is false — `cycle5` (q = 5, M = 49) has `B₃ = 5 > 4`.
* **T6's surviving-prefix counts** (1, 2, 3, 7, 12, …) — a computation, not a
  theorem; keep it in Python.
* **T7's quantitative / Diophantine part** — needs rationals and Baker-type
  input; out of reach here.
* **The 2-adic sieve beyond T8** (`M ≢ 97, 125 mod 128`, the limiting density
  0.2863…). Individual kills are three-line computations like T8; the general
  statement is an induction over forward exponent vectors.
* **That any nontrivial `q = 1` cycle exists.** That is the open problem, and it
  is what caveat 2 below is about.

*(Previously listed here: "soundness of the encoding". That is now proved —
`Cycle.ofOrbit`. A `List`-based front end would be sugar over it.)*

---

## Caveats a reviewer must check

1. **`hmax` is an assumption, not a computed maximum.** Deliberate: it avoids
   needing `Finset.max` without Mathlib. `Cycle.ofOrbit` discharges it from
   `∀ k < L, iter q k n ≤ n`, which *is* checkable for a concrete cycle.

2. **⚠️ The `q = 1` statements with `M > 1` have no witness, and are vacuously
   true if the Collatz cycle conjecture holds.** This is the single most
   important thing to understand about this development. `Cycle 1` is inhabited
   only by the fixed point `{1}` (`one`, `trivialCycle`), which fails `M > 1`.
   So these theorems —

   > `T2_q1`, `T3`, `T3_of_L`, `T4_base`, `T4_base_of_L`, `T5`, `T5'`,
   > `T5_of_L`, `T5_bb`, `T3_T8`

   — are **conditional statements about a hypothetical counterexample**. That is
   exactly what a constraint on a hypothetical cycle *is*, and it is not a
   defect; but it does mean they are not evidence that the machinery works.

   That evidential load is carried by the **general-`q`** theorems, which do
   have witnesses: `T1`, `T1_mod4`, `T2`, `T2_mod3`, `T2_bb`, `T2_unique`,
   `T3_gen`, `T4_mod9`, `T4_base_gen`, `T5_gen`, `T5_bb_gen`, `T0`, `T6`,
   `T6_iff`, `T7`, `closed_form` — all instantiated in `Collatz/Guards.lean` on
   `three5 : Cycle 5` (`{49,31,19}`, `L = 3`, `M = 49 > q`) and
   `two7 : Cycle 7` (`{11,5}`), both built through the soundness bridge.
   `T8` also has a witness (`one`), since it needs no size hypothesis.

3. **The `Cycle` fields were checked against reality outside Lean too.** All 873
   genuine `S_q`-cycles for odd `q ≤ 397` with `3 ∤ q` were enumerated in Python
   and every one satisfies all eleven fields — 0 violations. Together with
   `ofOrbit` (the same fact, proved) and `y_ne_of_lt` (no degenerate models),
   the encoding is pinned from both sides.

---

## Corrections to `docs/GROUND_TRUTH.md` that this formalization forces

* **T1 does not need `M > q`.** `Cycle.T1` is proved with no size hypothesis at
  all: `3M + q = 2m` with `q > 0` already gives `m > M`. The doc's two cited
  counterexamples are counterexamples to **T2**, not T1 — both satisfy T1's
  conclusion (`3·5+17 = 32`, `v₂ = 5 ≥ 2`; `3·11+23 = 56`, `v₂ = 3 ≥ 2`).
* **T2's `L ≥ 2` is redundant given `M > q`**, and T2's *uniqueness* half needs
  no relation between `M` and `q` at all (`Cycle.T2_unique`, from Lemma U).
* **T5 does not need `L ≥ 3`.** The right hypothesis is the size condition
  `M > 11q/7` (`T5_core_sharp`), which is sharp: `7M = 11q` admits `b₂ = 3`, and
  that is exactly what happens in the doc's `q = 7, M = 11` example — the exact
  inequality holds there with *equality* (`77 ≤ 77`), a size coincidence, not a
  wrap artifact. For `q = 1` the threshold is `11/7 < 2`, so `M ≥ 2` suffices.
* **T4's "recurses to higher powers of 3" is not a uniform statement** and must
  not be formalized as one; see `Collatz/Unproved.lean` §1.

* **T6 is stated in the doc as an `⟺`;** only `→` was formalized. `T6_iff` now
  proves the equivalence, so nothing is lost.

New here relative to the doc: **T8**, `M ≢ 9 (mod 16)` for `q = 1`, with no size
hypothesis, and its consequence `M ≡ 5, 17, 29 (mod 48)`; and the general-`q`
forms **T3_gen** (`M ≡ 5q mod 12`) and **T4_base_gen** (`M ≢ 5q mod 36`), which
specialise to the doc's T3 and T4 at `q = 1` and — unlike them — have witnesses.

---

## Novelty: none is claimed

T0, T1, T2, T6 and T7 are standard in the Collatz cycle literature — T0 is the
defining property of the Syracuse map (Kaneda 2015; Tao 2020/2022; Brox 2000);
T1 is Brox's "descending" condition and the local-max half of the Simons–de
Weger / Hercher `m`-cycle decomposition; T2 is that literature's standard
local-maximum analysis; T6's floor/ceiling exponent-vector device is
Eliahou/Kaneda; T7's cycle equation is Böhm–Sontacchi 1978 with Crandall 1978
for the Diophantine consequence. T3, T4, T5 and T8 are one-line corollaries of
that folklore that I did not find written verbatim — the weakest possible form
of novelty, and not to be presented as results.

What this directory contributes is **machine-checked certainty** and a small
reusable `Cycle` API, nothing more. Nothing here comes close to the state of the
art (no `m`-cycles with `m ≤ 91`, Hercher 2023; minimum element `> 2.36×10²¹`,
Barina 2025).

### On the user's seed intuitions

* *"7 can't be the largest, because `3·7+1 = 22 → 11 > 7`"* — **correct**, and it
  is exactly `lt_S_of_three_mod_four` / T1: `7 ≡ 3 (mod 4)`.
* *"to reach 11 you need a bigger odd"* — **the reason is wrong**: `S 1 7 = 11`
  with `7 < 11`, so 11 *is* reached from below (`Examples.lean` proves
  `S 1 7 = 11`). But 11 **is** excluded, by T1, because `11 ≡ 3 (mod 4)`.
* *"we need only look two even hops back"* — **correct for `q = 1`, `M ≥ 2`**
  (`Cycle.T5`), but the justification is a size inequality, not a cycle-length
  argument; the general threshold is `M > 11q/7`.

---

## `Collatz/Length.lean` — a cycle-length lower bound

The published cycle-length bounds (Steiner 1977, Simons–de Weger 2005, Hercher
2023) all route through **Baker's theorem** on linear forms in logarithms, which
bounds how close `2^B / 3^L` can get to 1. Lean 4 core has no real numbers, let
alone Baker. So the Baker input is taken as an explicit **hypothesis**, stated
in ℕ, and everything downstream of it is proved:

```
hbaker :  3^L * L^κ + c * 3^L  ≤  2^B * L^κ         -- i.e. 2^B/3^L ≥ 1 + c/L^κ
   ⟹     3 * m * c  ≤  2 * q * L^(κ+1)              -- `Cycle.length_bound`
```

with `m` the cycle minimum. Contrapositively: if every `n < m` is known to reach
the fixed point, any cycle satisfies `L^(κ+1) ≥ 3mc/(2q)`.

**No analysis is needed.** The usual derivation takes logarithms of
`2^B = ∏ (3 + 1/x_j)`. Here the same content is carried by two elementary facts:

| | |
|---|---|
| `Cycle.prodG_eq` | the exact integer identity `∏ (3x_j + q) = 2^B · ∏ x_j` |
| `pow_succ_le` | `(N+q)^L · N ≤ N^L · (N + 2Lq)` when `2Lq ≤ N` — the ℕ stand-in for `(1+q/N)^L ≤ 1 + 2Lq/N` |

Both are plain inductions. Together they give `Cycle.squeeze`:
`3m · 2^B ≤ 3^L · (3m + 2Lq)`.

### Non-vacuity

The hypotheses are satisfiable by a cycle that **actually exists**.
`cycle5 : Cycle 5` is `{49, 31, 19}`, with `L = 3`, `B = 5`, minimum `19`. Its
Baker input holds at `κ = 3, c = 5` — and holds *with equality*:

```
3^3 · 3^3 + 5 · 3^3  =  729 + 135  =  864  =  32 · 27  =  2^B · L^κ
```

so `c = 5` is exactly sharp there. `cycle5_length_bound` then reads
`3·19·5 ≤ 2·5·3^4`, i.e. `285 ≤ 810` — a true statement about a real cycle, not
a hypothetical one.

### What this is not

The bound is **weaker than the published ones**, which use genuine effective
irrationality measures for `log₂3` (Rhin and successors). Instantiating
`length_bound` with a published `(κ, c)` would give a real numeric bound, but
this repo does **not** verify any such constant — that is exactly the part left
as a hypothesis. The value here is that everything *after* the Baker input is
machine-checked and choice-free.

NOVELTY: none. This is the classical Crandall-style squeeze, rearranged to avoid ℝ.

