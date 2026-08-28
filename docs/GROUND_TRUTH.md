# Ground truth — the audited spec

*Final state, 2026-08-26, after an independent claim audit, a Lean 4
formalization pass, and an adversarial re-verification of the Python package.*

This file is the **shared specification**: the `python/`, `lean/` and `web/`
tracks all state their claims in this notation. It supersedes every earlier
version of this document. Earlier versions carried one outright false claim and
five wrong or misleading hypothesis statements; all six are recorded in
[§6](#6-refuted-claims-kept-as-warnings) rather than deleted, because each was
believed on the strength of numerics that did not actually test it.

**Nothing in this document is new mathematics.** See [§8](#8-prior-art).

---

## 1. Notation

The **Syracuse map** on odd numbers for the `3n+q` system, with `q` odd,
`3 ∤ q`, **`q > 0`**:

    S_q(n) = (3n + q) / 2^b,   b = v2(3n + q) ≥ 1,   n odd

`q > 0` is a genuine hypothesis, not decoration: every claim below uses it
(T1 via `2^b ≥ 3 + q/M > 3`, T5/T6 via `c_k > 0`, T7 via `c_L > 0`, the 2-adic
sieve via `d_j > 0`), and for `q < 0` the map does not even keep positive odds
positive (`S₋₇(1) = −1`).

A **cycle** is a closed orbit of odd numbers under `S_q`. For a cycle:

| symbol | meaning |
|---|---|
| `L` | number of odd elements |
| `M` | largest odd element |
| `B` | total halvings around the cycle |

Classical Collatz is `q = 1`.

**Backward** from `M`, the odd predecessors are `y_0 = M, y_1, y_2, …` with

    3·y_j + q = 2^{b_j} · y_{j−1},        B_k = b_1 + ⋯ + b_k
    y_k = (2^{B_k}·M − c_k)/3^k,          c_k = 2^{b_k}·c_{k−1} + 3^{k−1}·q,  c_0 = 0

**Forward** from `M`, the odd images are `x_0 = M, x_1, x_2, …` with

    2^{a_j}·x_j = 3·x_{j−1} + q,          A_j = a_1 + ⋯ + a_j
    2^{A_j}·x_j = 3^j·M + d_j,            d_j > 0

The two directions are mirror images: backward is governed by `⌊k·log₂3⌋`,
forward by `⌈j·log₂3⌉`.

---

## 2. Status legend

| mark | meaning |
|---|---|
| **P** | proved (proof recorded here or in `lean/`) |
| **L** | machine-checked in `lean/`, zero `sorry`, zero extra axioms |
| **E** | verified against the 2127-cycle census (`q ≤ 999` odd `3∤q`, all cycles with `M ≤ 20000`), reproducible via `cd python && uv run pytest` |
| **✗** | refuted — kept as a warning, never deleted |

Census composition: 2127 cycles, of which 1681 have `L ≥ 2`, 446 are fixed
points, 1482 have `M > q`, 312 have `M < q`, 333 have `M = q`, 1349 have
`M > 11q/7`, and 47 have `7M = 11q` exactly.

---

## 3. The claims

### T0 — cycles avoid multiples of 3
> Let `q` be odd with `3 ∤ q`. If `p` is odd and `3 ∣ p` then `p` has no odd
> `S_q`-predecessor; consequently `p` lies on no `S_q`-cycle. Equivalently:
> **every element of every `S_q`-cycle is coprime to 3.**

*Hypotheses:* none beyond `q` odd, `3 ∤ q`.
*Proof.* If `y` is odd and `S_q(y) = p` then `3y + q = 2^b·p`. Mod 3 the left
side is `q` and the right side is `0`, so `3 ∣ q` — contradiction. Every cycle
element has a predecessor inside the cycle. ∎
**P · L (`Cycle.T0`) · E 2127/2127**

### T1 — the maximum must fall by at least two halvings
> If `M` is the maximum of an `S_q`-cycle then `v2(3M+q) ≥ 2`, i.e. `4 ∣ 3M+q`.
> Equivalently **`M ≡ q (mod 4)`**. For `q = 1`: **`M ≡ 1 (mod 4)`**.

*Hypotheses:* **none.** In particular **not** `M > q`.
*Proof.* `S_q(M) = (3M+q)/2^b ≤ M` gives `2^b ≥ 3 + q/M > 3`, so `2^b ≥ 4`.
Then `3M ≡ −q (mod 4)` and `3⁻¹ ≡ 3 (mod 4)` give `M ≡ −3q ≡ q (mod 4)`. ∎
**P · L (`Cycle.T1`, `T1_mod4`, `T1_q1`) · E 2127/2127**

### T1′ — the refinement in the other direction
> `M < q ⇒ v2(3M+q) ≥ 3` (i.e. `8 ∣ 3M+q`). `M = q ⇒ v2(3M+q) = 2` exactly.

*Proof.* `2^b ≥ 3 + q/M`; if `M < q` this exceeds 4. If `M = q` then
`3M+q = 4q` with `q` odd. ∎
Note the direction: `M < q` gives a **strictly stronger** conclusion than
`M > q`. An earlier version of this document had this backwards.
**P · not formalized · E 312/312 and 333/333**

### U — the predecessor lemma
> Fix `q` odd, `3 ∤ q`, `q > 0`, and let `p > 0` be odd.
> (a) If `3 ∣ p`, `p` has no odd predecessor.
> (b) Otherwise the odd predecessors of `p` are exactly `y_b = (2^b·p − q)/3`
> for `b ≥ 1` with `b ≡ β_p (mod 2)` and `2^b·p > q`, where `β_p = 1` if
> `p ≡ −q (mod 3)` and `β_p = 0` if `p ≡ q (mod 3)`. Each such `y_b` is
> automatically odd, and `y_b` is strictly increasing in `b`.
> (c) `#{odd predecessors y ≤ X} = #{b ≥ 1 : b ≡ β_p (mod 2), q/p < 2^b ≤ (3X+q)/p} ≈ ½·log₂(3X/p)`.
> (d) **Taking `X = p`: every odd `p` coprime to 3 has *at most one* odd
> predecessor strictly below itself, for every `q`.** If `p ≥ q` it has exactly
> one when `p ≡ −q (mod 3)`, namely `(2p−q)/3` with `b = 1`, and none when
> `p ≡ q (mod 3)`.

*Proof of (d).* The admissible window is `q/p < 2^b < 3 + q/p`, an interval of
additive length 3. Two powers of two of the same parity differ by
`2^{b+2} − 2^b = 3·2^b ≥ 6 > 3` for `b ≥ 1`, so at most one admissible `b` of
the required parity exists. (Two of opposite parity coexist only for `b = 1, 2`,
i.e. `q/2 < p ≤ q`, and the parity rule then picks one.) ∎
*This is the clean lemma behind T2. Uniqueness needs no relation between `p` and
`q`.*
**P · L (`pred_unique`, `Cycle.T2_unique`) · E: 499 500 `(q,p)` pairs, 0
exceptions; 1681/1681 cycles with `L ≥ 2` have exactly one predecessor below `M`**

### FP — fixed points are small
> `L = 1 ⇒ M ≤ q`. Hence **`M > q` already forces `L ≥ 2`**, and the `L ≥ 2`
> hypothesis attached to T2/T3/T4 in earlier drafts is redundant.

*Proof.* `n` is a fixed point iff `3n + q = 2^b·n`, i.e. `n(2^b − 3) = q` with
`b ≥ 2` (b=1 impossible by T1's computation). So `n = q/(2^b − 3) ≤ q`. ∎
**P · L for `q=1` (`Cycle.M_ge_three_of_L`) · E 446/446**

### T2 — the step into the maximum is a single halving
> If `M` is the maximum of an `S_q`-cycle and **`M > q`** then `b_1 = 1`
> exactly: `M`'s unique in-cycle odd predecessor is `y_1 = (2M − q)/3`. This
> forces `3 ∣ 2M − q`, i.e. **`M ≡ 2q (mod 3)`**; for `q = 1`, `M ≡ 2 (mod 3)`.

*Hypotheses:* `M > q`, **strict**. Not `M ≥ q`, and no length hypothesis.
*Proof.* Predecessors are `y_b = (2^b M − q)/3`. `y_b < M ⟺ M(2^b − 3) < q`. For
`b ≥ 2` this gives `M ≤ M(2^b − 3) < q`. So `M ≥ q ⇒ b_1 = 1`. Then
`2M = 3y_1 + q` gives `M ≡ 2q (mod 3)` since `2⁻¹ ≡ 2 (mod 3)`. ∎
*Why strict:* at `M = q` the cycle is the fixed point `3q + q = 4q`, where
`b_1 = 2` and `2M − q = q` is never divisible by 3 — **both** halves of T2 fail.
Under `M ≥ q` the census gives 1482/1815.
*Converse is FALSE:* `b_1 = 1` does **not** imply `M > q` (e.g. `q=11`, cycle
`7 → 1 → 7`, `M = 7 < 11`).
*Tightness:* `q=17` cycle `{5,1}` has `M = 5 < q` and `b_1 = 2`; `q=23` cycle
`{11,7}` has `M = 11 < q` and `b_1 = 2`.
**P · L (`Cycle.T2`, `T2_mod3`, `T2_bb`, `T2_q1`) · E 1482/1482**

### T3 — the mod-12 class
> `M > q ⇒` **`M ≡ 5q (mod 12)`**. For `q = 1`: **`M ≡ 5 (mod 12)`**.

*Proof.* CRT on `M ≡ q (mod 4)` (T1) and `M ≡ 2q (mod 3)` (T2). ∎
**P · L (`Cycle.T3_gen`, `T3`, `T3_of_L`) · E 1482/1482**

### T4 — one 3-adic level deeper
> `M > q ⇒` **`M ≢ 5q (mod 9)`**. Combined with T3 this is exactly
> **`M ≡ 17q or 29q (mod 36)`**. For `q = 1`: `M ≡ 17 or 29 (mod 36)`.

*Proof.* By T2, `y_1 = (2M−q)/3` is on the cycle, so by T0, `3 ∤ y_1`. Now
`3 ∣ y_1 ⟺ 9 ∣ 2M − q ⟺ M ≡ 5q (mod 9)` (since `2·5 ≡ 1 mod 9`). The three
classes mod 36 that are `≡ 5q (mod 12)` are `5q, 17q, 29q`; their residues mod 9
are `5q, 8q, 2q`, pairwise distinct, so exactly `5q` is removed. ∎
*Hypothesis is tight:* cycles **do** satisfy `M ≡ 5q (mod 9)` — e.g. `q=119`,
`M=19`, `L=2`; `q=355`, `M=47`, `L=3`; `q=833`, `M=133` — and every one has
`M < q` or `L = 1`.
**P · L (`Cycle.T4_mod9`, `T4_base_gen`, `T4_base`, `T4_base_of_L`) · E 1482/1482**

### T5 — "only two even hops back", corrected
> If `M` is the maximum of an `S_q`-cycle and **`M > 11q/7`** then `b_2 ≤ 2`.
> Exact form: `M(2^{1+b_2} − 9) ≤ (2^{b_2} + 3)·q`.
> For `q = 1` the threshold is `11/7 < 2`, so `M ≥ 2` suffices.

*Hypotheses:* the **size** condition `M > 11q/7`. Not `L ≥ 3` — see
[§6](#6-refuted-claims-kept-as-warnings). No length hypothesis is needed at all,
since `M > 11q/7 > q` gives `L ≥ 2` by FP.
*Proof.* `y_2 = (2^{1+b_2}M − (2^{b_2}+3)q)/9` is a cycle element so `y_2 ≤ M`,
giving the exact inequality. For `b_2 ≥ 3` the coefficient `2^{1+b_2} − 9 > 0`,
so `M ≤ (2^{b_2}+3)q/(2^{1+b_2}−9) ∈ {11/7, 19/23, 35/55, …}·q`, maximised at
`b_2 = 3`. ∎
*Sharp:* `7M = 11q` admits `b_2 = 3`. 47 census cycles have `7M = 11q` exactly
and **all** of them have `b_2 = 3` — starting with `q=7, M=11`.
**P · L (`Cycle.T5_gen`, `T5_bb_gen`, `T5`, `T5'`, `T5_of_L`, `T5_bb`) ·
E 1349/1349**

### T6 — the backward prefix inequality
> **`y_k ≤ M ⟺ M(2^{B_k} − 3^k) ≤ c_k`.**

*Hypotheses:* none. It is an equivalence, both directions.
*Consequence (conditional):* for large `M` this forces `B_k ≤ ⌊k·log₂3⌋`.
The threshold is **not** `2^68`: the exact crossover `floor_rule_threshold(k)`
is `1, 1, 9, 7, 86, 23, 22, 82, 62, 381` for `k = 1..10` and
`175, 173, 538, 450, 2012, 1219, 17344, 3536, 3219` for `k = 11..19`, so
`M > 17344` suffices for all `k ≤ 19`. The sequence is not monotone; nothing is
claimed past `k = 19`. The `k = 2` value `1` (i.e. `M ≥ 2`) is an independent
cross-check of T5.
*Surviving backward-prefix counts* `N(k)`, `k = 1..15`:
`1, 2, 3, 7, 12, 30, 85, 173, 476, 961, 2652, 8045, 17637, 51033, 108950`
(against `8^k` unconstrained). Growth rate
`λ = α^α/(α−1)^(α−1) = 2.8395137305` with `α = log₂3`, empirically
`N(k) ≈ 1.235·λ^k·k^(−1.51)`.
**P · L (`Cycle.T6`, `T6_iff`, `closed_form`) · E 2127/2127; `N(k)` pinned to
fixtures**

### T7 — the cycle equation
> **`M(2^B − 3^L) = c_L > 0`**, hence `2^B > 3^L` and `B/L > log₂3`. Closing a
> cycle needs `2^B/3^L` within about `1/M` of 1 — a Diophantine condition.

**P (equation and `2^B > 3^L`) · L (`Cycle.T7_eq`, `T7`) · E 2127/2127.**
The Diophantine half is **not formalized** and not proved here; it is where
Baker's theorem enters the literature.
Elementary Crandall squeeze, as computed in `python/collatz_maxodd/cycleeq.py`:
a minimum element above Barina's verified `2075·2^60 = 2.39×10²¹` forces
`L ≥ 72 057 431 991` (`B = 114 208 327 604`). The published bound is
**stronger**: Hercher (2023) gets `K > 1.375×10¹¹` odd elements and `m ≥ 92`
circuits using Baker's theorem.

### T8 — the mod-16 refinement (`q = 1`)
> **`M ≢ 9 (mod 16)`**, hence `M ≡ 1, 5, 13 (mod 16)`, and with T3
> `M ≡ 5, 17, 29 (mod 48)`.

*Hypotheses:* none for the mod-16 half (the mod-48 half inherits T3's `M > 1`).
*Proof.* `M = 16s+9 ⇒ 3M+1 = 4(12s+7)`, so `v2 = 2` exactly and `x_1 = 12s+7`.
Then `3x_1+1 = 2(18s+11)`, so `v2 = 1` exactly and `x_2 = 18s+11 > 16s+9 = M`
for every `s ≥ 0`. Contradicts maximality. ∎
**P · L (`Cycle.T8`, `T8_mod16`, `T3_T8`) · E: real orbits from the smallest
member of each dead class, so the kill is verified unconditional, not just for
large `M`**

### D2, D3 — the two further forced levels
> **D2.** `M > 11q/7 ⇒ M ≡ 17q, 29q, 53q, 101q (mod 108)`.
> For `q = 1`: `M ≡ 17, 29, 53, 101 (mod 108)`.
> **D3.** `M > 49q/5 ⇒ M ≡ 101q, 125q, 161q, 233q, 269q, 317q (mod 324)`.
> For `q = 1`: density `1/27` of the odd numbers.

*Proof sketch.* By T5, `b_2 ≤ 2`; by Lemma U the parity of `b_2` is forced, so
`b_2 ∈ {1,2}` is uniquely determined and `y_2` is a determined function of `M`;
T0 (`3 ∤ y_2`) is then a congruence mod 27, and with `M ≡ q (mod 4)` a condition
mod 108. D3 repeats this with `y_3 ≤ M`, which excludes `b_3 ≥ 3` when `b_2 = 1`
once `M > 49q/5`, and `b_3 ≥ 2` when `b_2 = 2` once `M > 37q/5`. ∎
*Thresholds essentially sharp:* an exhaustive sieve scan over `q ≤ 899` found
violators with `M/q` up to `1373/877 = 1.5656 < 11/7` and
`8573/877 = 9.7754 < 49/5`, none above.
**P (on paper) · not formalized · E: exhaustive sieve over all odd `M ≤ 2·10⁶`
at `q = 1`; 1931/1931 and 931/931 real cycles in the audit's separate
2868-cycle dataset**

---

## 4. The sieve, and where it stops

### 4a. The 3-adic (backward) sieve
T0 **alone** saturates immediately: without the size bound the survivor set is
`M ≡ 2, 8 (mod 9)` at every depth, density `2/9` forever. **All** further 3-adic
gain comes from T6, not from T0. With T6:

| k | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 10 | 15 | 20 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| survivors mod `3^{k+1}` | 2 | 4 | 6 | 13 | 22 | 50 | 123 | 254 | 1302 | 113034 | 10995110 |
| density | .2222 | .1481 | .0741 | .0535 | .0302 | .0229 | .0187 | .0129 | .00735 | .00263 | .00105 |

Density falls by an empirical factor ≈ 0.82 per step over `k = 12..20`; the
asymptotic floor from `N(k)` is `(λ/3)^k = 0.9465^k·k^(−1.51)`. The collision
term is still decreasing at `k = 20` and its asymptotics were not determined —
**no claim is made** that the density decays at rate `0.82^k`.

Exact survivor sets, `M mod 3^{k+1}`:

```python
SURV3 = {
 1: (9,   [2, 8]),
 2: (27,  [2, 17, 20, 26]),
 3: (81,  [20, 26, 44, 71, 74, 80]),
 4: (243, [20, 80, 107, 125, 152, 155, 161, 182, 188, 206, 233, 236, 242]),
}
```
`SURV3[1]` ⊗ (`M ≡ 1 mod 4`) = `M ≡ 17, 29 (mod 36)` = T4. ✓

### 4b. The 2-adic (forward) sieve — **unconditional, and it saturates**
Kills occur only at `a ∈ {2, 4, 7, 10, 12, 15, 18, 20, 23, …} ⊂ {⌊j·log₂3⌋+1}`:
`a=2` kills `{3}` (this **is** T1), `a=4` kills `{9}` (this **is** T8), `a=7`
kills `{97, 125}`, `a=10` kills 7 classes, and so on.

```python
SURV2 = {
 2: (4,  [1]),
 3: (8,  [1, 5]),
 4: (16, [1, 5, 13]),
 5: (32, [1, 5, 13, 17, 21, 29]),
}
```

Unlike the 3-adic sieve this half needs **no** largeness hypothesis: the kill
condition is `2^{A_j} < 3^j`, and `2^{A_j}·x_j = 3^j·M + d_j` with `d_j > 0`
gives `x_j > M` outright. A class killed here contains no cycle maximum of any
size.

**But it saturates.** Limiting density `0.2863153965` of the odd numbers (DP to
depth 600, converged to 12 digits; confirmed at `0.286555` over 400 000 real odd
`M` near `2^24`). That is **1.80 bits, forever**. No depth helps.

### 4c. Combined (CRT; the moduli are coprime)

| k | a | modulus bits | joint density among odd `M` | bits removed |
|---|---|---|---|---|
| 1 | 2 | 5.2 | 0.1111111111 | 3.17 |
| 4 | 6 | 13.9 | 0.0200617284 | 5.64 |
| 8 | 12 | 26.3 | 0.0040704741 | 7.94 |
| 12 | 18 | 38.6 | 0.0016092362 | 9.28 |
| 16 | 24 | 50.9 | 0.0006591907 | 10.57 |
| 20 | 30 | 63.3 | 0.0003009525 | 11.70 |

Best computed: ~1 odd number in 3300 survives, at modulus ≈ `2^63`. Marginal
efficiency ≈ 0.28 bits of sieve per bit of modulus, and falling.

**Caveat on record.** The CRT product is exact as a statement about *residue
classes surviving two independently-defined sieves*. It is a joint statement
about an actual cycle only when `L ≥ k + j + 1`, so that the `k` backward and
`j` forward elements from `M` are disjoint. Harmless for hypothetical large
cycles; not proved for short ones.

---

## 5. Independent verification performed

Two checks run against **real integers**, with no residue arithmetic:

1. **Backward.** Honest DFS on 200 000 odd `M` near `2^41` using only the exact
   tests `y_j ≤ M`, `3 ∤ y_j`, integrality — and **not** assuming `b_1 = 1`.
   Observed residue sets mod `3^{k+1}` for `k = 1..7` are *set-equal* to the
   predicted ones. This re-derives T2 as an output rather than an input.
2. **Forward.** 400 000 odd `M` near `2^24`, full forward orbit. Observed
   density 0.286555 vs. the DP limit 0.2863153965; observed mod-`2^a` residue
   sets ⊆ predicted, sizes identical, for `a = 2..14`.

Plus: 240 Python tests over the 2127-cycle census; 1623 real `S_q` cycles
(`q < 700`) re-derived independently during the Lean pass with 0 violations;
`lean/check.sh` verified to *fail* on four deliberately injected defects,
including a build-passing `sorry`.

---

## 6. Refuted claims, kept as warnings

| ✗ | claim as once stated | status |
|---|---|---|
| ✗1 | `B_k ≤ ⌊k·log₂3⌋` unconditionally | **FALSE.** `c_k` grows like `2^{B_k}`, not `O(1)`. Real counterexample: `q=5`, cycle `(49, 19, 31)`, `B_3 = 5 > 4`. Holds only for large `M` — see T6 for the real threshold. |
| ✗2 | "`M > q` is required for T1" | **FALSE.** T1 needs no size hypothesis. The two cited counterexamples, `q=17 {1,5}` and `q=23 {7,11}`, both *satisfy* T1 (`3·5+17 = 32`, `v2 = 5`; `3·11+23 = 56`, `v2 = 3`). They refute **T2 only**. And `M < q` gives the *stronger* conclusion (T1′). |
| ✗3 | "T5 needs `L ≥ 3`, else `y_2 = M` wraps" | **FALSE.** Counterexample `q = 37`, cycle `53 → 49 → 23 → 53`: `L = 3`, `M = 53 > q = 37`, `y_2 = 49 < M` (no wrap), `b_2 = 3`. 33 such cycles in the census. The correct hypothesis is `M > 11q/7`. The stated reason for the `q=7, M=11, L=2` case is also wrong: there the exact inequality holds with **equality** (`77 ≤ 77`) because `7M = 11q` exactly — a size coincidence at the sharp threshold, not a wrap artifact. |
| ✗4 | T2 under `M ≥ q` | **FALSE at `M = q`**, which is precisely the fixed point `3q+q = 4q`: `b_1 = 2`, and `2M − q = q` is never divisible by 3. Census: 1482/1815 under `M ≥ q`, 1482/1482 under `M > q`. |
| ✗5 | "`L ≥ 2` is required for T2/T3/T4" | **Redundant**, not required: `M > q` already forces `L ≥ 2` (FP). |
| ✗6 | "T4 recurses to higher powers of 3" (as a uniform statement) | **Misleading.** T0 alone saturates at `M ≡ 2, 8 (mod 9)`. Every further gain comes from T6 and needs its own threshold `M > C_k·q` (`C_2 = 11/7`, `C_3 = 49/5`, …), and the recursion is a single **forced chain only for depths 1–3**. From depth 4 it is a branching sieve: the prefix `(b₁,b₂,b₃,b₄) = (1,1,1,3)` has `2^{B₄} = 64 < 81 = 3⁴`, so `y₄ ≤ M` imposes nothing. Assuming a forced chain at depth 4 produced 8 false predictions against real cycles (e.g. `q=13`, `M=797`, `L=5`). |

Empirically the depth-`D` survivor set for `q = 1` is still exactly a congruence
condition on `M` mod `4·3^{D+1}` (2 classes mod 36, 4 mod 108, 6 mod 324, 13 mod
972, 22 mod 2916, …), but only D ≤ 3 is a forced chain, and only D ≤ 1 (T4) is
formalized.

---

## 7. Formalization status (`lean/`)

Lean 4.33.1, **no Mathlib**, `"packages": []`. 302 declarations audited:
238 depend on `[propext, Quot.sound]`, 30 on `[propext]`, 34 on nothing. Zero
`sorry`, zero `axiom`, zero `native_decide`, zero `set_option`.

**Proved:** T0, T1, T1_mod4, T1_q1, T2, T2_mod3, T2_bb, T2_unique, T2_q1,
T3_gen, T3, T3_of_L, T4_mod9, T4_base_gen, T4_base, T4_base_of_L, T5_gen,
T5_bb_gen, T5, T5', T5_of_L, T5_bb, T6, T6_iff, closed_form, T7_eq, T7, T8,
q_dvd_cc, M_mul_sub, q_dvd_sub, burst, q1_burst, aa_1..aa_4,
T8_mod16, T3_T8, plus `pred_unique`, `pred_exists`, `M_ge_three_of_L`,
`y_ne_of_lt`, `shift_zero`, and the soundness bridge `Cycle.ofOrbit`.

**Not formalized** (recorded in `lean/Collatz/Unproved.lean`): T1′; FP in
general `q`; D2/D3 (the mod-108 / mod-324 levels); the T6 largeness threshold
and the prefix counts `N(k)`; the Diophantine half of T7; the 2-adic sieve
beyond T8; the limiting density 0.2863153965.

**The load-bearing caveat.** Every `q = 1` theorem that also assumes `M > 1` is a
conditional statement about a hypothetical counterexample, and is **vacuously
true if the Collatz cycle conjecture holds**. `Cycle 1` is inhabited only by
`{1}`, which fails `M > 1`. That is what such a constraint *is*, not a defect —
but it means those theorems are not evidence the machinery works. That load is
carried by the general-`q` forms (`T3_gen`, `T4_base_gen`, `T5_gen`), which have
real witnesses: `two7 : Cycle 7` (`{11,5}`) and `three5 : Cycle 5`
(`{49,31,19}`, `L=3`, `M > q`).

---

## 8. Prior art

**Novelty: none.** Do not present any claim above as new.

| claim | prior art |
|---|---|
| T0 | Kaneda, *Fibonacci Quart.* 53(2) (2015) 168–174 — states it verbatim for general `d`. Tao, *Forum of Math. Pi* 10 (2022) e12 — the Syracuse map is defined on odds coprime to 3 for this reason. Brox, *Acta Arith.* 92 (2000) 181–188. |
| T1 | Brox 2000's "descending" condition; the local-max decomposition of Simons & de Weger, *Acta Arith.* 117 (2005) 51–70; Terras, *Acta Arith.* 30 (1976) 241–252. |
| U, T2 | Brox 2000 ("descendent" of a local maximum); Kaneda 2015 Thm 2.1 uses the same inverse map. |
| T3, T4, T5, T8, D2, D3 | Not found written verbatim — the weakest possible form of novelty. One-line corollaries of the above. The mod-`3^j` predecessor machinery is Wirsching, *The Dynamical System Generated by the 3n+1 Function*, Springer LNM 1681 (1998). |
| T6 | Kaneda 2015 Thm 2.1 (ineq. 2.3); Eliahou, *Discrete Math.* 118 (1993) 45–56; Halbeisen & Hungerbühler, *Acta Arith.* 78 (1997) 227–239; Simons–de Weger 2005; Hercher, *JIS* 26 (2023) Art. 23.3.5. |
| T7 | **Böhm & Sontacchi**, *Atti Accad. Naz. Lincei* 64 (1978) 260–264 — already Lean-formalised at ccchallenge.org. Crandall, *Math. Comp.* 32 (1978) 1281–1292 for the continued-fraction consequence; Baker, *Mathematika* 15 (1968) 204–216 for the transcendence input. |
| `3n+q` setting | Belaga & Mignotte, *Exp. Math.* 7(2) (1998) 145–151; Belaga, *Acta Arith.* 106.2 (2003) 197–206; Lagarias, *Acta Arith.* 56 (1990) 33–53. |

State of the art, for scale: no nontrivial cycle has `m ≤ 91` circuits (Hercher
2023); `K > 1.375×10¹¹` odd elements; minimum element `> 2075·2^60 ≈ 2.39×10²¹`
(Barina, *J. Supercomputing* 81 (2025) art. 810). Nothing here approaches that.

Two literature gaps could not be closed (searched, found nothing — absence of
evidence only): an explicit published `M ≡ 5 (mod 12)` for the maximum, and an
explicit published mod-`3^j` recursion of the T4 form. Both are trivially
derivable from cited folklore, so the honest framing is "elementary consequences
of standard facts, collected here", not "new".

---

## 6. The sieve *is* the cycle problem  (added after the original audit)

Formalized in `lean/Collatz/Equivalence.lean`; see also `docs/DEATH_DEPTH.md`.

A **backward chain** bounded by `M` is an infinite sequence `M = y₀, y₁, …` of
odd numbers with `S_q(y_{j+1}) = y_j` and every `y_j ≤ M`. Surviving the
backward sieve at depth `k` means such a chain exists out to length `k`.

| direction | statement | Lean |
|---|---|---|
| easy | a cycle is a backward chain bounded by its own maximum | `Cycle.toBackChain` |
| hard | any bounded chain forces a periodic point of `S_q` at or below `M` | `BackChain.exists_periodic` |
| `q=1` | for `M > 1` that periodic point is `≠ 1`, i.e. a genuinely nontrivial cycle | `BackChain.exists_nontrivial_periodic` |

The hard direction is pigeonhole (finitely many odd values `≤ M`, infinitely many
terms) plus the observation that `1` cannot occur in a `q = 1` chain above 1,
since `S₁ 1 = 1` would drag `M` down to 1.

**Consequence.** Proving the sieve kills every `M` at some finite depth is not an
approach to the conjecture — it is logically the same statement. Define
`d(M)` = the largest `k` with a chain of length `k`; a counterexample is exactly
an odd `M > 1` with `d(M) = ∞`.

**NOT formalized** (`Collatz/Unproved.lean` § 4): the step from "chains of every
finite length" to "one infinite chain", i.e. König's lemma. It needs dependent
choice and would put `Classical.choice` into the axiom certificate. So the
machine-checked claim is *infinite bounded chain ⟺ cycle*, not the stronger
*survives every finite depth ⟺ cycle*.

**Non-vacuity.** For `q = 1` the hypothesis is what the conjecture denies, so that
corollary would be vacuous if Collatz is true. The general-`q` theorem is not:
`q7_has_periodic_point` instantiates it on the real cycle `11 → 5 → 11`.

**Quantitatively** (`docs/DEATH_DEPTH.md`): `P(d ≥ k) = a_k / 3^k` exactly, with
`a_k = 1, 2, 3, 6, 10, 22, 50, 104, 254, 538, 1302, 3202, 7553, 19206`; `d(M)`
depends only on `M mod 3^k`; the tail rate is conjectured — not shown — to
approach `λ/3 ≈ 0.9465`.

---

## 7. Later work, and what is machine-checked  (added after §6)

The project kept going after the sections above were written. This records what
was added and — more importantly — **which of it is verified how**, because the
newest results were for a while the least checked.

### Certification (`docs/CERTIFY.md`)

Three *complete* tests that a given `M` is not a cycle maximum, in increasing
order of cleverness and decreasing order of cost (200 000 odd `M` from `10⁷`):

| test | work | complete because |
|---|---|---|
| run the orbit to 1 | 11 424 896 | cycles never reach 1 |
| run until it exceeds `M` | 3 095 678 | then `M` isn't its own orbit's max |
| exhaust the backward tree | 414 293 | equivalence theorem (§6) |

A dead residue class mod `3^k` certifies **infinitely many** `M` at once, for
`M` above a closed-form threshold `T_k` that reproduces the project's own
`running_max` exactly. `T₁₁₈ = 1.87×10²¹ ≤ 2.39×10²¹ < T₁₁₉`, so the threshold
is *not* the binding constraint — `a_k`'s `2.84^k` growth is.

### Both ends (`docs/STRUCTURE.md`)

The minimum is the exact mirror of the maximum **once `m > q`**: one halving out,
`≥ 2` in, `m ≡ 3 (mod 4)` and `≡ 7 or 11 (mod 12)` for `q = 1`. The hypothesis is
load-bearing — 197 of the 474 census cycles with `m ≤ q` break the mirror (the
longest being `q = 541`, whose minimum `m = 25` leaves by three halvings) — and
it is *sufficient, not necessary*: some cycles with `m ≤ q` satisfy it anyway.
It is free at
`q = 1`, where any nontrivial cycle has `m ≥ 3`. See `docs/CERTIFY.md`.
Pairing the two ends gives
`m ≤ qL/(3 ln2 · d) ≤ M` with `d = B − L log₂3`. Three consequences:
`L ≤ |R(O)|`; the ascent needs `≥ 1.71 log₂(O/m)` steps while the descent can be
a single step (17 of 77 census cycles); and `u ≥ 2L − B`, which for `q = 1`
becomes **at least 41.5 % of steps are single halvings**.

### Why none of it finishes (`docs/WHY_NOT.md`)

Periodic points of the backward map are exactly `c_L/(2^B − 3^L)` — the cycle
equation — so a cycle is a periodic point landing on a positive integer. The
all-ones pattern gives `y = −1`, whose base-3 expansion is all 2s — so its class
mod `3^k` ends in a 2 at every depth and survives the sieve forever. Hence `a_k ≥ 1` **provably, with a witness**,
and `−1` is not a natural number. A congruence sieve cannot see sign or
integrality; that is the whole gap.

### Verification status

| result | Python | Lean |
|---|---|---|
| T0–T8, U, FP, T6, T7 (§3) | ✓ | ✓ |
| equivalence theorem (§6) | ✓ | ✓ `Equivalence.lean` |
| cycle-length bound (Baker assumed) | ✓ | ✓ `Length.lean` |
| sandwich, both halves | ✓ | ✓ `pow_le_of_min`, `pow_ge_of_max` |
| `u ≥ 2L − B` | ✓ | ✓ `single_halving_count` |
| the 41.5 % figure itself | ✓ | ✓ `Halving.lean` (nothing assumed) |
| min mirror (`m ≡ 3 mod 4`, needs `m > q`) | ✓ | ✓ `Minimum.lean` |
| that hypothesis cannot be *dropped* | ✓ | ✓ `min_bb_out_needs_its_own_hypothesis` |
| `L ≤ \|R(O)\|` | ✓ | ✓ `Reach.lean` (count `#eval`'d, not kernel-reduced) |
| periodic points / the `−1` witness | ✓ | ✓ `Periodic.lean` (algebra only; existence and `a_k` are not) |
| census: `q ∣ 2^B − 3^L`, the burst, `q=1`'s unique burst | ✓ | ✓ `Census.lean` |
| the death-depth counts `a_k` (`k ≤ 4`) | ✓ | ✓ `Census.lean` |
| over-dispersion, tail rate, box dimension | ✓ | ✗ — infeasible in-kernel, open, unresolved limit |

Lean total: **302 declarations**, all certifying `[propext, Quot.sound]` or
`[propext]` — no `sorry`, no `Classical.choice`, no Mathlib.

### A duplication that was removed

`Length.lean` originally defined its own `sumB`, which was identical to the
`BB` already in `Cycle.lean`. It has been deleted and the file now uses `BB`.

