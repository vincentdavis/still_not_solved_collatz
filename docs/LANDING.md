# The landing form `(s, x)` — the odd step as a table of landings

**Provenance.** Synthesis run of 2026-09-23 on the user's proposal to write
each odd step as a pair and ask which pairs a cycle could be made of, with
the odd numbers that are never reached excluded up front.  Four explorer
angles (bijection, exclusion, height word, literature) produced claims; each
claim was checked by two independent referees against the repository and by
fresh computation, and only the surviving or referee-corrected statements
are recorded here.  Labels follow the house scheme: **PROVED** (complete
proof), **COMPUTED** (exact computation, this project), **CONJECTURE**,
**CITED**.  **No novelty is claimed.**  With a few elementary exceptions,
every statement is a restatement of material already in the repository or in
the literature, and each one says where; the additions are the vocabulary and
the bookkeeping that turns the old lemmas into one table.  The exceptions are
new-to-repo and elementary: the superadditivity upgrade of `docs/WORDS.md`
W2's "checked" to PROVED (H9(i)); the set equality
`S_k = {r(b) mod 3^k : b admissible, |b| ≥ k}` (H9(ii)); the general-`q`
first-source rule with its `2s > q` boundary (E1); the `−91` phase computation
(H9(iii)); and the correction in E2′ that the first `j` forward heights are a
function of `M mod 2^{A_j + 1}`, not `2^{A_j}`.  Witnesses: `python/tests/test_landing.py` (24 tests) and the page
`web/landing.html`.
Everything below is about `3n+1` (`q = 1`); the `3n+q` census of
`python/tests/conftest.py` (2127 cycles, `q ≤ 999`, `M ≤ 20 000`) is used only
as a harness to check that an identity survives on maps that do have cycles.

Setting as everywhere in this repo: `S(n) = (3n+1)/2^{v₂(3n+1)}` on odd `n`;
a cycle has odd members `n₁, …, n_L`, maximum `M`, minimum `m`, `B` halvings.

---

## 0. Objects and the bijection

**Definition (landing).** For odd `n > 0` put `x = v₂(3n+1)` and
`s = (3n+1)/2^x`.  The pair `λ(n) = (s, x)` is the *landing* of `n`: `n` is
the **source**, `s` the **target** (the next odd number, `s = S(n)`), `x` the
**height** (the number of halvings).  The user's two numbers are functions of
it: the ascent `3n+1−n = 2n+1 = (2^{x+1}s + 1)/3` and the descent
`D(n) = (3n+1) − s = s(2^x − 1)`; their difference is the net `s − n`.

**Bijection (PROVED; restatement of `docs/LEDGER.md` §2 "The pairs factor"
and Lemma U(b) of `docs/GROUND_TRUTH.md` §3).**  Let
`Λ = {(s, x) : s odd, 3 ∤ s, x ≥ 1, s ≡ (−1)^x (mod 3)}` (equivalently
`2^x s ≡ 1 (mod 3)`), the *admissible landings*.  Then `λ` is a bijection from
the positive odd integers onto `Λ`, with inverse `σ(s, x) = (2^x s − 1)/3`.

*Proof.* `3n+1 = 2^x s` with `s` odd; reducing mod 3, `2^x s ≡ 1`, so `3 ∤ s`
and, since `2 ≡ −1`, `s ≡ (−1)^x`.  Conversely for `(s, x) ∈ Λ` the number
`2^x s − 1` is odd (`2^x s` is even) and `≡ 0 (mod 3)`, so `n = (2^x s − 1)/3`
is a positive odd integer with `3n+1 = 2^x s`, `s` odd; hence `v₂(3n+1) = x`
and `S(n) = s`. ∎  In table language: rows are the targets
`s` (odd, `3 ∤ s`); a row uses the odd columns when `s ≡ 2 (mod 3)` and the
even columns when `s ≡ 1 (mod 3)`; each odd `n` sits in exactly one cell,
cell `(s, x)` holding the source `σ(s, x)`.  The cells of a row are
`y_{x+2} = 4 y_x + 1` apart (PROVED, one line).

**COMPUTED.**  All 50 000 odd `n < 10⁵` map to 50 000 distinct admissible
landings and return under `σ`; all 399 996 admissible `(s, x)` with
`s ≤ 10⁵`, `x ≤ 24` return under `λ∘σ`; the other parity is never admissible
(`test_landing_map_is_a_bijection_onto_admissible_landings`,
`test_every_admissible_landing_has_exactly_one_source`).  Harness: for the 33
admissible `5 ≤ q ≤ 101` the same maps with `q` in place of 1 (positivity
needs `2^x s > q`) are inverse on odd `n < 20 000`
(`test_landing_bijection_survives_on_the_3nq_harness`).

**Rise and fall (PROVED; `docs/LEDGER.md` §2).**  `s > n` iff `x = 1` (for
`n > 1`); column 1 is exactly the `n ≡ 3 (mod 4)`, every other column is a
fall, and the single cell `(1, 2)` holds `n = 1 = s`.  Column `x` is one
residue class mod `2^{x+1}` of the odd numbers (Terras 1976, CITED via
`docs/GROUND_TRUTH.md` §8, T1 row, and `docs/WORDS.md` §1 prior art).

**Where this is in the repo.**  `docs/LEDGER.md` §2 (`D = s(2^x − 1)`,
`n = (2^x s − q)/3`, "a pair is a landing"); `web/ledger.html` §2;
`python/collatz_maxodd/syracuse.py` module docstring (Lemma U: the inverse
map `(2^b p − q)/3` is Kaneda's `g_d`); `web/surface.html` already calls the
cells "landing pads".  The word "landing" is this site's; no source uses it.

---

## 1. A cycle in landing coordinates, and the cycle equation

**Chaining = closure (PROVED; restatement of `docs/GROUND_TRUTH.md` §1
"Backward/Forward" and T7).**  An `S`-cycle `n₁ → n₂ → … → n_L → n₁` is, in
landing coordinates, the cyclic list `(sᵢ, xᵢ) = λ(nᵢ)`, i.e. `sᵢ = n_{i+1}`,
`xᵢ = v₂(3nᵢ+1)`.  The **chaining condition** is that the source of landing
`i` is the target of landing `i−1`:

    3 s_{i−1} + 1 = 2^{xᵢ} sᵢ      (indices in Z/L).

Conversely any cyclic list of admissible landings satisfying the chaining
condition is an `S`-cycle, or a shorter cycle traversed several times
(`nᵢ := σ(sᵢ, xᵢ)`; chaining says `S(n_{i−1}) = nᵢ`).

**The cycle equation (PROVED; T7, Böhm–Sontacchi 1978, Lean
`Cycle.T7_eq`).**  Walk backwards from the landing whose target is `M`, with
`b_j` the heights read backwards, `B_k = b_1 + … + b_k`,
`c_k = 2^{b_k} c_{k−1} + 3^{k−1}`.  Then `3^k y_k = 2^{B_k} M − c_k` for every
`k`, and at `k = L` (`y_L = M`): `M (2^B − 3^L) = c_L > 0`, hence `2^B > 3^L`.
This is `backtree.c_constant` / `cycleeq.cycle_constant` verbatim; the
landing list is the `Cycle` object's `(elements[i+1], forward_halvings[i])`.

**The trivial cycle (PROVED; `docs/GROUND_TRUTH.md` FP).**  It is the single
landing `(1, 2)`: `3·1+1 = 4 = 2²·1`, chaining `(4−1)/3 = 1`, cycle equation
`1·(4 − 3) = 1 = c_1`.  For `q = 1` it is the unique fixed cell: `n(2^x − 3) = 1`
forces `(n, x) = (1, 2)` (the other integer solution, `(−1, 1)`, is the
negative fixed point).  For general `q` the fixed cells are `s(2^x − 3) = q`.

**Both ledgers, in landing form (PROVED; restatement of `docs/LEDGER.md`
§1–§2 and §6 / `cycleeq.product_identity`).**  Around a cycle,

    Σᵢ sᵢ (2^{xᵢ} − 3)  =  L        (additive:  rises weight −1, falls weight 1, 5, 13, …)
    2^B  =  ∏ᵢ (3 sᵢ + 1)/sᵢ         (multiplicative)

The additive line is `Σ(2nᵢ+1) = Σ D(nᵢ)`, i.e. `E = 4O + 2L`, rewritten
with `nᵢ = (2^{xᵢ}sᵢ − 1)/3`; the multiplicative one is the chaining
condition multiplied around the cycle.  Both are consequences of the multiset
identity `{targets} = {sources}` (closure): the additive ledger is its first
power sum; the multiplicative one, cleared of denominators, is
`∏ᵢ(3nᵢ+1) = ∏ᵢ(3sᵢ+1)`, the `L`-th elementary symmetric function of the
*shifted* multiset `{nᵢ + 1/3}`.  For `L = 2`, given equal sums, the shifted
product identity is equivalent to `n₁n₂ = s₁s₂`, and sum plus product
determine a 2-element multiset, so together they force closure; for `L ≥ 3`
two symmetric functions do not determine an `L`-element multiset in general,
and no landing example of a sum-and-product-balanced non-closed triple is
exhibited here (none exists among odd `n < 400`, COMPUTED below).  **Balance
is not closure** (COMPUTED): among odd `n < 400` there are 83 pairs of cells
with nets summing to zero, none closed, and among odd `n < 120`, 408 zero-sum
triples, none closed (`docs/LEDGER.md` §2, `test_ledger.py`); the rest is
this document's own computation, pinned only by
`test_balance_is_not_closure_in_landing_form`: none of the 83 pairs is
product-balanced, and among odd `n < 400` there are 4 784 zero-sum triples,
none of them product-balanced (shifted or plain) and none closed.

**What "a set of landings that balance" can and cannot mean (PROVED,
trivial; referee correction to a draft).**  A finite set of cells whose
sources and targets coincide *as sets* is exactly a finite `S`-invariant set,
i.e. a disjoint **union** of cycles; it is one cycle iff `S` acts transitively
on it.  Harness: for `q = 7` the union `{7} ∪ {11, 5}` of two census cycles
satisfies the set condition and is not a cycle.  So the user's "a cycle would
need a set of these that balance" is a necessary condition (the additive
ledger), and even the full set condition characterises only unions of cycles.

**COMPUTED (census harness, `test_cycles_chain_in_landing_coordinates_and_satisfy_the_cycle_equation`,
`test_additive_and_multiplicative_ledgers_in_landing_form`,
`test_fixed_cells_are_s_times_2x_minus_3_equals_q`).**  2127/2127 census
cycles: the landing list chains, the closed form holds at every depth
`k ≤ L`, `M(2^B − 3^L) = c_L = cycle_constant`, both ledgers hold exactly
(the multiplicative one over `Q`); the landing into `M` has height 1 in
1482/1482 cycles with `M > q` (T2); for `q < 200` the 89 solutions of
`s(2^x − 3) = q` are exactly the 89 census cycles of length 1.

---

## 2. What reachability excludes

The user's instruction was to exclude the odd numbers that are not reachable.
In landing coordinates the answer is exact and short.

**E0 — the excluded set is the odd multiples of 3, and nothing else, without
a size bound (PROVED; T0 and Lemma U, `docs/GROUND_TRUTH.md` §3; saturation:
`sieve.surviving_residues_mod3_no_size` docstring and §4a).**
(i) A target `s` never has `3 | s` (`2^x s ≡ 1 (mod 3)`), so an odd multiple
of 3 has in-degree 0 under `S`: it has a cell but no row, and lies on no cycle
(T0).  (ii) Every `s` with `3 ∤ s` has infinitely many landings (all `x` of
the admissible parity), and — see the leaf rule — infinitely many whose source
is again coprime to 3, so **backward chains of every length avoiding `3Z`
exist for every such `s`**; the sieve driven by T0 (with T2's `b_1 = 1`)
saturates immediately at the lift of `{M ≡ 2 (mod 3), M ≢ 5 (mod 9)}`,
`2·3^{d−1}` classes mod `3^{d+1}`, density `2/9` at every depth `d` (CITED:
the pruned tree to depth `k` "is completely determined by `a mod 3^{k+1}`",
Applegate–Lagarias 1995c §2, fetched — §4 below).
(iii) From below, a row `s` has exactly one source smaller than itself iff
`s ≡ 2 (mod 3)` — the column-1 cell `(2s−1)/3` — and none iff `s ≡ 1 (mod 3)`
(Lemma U(d), Lean `pred_unique`).  COMPUTED: odd `n < 200 001` produce no
target divisible by 3; for `s < 5000` the sources below `s` are exactly
`{x = 1}` when `s ≡ 2` and empty when `s ≡ 1 (mod 3)`; every `s < 2000`
coprime to 3 has a greedy backward chain of length 12 avoiding `3Z` with every
step at height `≤ 4` (example `5 ← 13 ← 17 ← 11 ← 7 ← 37 ← 49`); the
no-size sieve returns `2, 6, 18, 54` classes mod `9, 27, 81, 243`, each the
predicted lift (`test_targets_are_never_multiples_of_3_and_smaller_source_is_unique`,
`test_live_backward_chains_exist_at_every_depth`,
`test_no_size_sieve_saturates_at_density_two_ninths`).

**E1 — the leaf rule, mod 9 by mod 6 (PROVED; already on `web/landing.html`
§3 "Sources" and its leaf wheel; the `x = 1` case is the proof of T4 in
`docs/GROUND_TRUTH.md` and `sieve.py`; the period-6 mechanism is the
`sieve.py` module docstring ("T4 does NOT recurse on its own … 2 has order 6
mod 9") and the `surviving_residues_mod3_no_size` docstring.  CITED: the `x = 1` leaf rule
is the Fig. 1/Fig. 2 caption of Applegate–Lagarias 1995c (fetched; nodes
`n ≡ 5 (mod 9)` circled because their preimage `(2n−1)/3 ≡ 0 (mod 3)`), and
the proof of Monks et al. 2013 Lemma 5.5, Cases 1–4 (the lemma's statement is only that the
back-tracing parity vector has at most three consecutive 0's) — greedy
back-tracing from `y` coprime to 3 needs 1, 2, 3, 4 halvings for
`y ≡ {2, 8}, {1, 4}, 5, 7 (mod 9)`, which is the first-source
rule below and the height bound `≤ 4` of E0 — and its Fig. 5.2, the leaf
wheel mod 9.  Their Thm 5.7 says every infinite `T`-back-tracing sequence
avoiding `3Z` contains an integer `≡ 2 (mod 9)`, possibly an even one; for odd
chains alone the statement fails (`1 ← 1 ← …`), so it is not a statement
about rows.  The full mod-6 periodicity of the dead heights is the one-line
extension.)**  For an admissible landing `(s, x)` the source
`n = (2^x s − 1)/3` is itself a multiple of 3 — a *dead* source, a leaf of
the backward tree — iff `2^x s ≡ 1 (mod 9)`.  Since 2 has order 6 mod 9 there
is a unique `x₀(s mod 9) ∈ {0, …, 5}` with `2^{x₀} s ≡ 1 (mod 9)`:

| `s mod 9` | 1 | 2 | 4 | 5 | 7 | 8 |
|---|---|---|---|---|---|---|
| dead heights `x ≡ · (mod 6)` | 0 | 5 | 4 | 1 | 2 | 3 |

The admissible heights are `x ≡ x₀ (mod 2)`, the dead ones `x ≡ x₀ (mod 6)`,
the live ones `x ≡ x₀ + 2, x₀ + 4 (mod 6)`: **exactly one of every three
consecutive admissible heights is dead**, for every row (along a row
`y_{x+2} = 4y_x + 1`, so the residue mod 3 advances by one).  The first
admissible source (`x = 1` if `s ≡ 2`, `x = 2` if `s ≡ 1 (mod 3)`) is dead iff
`s ≡ 5 (mod 9)` (that is T4, `M ≢ 5 (mod 9)`) or `s ≡ 7 (mod 9)` (its `x = 2`
twin, `4·7 ≡ 1 (mod 9)`).  General `q` with `2s > q`: iff `s ≡ 5q, 7q (mod 9)`;
the bound is sharp (`q = 7`, `s = 1`: first positive source at `x = 4`,
namely 3).  COMPUTED: for the 667 odd `s < 2000` coprime to 3 and `x ≤ 30`
(15 admissible heights each, a multiple of 3, so the fraction is exact):
10 005 landings, 3 335 dead, exactly 5 per row; the 222 rows whose first
source is dead are exactly `s ≡ 5, 7 (mod 9)`, beginning
`5, 7, 23, 25, 41, 43, 59, 61`; among all odd `n < 200 001`, `33 333 =
⌊100 000/3⌋` are dead sources (`test_leaf_rule_mod_9_by_mod_6`,
`test_dead_source_counts`, `test_first_source_leaf_rule_on_the_3nq_harness`).
Globally, the leaves of the odd pruned tree are the odd multiples of 3, one
third of the odd numbers (PROVED, trivial: T0); no source is cited for this
count.

**E2 — the exclusion tiers below 100 (COMPUTED on PROVED gates; tiers are
T0, U, T2, T4: the two mod-12 gates are `docs/LEDGER.md` §3, the mod-9 and
mod-16 kills are `docs/GROUND_TRUTH.md` T4 and T8; the tier counts and the
lists below are not stated elsewhere in the repo and are pinned by
`test_exclusion_tiers_below_100`).**
50 odd numbers → 33 have a row (`3 ∤ s`; the 17 multiples of 3 appear only
as cells) → 16 can be entered by a rise (`s ≡ 2 (mod 3)`) → 10 have that
rise coming from a row (`s ≢ 5 (mod 9)`); for the six rows
`5, 23, 41, 59, 77, 95` the unique rise source is a multiple of 3
(`3 → 10 → 5`), so within a chain of rows — in particular within a cycle —
they can be entered only by falls.  For a **nontrivial** cycle (`M > 1`; the
trivial cycle has `M = 1 ≡ 1 (mod 3)`, entered at height 2) the maximum is
entered at height 1 (T2) and left at height `≥ 2` (T1), so
`M ≡ 2 (mod 3)`, `M ≡ 1 (mod 4)`, `M ≢ 5 (mod 9)`: candidates below 100 are
`17, 29, 53, 65, 89`, and the forward gate T8 (`M ≢ 9 (mod 16)`) removes 89.
The minimum (`m > 1`) is entered at height `≥ 2` and left at height 1:
`m ≡ 3 (mod 4)`, `3 ∤ m` (`docs/LEDGER.md` §3; Lean `Minimum.lean`
`m_step_one`, hypothesis `q < m`; census 434/434 cycles with `m ≥ q`, `L ≥ 2`
leave `m` by one halving with `m ≡ q + 2 (mod 4)`, `3 ∤ m`,
`test_ledger.py::test_min_gate_counts_quoted_on_the_page`, repeated in
`test_cycles_chain_in_landing_coordinates_and_satisfy_the_cycle_equation`).
Below `2^71` none of this matters (Barina 2025, CITED).
(`test_exclusion_tiers_below_100`.)

**E2′ — the forward 2-adic sieve: the one exclusion that is neither `3Z` nor
the cycle problem (CITED from this repo: `docs/GROUND_TRUTH.md` §4b,
`sieve.surviving_residues_mod2`, `python/tests/test_sieve.py` `SURV2`).**
Start at the source `M` and follow the landings forward: with `A_j` the sum
of the first `j` heights, `x_j 2^{A_j} = 3^j M + d_j` with `d_j > 0`, so
whenever `2^{A_j} < 3^j` the `j`-th target `x_j` exceeds `M` outright, for
every positive `M`.  The first `j` heights are a function of
`M mod 2^{A_j+1}` (`v₂(3M+1) = x` is a condition mod `2^{x+1}`, not
`2^x`: `M = 1` and `M = 5` agree mod 4 and have `x₁ = 2, 4`), so the kill at
step `j` is a condition on `M mod 2^a` with `a = A_j + 1`, unconditional (no
largeness hypothesis); the listed kills are `a = 2, 4, 7, 10, 12` ↔ `A_j = 1,
3, 6, 9, 11` at `j = 1, 2, 4, 6, 7`, i.e. `a = ⌊j log₂ 3⌋ + 1` as in
`docs/GROUND_TRUTH.md` §4b.  Kills at `a = 2` (`M ≡ 3 (mod 4)`; this is T1), `a = 4`
(`M ≡ 9 (mod 16)`; this is T8), `a = 7` (`97, 125 (mod 128)`), `a = 10`
(7 classes), `a = 12` (30 classes), none at `a = 3, 5, 6, 8, 9, 11`;
survivors `1, 2, 3, 6, 12, 22, 44, 88, 169, 338, 646`
classes mod `2^a` for `a = 2..12` (COMPUTED,
`test_forward_two_adic_sieve_in_landing_form`; `646/2048 ≈ 0.3154` at
`a = 12`).  It saturates: limiting density `0.2863153965` of the odd numbers
(CITED, §4b: DP to depth 600, not recomputed here), so it excludes about
71.4 % of the odd `M` and then stops; a surviving class need not contain any
cycle maximum.

**E3 — what the size bound adds, and why that is the cycle problem
(CITED from this repo: Lemma U(c)/(d), T2, T4, `docs/GROUND_TRUTH.md` §4a
and §6 "The sieve *is* the cycle problem" (the second §6, after §8),
`docs/DEATH_DEPTH.md`, `lean/Collatz/Equivalence.lean`).**  Once every
member must be `≤ M`, the heights available at a target `s` are the admissible
`x` with `2^x s ≤ 3M+1`, about `½·log₂(3M/s)` of them (U(c); COMPUTED at
`M = 10⁶`: 10, 7, 2 heights at `s = 5, 101, 100 001`), of which two in three
are live; at `s = M > 1` the box holds only `x = 1` when `M ≡ 2 (mod 3)` and
is empty when `M ≡ 1 (mod 3)` (U(d); the empty case is T2's kill), so a
nontrivial maximum is entered by the single landing `(M, 1)` whose source
`(2M−1)/3` is dead iff `M ≡ 5 (mod 9)` (T4).  Iterating is the backward sieve: exact-size survivors
mod `3^{k+1}` (`sieve.surviving_residues_mod3`, valid above the floor-rule
threshold) `2, 4, 6, 13, 22` for `k = 1..5`; magnitude-free `a_k` with
`P(d ≥ k) = a_k/3^k`: `1, 2, 3, 6, 10, 22, 50, 104, 254, 538` for
`k = 1..10` (`test_what_the_size_bound_adds`).  The honest statement: for odd
`M > 1`, an **infinite** backward chain starting at `M` and bounded by `M`
exists iff `M` is the maximum of a nontrivial cycle (PROVED; Lean
`Equivalence.lean` `exists_nontrivial_periodic` gives a nontrivial periodic
point `z ≠ 1`, `z ≤ M`, from such a chain; that `M` itself lies on that cycle
is the one extra line `y_i = y_j ⇒ y_0 = y_{j−i}`, not machine-checked; the
converse is `Cycle.toBackChain`).  Survival at every *finite* depth ⟺ cycle
is **not** machine-checked (König's lemma; `Unproved.lean`, its second item
4, "KÖNIG'S LEMMA", after item 7;
`docs/GROUND_TRUTH.md` §6 "The sieve *is* the cycle problem", the second §6,
after §8).  So "exclude
more by bounded unreachability" is not a tool applied to the cycle problem;
it is the cycle problem, `M` by `M`.  The survivor-thinning rate (rigorous
bracket `[0.7364, 0.9465]` on `lim (a_k/3^k)^{1/k}`, `docs/DEATH_DEPTH.md`) is
a density statement, and density zero is not emptiness.

**Verdict on the exclusion idea.**  Magnitude-free reachability excludes
exactly `3Z ∩ Odd` (E0) and then stops (E0(ii)); the leaf rule (E1) says
which *cells* of the remaining rows are dead, one in three, forever; the
forward 2-adic sieve (E2′) excludes a further 71.4 % of the odd `M`
unconditionally and stops at density `0.2863`; everything else in this
repository comes from the size bound and is the cycle problem itself (E3).  The table makes this visible; it does not change
it.

---

## 3. The height word and the residue automaton `= Φ_k`

Read a chain of landings by its heights only: the **height word**
`(x₁, x₂, …)`.  Read backwards from a cycle maximum it is the word
`b = (b₁, b₂, …)` of `docs/WORDS.md` (`b₁` = the height *into* `M`); the
forward word of the same walk is `reversed(b)`.

**H1 — parity of every height is forced by the target's residue mod 3
(PROVED; Lemma U(b)).**  `x` is odd iff `s ≡ 2 (mod 3)`, even iff
`s ≡ 1 (mod 3)`.  COMPUTED on all odd `n < 10⁵` (bijection test), and on the
census (`test_mod_3_share_of_cycle_members`).

**H2/H4 — the forward residue automaton, and the one-step sweep (PROVED,
trivial; the backward form is the docstring of
`sieve.surviving_residues_mod3_no_size`, `docs/WORDS.md` W1/C7, and Monks et
al. 2013 Lemma 4.3 and Prop. 6.1(d), "2 is a primitive root mod every power
of 3").**  On `Z/3^k` the odd step is
`n ↦ 2^{−x}(3n+1)`, which depends on `x` only mod `2·3^{k−1}` (2 is a
primitive root mod `3^k`).  For *any* residue `r` (unit or not) the map
`b ↦ 2^{−b}(3r+1)` is a bijection from `Z/(2·3^{k−1})` onto the units mod
`3^k`, so the transition matrix on units over the cyclic alphabet is the
all-ones matrix `J` already at **one** step: `A_k^L = (2·3^{k−1})^{L−1} J`,
`tr A_k^L = (2·3^{k−1})^L`, and `Φ_k` over words with letters uniform on
`Z/(2·3^{k−1})` is exactly equidistributed with fibres of size
`(2·3^{k−1})^{k−1}`.  A referee's caveat is part of the statement: this
equidistribution is a property of the uniform measure on the artificial
cyclic alphabet only; for the integers' own letters (geometric weights
`2^{−b}`, Tao 2022) and for the capped word set the fibres are *not* uniform,
and the non-unit residues (multiples of 3) have in-degree 0 (T0) and are the
only unreachable states.  COMPUTED `k ≤ 5`
(`test_one_step_sweep_and_forward_realization_for_k_le_5`).

**H3 — forward realization = W1 read forward (PROVED; `docs/WORDS.md` W1,
C1; Terras 1976 for the forward mirror).**  For every `k`, every start residue
`n₀` mod `3^k` and every input word `(x₁, …, x_k)`, the end state is
`Φ_k(x_k, …, x₁)` — the WORDS.md residue map of the *reversed* word —
independently of the start (the closed form
`n_k 2^{X_k} = 3^k n₀ + Σ 3^{k−i} 2^{X_{i−1}}` loses the `n₀` term mod `3^k`).
For integers: if the first `k` forward heights of odd `n` are `x₁..x_k` then
`S^k(n) ≡ Φ_k(x_k, …, x₁) (mod 3^k)`.  Hence the closing state of a cycle
maximum read backward with word `b` is `Φ_k(b₁..b_k)`, and the set of closing
states over admissible `k`-words is exactly the survivor set `S_k`, `a_k` of
them.  COMPUTED: all words for `k ≤ 3` and 3000 random words for `k = 4, 5`,
start-independent and equal to `phi(reversed)`; 6000 integer trials
(`n < 10⁹`, `k ≤ 6`); `image(Φ_k)` over admissible words `= S_k` for `k ≤ 6`
with `a_k = 1, 2, 3, 6, 10, 22` and `N_k = 1, 2, 3, 7, 12, 30`
(`test_one_step_sweep_and_forward_realization_for_k_le_5`,
`test_integers_realize_phi_of_the_reversed_height_word`,
`test_survivor_sets_are_the_image_of_phi_and_the_counts`).

**H5/H6 — 3-adic closure is automatic; the whole cycle condition is one
Diophantine statement (PROVED; already in `python/collatz_maxodd/padic.py`
`periodic_point`, `docs/WHY_NOT.md`, `lean/Collatz/Periodic.lean`; the
mod-`3^k` form is W1 + C1 applied to the periodic word; T7 / Böhm–Sontacchi
1978 and its converse, Lagarias 1990).**  For **every** height word
`x = (x₁..x_L)` of positive integers and every `k` there is exactly one start
state mod `3^k` whose walk closes, namely `c/(2^B − 3^L) mod 3^k` with
`c = Σ_{i=1}^{L} 3^{L−i} 2^{X_{i−1}}` (the denominator is a 3-adic unit); all
its states are units; and it equals `Φ_k(b^∞|_k)` for `b = reversed(x)`.
Consequently no height word is excluded by any congruence condition mod `3^k`
alone.  A word is the height word of a closed odd walk (a cycle traversed some
positive number of times; a single cycle iff the word is primitive — e.g.
`(2, 2)` gives `n₀ = 1` twice) iff `n₀ = c/(2^B − 3^L)` is a **positive
integer**; then every member is automatically an odd integer with
`xᵢ = v₂(3n_{i−1}+1)` exactly.  So for `q = 1` the entire exclusion content
lies in (i) the magnitude caps of the backward sieve, (ii) integrality of
`c/(2^B − 3^L)`, and (iii) its **sign** `2^B > 3^L` — negative integer
periodic points such as `−1 = (1)`, `−5, −7 = (1,2)`,
`−17 = (1,1,1,2,1,1,4)` (`L = 7`, `B = 11`, the cycle
`−17, −25, −37, −55, −41, −61, −91`) pass every congruence, and one phase
of each (`−1`, `−7`, `−91`) also passes every cap (H9(iii)); the other phases
die at finite depth despite being integer periodic points.  Notation warning: in this repository `A_k`
denotes the set of admissible words (`a_k = |Φ_k(A_k)|`); the automaton above
is not given that symbol.  COMPUTED `k ≤ 4`, `L ≤ 3`, letters `≤ 4`
(`test_every_height_word_has_exactly_one_closed_walk_per_level`).

**H9 — immortal periodic words are the negative rational cycles (PROVED;
Lagarias, *Acta Arith.* 56 (1990) for rational cycles with odd denominator
↔ integer cycles of `3x+d`; `docs/WORDS.md` W2 has `−7` "checked", the two
lines below prove it).**  (i) If `b` is an admissible `L`-word then `b^∞` is
admissible at every depth, because `f(t) = ⌊t log₂ 3⌋` is superadditive
(`m f(L) + f(t) ≤ f(mL + t)`).  (ii) For admissible `b`,
`r(b) = c_L/(2^{B_L} − 3^L)` is a **negative** rational with odd denominator
(`B_L ≤ f(L)` gives `2^{B_L} < 3^L`), a cycle of the rational Syracuse map,
and `r(b) mod 3^k ∈ S_k` for every `k`; moreover
`S_k = {r(b) mod 3^k : b admissible, |b| ≥ k}` (PROVED: `⊇` because
`r(b) mod 3^k = Φ_k(b^∞|_k)` (H5/H6) and `b^∞|_k` is admissible by (i);
`⊆` because `S_k = Φ_k(A_k)` (W1, H3) and for an admissible `k`-word `w`,
`r(w) mod 3^k = Φ_k(w^∞|_k) = Φ_k(w)`; COMPUTED witness `k ≤ 6`,
`|b| ≤ k + 2`).  (iii) The `−7` phase
`(1, 2)` of the cycle `{−5, −7}` therefore survives the magnitude-free sieve
at every depth, while the `−5` phase `(2, 1)` dies at depth 1; the negative
7-cycle `{−17, …, −91}` has exactly one immortal phase, `−91`, backward
word `(1,1,2,1,1,1,4)`; the other six phases die, `−17, −25, −37, −55, −41, −61` at depths
`1, 3, 6, 7, 1, 9`, the last of them `−61` at depth 9 (COMPUTED, `k ≤ 12`).  The complement is the point of
`docs/WHY_NOT.md`: a positive cycle's own word has `B_L ≥ f(L) + 1` by T7
(equality if `L·δ(m) < 1`, the Crandall–Eliahou squeeze of `docs/LEDGER.md`
§6; the converse fails: on the census 95 cycles have `B = f(L) + 1` with
`L·δ(m) ≥ 1`, e.g. `q = 7`, `M = 11`, `L = 2`, `B = 4`, `L·δ ≈ 1.105`;
COMPUTED, `test_cycles_chain_in_landing_coordinates_and_satisfy_the_cycle_equation`),
at least one over the symbolic cap, so **a positive cycle's own backward word
leaves the admissible set `A_k` at `k = L`**: for `k ≥ L` its maximum can lie
in `S_k` only through a collision with a *different* admissible word.  This is
a statement about words, not residues — `S_k` is a set of residues mod `3^k`
and cycle maxima do lie in it: for `q = 1` every nontrivial `M ≡ 2 (mod 3)`
is in `S₁ = {2}`, and on the harness (`S_k(q) = q·S_k(1)`, PROVED: the
backward step `y ↦ (2^b y − q)/3` commutes with multiplication by the 3-adic
unit `q` and the caps are `q`-free; pinned for `k ≤ 9`, `q = 5, 7`) the `q = 5` cycle
`(49, 19, 31)` (`L = 3`, `B = 5 > f(3) = 4`) has `49 mod 3^k ∈ S_k(5)` for
every `k ≤ 7`, dying only at `k = 8`, and the `q = 7` cycle `(11, 5)`
(`B = 4 > f(2) = 3`) survives to `k = 4` (COMPUTED,
`deathdepth.surviving_residues(9, q)`).  What the caps meet
is the exact T6 size test with its floor-rule thresholds
(`docs/GROUND_TRUTH.md` T6, valid for `k ≤ 19`).  COMPUTED `k ≤ 12`
(`test_trivial_cycle_and_the_immortal_negative_words`).

**H10 — the mod-3 share of a cycle's members (PROVED conditional on
`m ≥ 12 825`, Lean `Halving.lean` `single_halving_percent` + Lemma U(b);
discharge CITED: Barina 2025, `m > 2^71`; restatement of `docs/STRUCTURE.md`
§3 read on the target side).**  `#{members ≡ 2 (mod 3)} = #{odd heights} ≥ u
≥ 2L − B`, where `u` counts single halvings; for `q = 1` and minimum
`m ≥ 12 825` (the sharp threshold of `(3m+1)^{200} ≤ 2^{317} m^{200}`)
`1000u ≥ 415L`, so at least 41.5 % of the members are `≡ 2 (mod 3)` and at
most 58.5 % are `≡ 1 (mod 3)`.  The trivial cycle (`u = 0`) shows the
hypothesis cannot be dropped.  COMPUTED on all 2127 census cycles and the
threshold (`test_mod_3_share_of_cycle_members`).  Adjacent in the literature:
Monks et al. 2013 Prop. 6.3(b) bounds the share of odd (`T₁`) steps of a
nontrivial cycle below by `ln 2 / ln(3 + 1/m)`, the same squeeze read on the
`T`-word.

**What was tried and did not survive (recorded so it is not retried).**
A draft claimed that for a nontrivial cycle with `L < 1/δ(m)` the backward
word is an admissible `(L−1)`-word followed by one over-cap letter, hence one
of `N_{L−1}` symbolic candidates.  PROVED parts, for a cycle with
`L·δ(m) < 1`: `B_L = f(L) + 1` exactly (T7 + the Crandall–Eliahou squeeze,
`docs/LEDGER.md` §6), and `B_t ≤ f(t) + 1` for every `t < L` (the same
squeeze on the prefix, which needs `t·δ(m) < 1`); unconditionally,
`B_t ≤ f(t)` wherever `M > floor_rule_threshold(t)`, known for `t ≤ 19`
(`M > 17 344`, `docs/GROUND_TRUTH.md` T6).  NOT PROVED: the all-prefix floor
rule — `floor_rule_threshold(t)` is computed only to `t = 19`
(`backtree.floor_rule_threshold`, `cap = 10⁶`), is not monotone, and nothing
is claimed beyond; a draft's "`t ≤ 115` for `M > 2^71`" and "exceeds `2^71`
at `t = 119`" could not be reproduced and are withdrawn.  On the harness real
cycles do carry over-cap prefixes (`q = 47`, `M = 175`, backward word
`(1,2,2,2)`, `B_3 = 5 > 4 = f(3)`; `M/q ≈ 3.7`, so no contradiction with the
`q = 1` thresholds, which scale with `q`; COMPUTED,
`test_cycles_chain_in_landing_coordinates_and_satisfy_the_cycle_equation`).
The candidate count is therefore CONJECTURE at best and is not used anywhere.

---

## 4. Literature — what the landing form is called elsewhere (CITED)

Sources read during this run: Lagarias' annotated bibliography 1963–1999
(arXiv math/0309224), Monks–Monks–Monks–Monks, *Discrete Math.* 313 (2013)
(arXiv 1204.3904), Lagarias 2021 (arXiv 2111.02635),
Applegate–Lagarias, *Experimental Math.* 4 (1995) no. 3, Chamberland, "An
update on the 3x+1 problem", Tao, *Forum Math. Pi* 10 (2022), and the
entries already in `docs/GROUND_TRUTH.md` §8.  Web searches for "landing" together with Collatz
or `(2^k n − 1)/3` returned nothing using the term.

* The cells of a row, `y_b = (2^b s − 1)/3`, are Crandall's odd-to-odd map
  `C_{3,1}` run backwards (*Math. Comp.* 32, 1978; not fetched, via
  Lagarias's bibliography entry 47); the inverse map is
  Kaneda's `g_d` (*Fibonacci Quart.* 53(2), 2015) and Brox's "descendent"
  relation (*Acta Arith.* 92, 2000) — all already cited for T0/U in
  `docs/GROUND_TRUTH.md` §8.
* A landing is Wirsching's back-tracing function of length one,
  `T₁⁻¹ ∘ T₀^{−(x−1)}`, admissible on one residue class mod 3 — his "unique
  congruence class mod `3^m`" lemma at `m = 1`, which is exactly
  `s ≡ (−1)^x (mod 3)` (LNM 1681, 1998, Ch. II — not fetched; the chapter via
  Lagarias's bibliography entry 186, the lemma as quoted in Monks et al.
  2013 §4).  The height sequence along a chain is his block encoding of the
  parity word (*Discrete Math.* 148, 1996; not fetched, via Lagarias's entry
  184).
* The table with its missing rows is the **pruned 3x+1 tree** of
  Applegate–Lagarias, "On the distribution of 3x+1 trees", *Experimental
  Math.* 4 (1995) no. 3 (fetched; running heads pp. 193–209, while Lagarias's
  bibliography entry 8 prints 101–117), §2: the pruned tree `T*_k(a)`
  "consisting of nodes `n ≢ 0 mod 3`", whose structure "is completely
  determined by `a mod 3^{k+1}`" (E0(ii)'s classes mod `3^{d+1}`), with the
  "strict branching" property that every pruned tree branches after at most
  four steps from any node (E0's height bound `≤ 4`); their Fig. 1/Fig. 2
  caption circles the nodes `n ≡ 5 (mod 9)` because they "have a preimage
  `(2n−1)/3 ≡ 0 mod 3`" — E1's first-source rule at `x = 1` (T4), eighteen
  years before Monks et al.  The graph form is the **pruned 3x+1 graph** `G̃`
  of Monks et al. 2013 (§1: "the subgraph of G consisting of the positive
  integers relatively prime to 3"; drawn in their Fig. 5.1), restricted here
  to odd vertices; the user's "unreachable set" is exactly that pruning.  The
  earlier Applegate–Lagarias paper (*Math. Comp.* 64, 1995) is not fetched;
  Lagarias's bibliography entry 6 confirms only that its trees are rooted at
  `a ≢ 0 (mod 3)`, and Monks et al. cite it only for the notion of level set
  (the Remark after their definition of `L_k(x)` in §5).  Lagarias 2021 calls
  the unrestricted object the unary-binary tree of inverse iterates;
  Chamberland's survey (fetched) treats it as the predecessor set
  `P_T(a) := {b ∈ Z⁺ : T^{(k)}(b) = a for some k}` with counting function
  `Z_a(x)`, §2.3 "The Collatz Graph and Predecessor Sets"; and
  Beltraminelli–Merlini–Rusconi (1994) are said to draw it as the "chalice"
  (not fetched; known through Lagarias's bibliography, entry 19).
* Columns are Terras' parity classes mod `2^{x+1}` (*Acta Arith.* 30, 1976);
  the forward residue reading of §3 is Terras' side of Wirsching's realization
  lemma.  The one-step sweep of §3 is the primitive-root argument of Monks et
  al. 2013 Lemma 4.3 and Prop. 6.1(d) (their Thm 4.4 is the analogue for an
  odd prime `p > 3` with 2 a primitive root mod `p^r`); the leaf rule E1 is
  the proof of their Lemma 5.5 (Cases 1–4) / Fig. 5.2; the non-uniformity caveat is Tao 2022 §1 (the Syracuse
  map on `Z/3^n Z` is not uniformly distributed; Prop. 1.14 mixes only at fine
  3-adic scales).
* The cycle equation and its converse: Böhm–Sontacchi (*Atti Accad. Naz.
  Lincei* 64, 1978); rational cycles with odd denominator: Lagarias
  (*Acta Arith.* 56, 1990).  The leaf count (one third of the odd vertices)
  is T0 and needs no source.
* The `(2^71)` search bound: Barina, *J. Supercomputing* 81 (2025).

---

## 5. Verification table

All tests in `python/tests/test_landing.py`
(`cd python && uv run pytest tests/test_landing.py -q`: 24 passed).

| § | statement | label | witness | numbers pinned |
|---|---|---|---|---|
| 0 | `λ`: odd → admissible landings is a bijection, inverse `σ`; `D = s(2^x−1)`, `3(2n+1) = 2^{x+1}s+1`; rise iff `x = 1` | PROVED (LEDGER §2, U(b)) | `test_landing_map_is_a_bijection_onto_admissible_landings` | 50 000 odd `n < 10⁵` ↔ 50 000 landings |
| 0 | every admissible cell has exactly one source; other parity never admissible | PROVED | `test_every_admissible_landing_has_exactly_one_source` | 399 996 cells, `s ≤ 10⁵`, `x ≤ 24` |
| 0 | general-`q` bijection (harness) | PROVED | `test_landing_bijection_survives_on_the_3nq_harness` | 33 values `5 ≤ q ≤ 101`, `n < 20 000` |
| 1 | chaining ⟺ closure; `3^k y_k = 2^{B_k}M − c_k`; `M(2^B−3^L) = c_L`; T2 landing height 1; minimum gate; `q = 47` over-cap prefix | PROVED (GROUND_TRUTH §1, T7, T2, LEDGER §3) / COMPUTED | `test_cycles_chain_in_landing_coordinates_and_satisfy_the_cycle_equation` | 2127/2127; 1482/1482 with `M > q`; 434/434 min gate; `(175, 47)`: `(1,2,2,2)`, `B_3 = 5 > 4`; 95 cycles with `B = f(L)+1`, `L·δ(m) ≥ 1` |
| 1 | `Σ sᵢ(2^{xᵢ}−3) = Lq`; `2^B = ∏(3sᵢ+q)/sᵢ` | PROVED (LEDGER §1, §6) | `test_additive_and_multiplicative_ledgers_in_landing_form` | 2127/2127 |
| 1 | unique fixed cell `(1,2)`; fixed cells `s(2^x−3) = q` | PROVED (FP) | `test_fixed_cells_are_s_times_2x_minus_3_equals_q` | 89 = 89 for `q < 200` |
| 1 | balance is not closure; sum + shifted product force closure only at `L = 2` | COMPUTED (LEDGER §2) | `test_balance_is_not_closure_in_landing_form` | 83 pairs / 0; 408 and 4 784 triples / 0 |
| 1 | `{sources} = {targets}` characterises unions of cycles | PROVED, trivial | `test_unions_of_cycles_also_satisfy_sources_equal_targets` | harness; `q = 7`: `{7} ∪ {11, 5}` |
| 2 | in-degree 0 iff `3 | s`; smaller source unique, `x = 1`, iff `s ≡ 2 (mod 3)` | PROVED (T0, U(d)) | `test_targets_are_never_multiples_of_3_and_smaller_source_is_unique` | `n < 200 001`; `s < 5000` |
| 2 | leaf rule: dead iff `2^x s ≡ 1 (mod 9)` iff `x ≡ x₀(s mod 9) (mod 6)`; `y_{x+2} = 4y_x + 1`; one dead in three; first-source rule `5, 7 (mod 9)` | PROVED (landing.html §3, T4; CITED Applegate–Lagarias 1995c Fig. 2, proof of Monks Lemma 5.5) | `test_leaf_rule_mod_9_by_mod_6` | `s < 3000`, `x ≤ 60` |
| 2 | dead-source counts | COMPUTED | `test_dead_source_counts` | 667 rows, 10 005 / 3 335, 5 per row, 222 first-dead, 33 333 below 200 001 |
| 2 | live backward chains at every depth | PROVED (sieve docstring) | `test_live_backward_chains_exist_at_every_depth` | length 12, `s < 2000`, heights `≤ 4` |
| 2 | no-size sieve saturates at 2/9 | PROVED (GROUND_TRUTH §4a) | `test_no_size_sieve_saturates_at_density_two_ninths` | 2, 6, 18, 54 classes |
| 2 | exclusion tiers below 100; maximum candidates; T8 | COMPUTED on PROVED gates (LEDGER §3, T4, T8) | `test_exclusion_tiers_below_100` | 50/33/17/16/10; `5,23,41,59,77,95`; `17,29,53,65,89` → `17,29,53,65` |
| 2 | size-bound sieve tables; heights in the box; `{1}` at `M ≡ 2`, `∅` at `M ≡ 1 (mod 3)` | CITED (§4a, DEATH_DEPTH, U(c)/(d)) | `test_what_the_size_bound_adds` | 2,4,6,13,22; `a_k` to 538; 10, 7, 2 |
| 2 | forward 2-adic sieve in landing form; kills `a = 2, 4, 7, 10, 12`; survivor counts | CITED (GROUND_TRUTH §4b) / COMPUTED | `test_forward_two_adic_sieve_in_landing_form` | `{1}`, `{1,5}`, `{1,5,13}`; 1,2,3,6,12,22,44,88,169,338,646; kills `3`, `9`, `97, 125`, 7 at `a = 10`, 30 at `a = 12`; first `j` heights fixed by `M mod 2^{A_j+1}`, not `2^{A_j}` (`M < 5000`, `j ≤ 4`) |
| 2 | first-source leaf rule, general `q`, `2s > q` sharp | PROVED (harness) | `test_first_source_leaf_rule_on_the_3nq_harness` | 8 values of `q`, `s < 4000`; `q = 7, s = 1` |
| 3 | one-step sweep `A_k = J`; end state `= Φ_k(reversed)`, start-free | PROVED (W1, C7) | `test_one_step_sweep_and_forward_realization_for_k_le_5` | `k ≤ 5` |
| 3 | `S^k(n) ≡ Φ_k(x_k..x₁)` | PROVED (W1, C1) | `test_integers_realize_phi_of_the_reversed_height_word` | 6000 trials, `k ≤ 6` |
| 3 | `image(Φ_k) = S_k`; `a_k`, `N_k` | PROVED / COMPUTED (WORDS, DEATH_DEPTH) | `test_survivor_sets_are_the_image_of_phi_and_the_counts` | 1,2,3,6,10,22; 1,2,3,7,12,30 |
| 3 | one closed walk per word per level `= c/(2^B−3^L) = Φ_k(b^∞)`; `−17 = (1,1,1,2,1,1,4)` | PROVED (padic, WHY_NOT, Periodic.lean) | `test_every_height_word_has_exactly_one_closed_walk_per_level` | `k ≤ 4`, `L ≤ 3`; `L = 7`, `B = 11` |
| 3 | `(2)` closes on 1; `(1,2)^∞` admissible; `−7, −1 ∈ S_k`, `−5 ∉ S_k`; `−91` the immortal phase; `S_k = {r(b) mod 3^k}` | PROVED / COMPUTED (W2 upgraded) | `test_trivial_cycle_and_the_immortal_negative_words` | `k ≤ 12`; the seven phases die at `1, 3, 6, 7, 1, 9, never`; `k ≤ 6`; harness maxima `49` (`q = 5`) and `11` (`q = 7`) in `S_k(q)` to `k = 7` and `4` |
| 3 | mod-3 member share; 12 825 sharp | PROVED cond. + CITED | `test_mod_3_share_of_cycle_members` | 2127/2127 |
| page | table geometry; in-degrees from `n < 2^20`; first unhit target | COMPUTED | `test_landing_table_geometry_and_in_degrees` | 22/110/36/20 821; 16/64/22/3669; 10,10,9,9,8,9; 786 433 |
