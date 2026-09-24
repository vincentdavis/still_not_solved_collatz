# The drop function `f(n) = n − S(n)`

**Provenance.** A visualization-led pass of 2026-09-23 (`web/drop.html`,
`python/collatz_maxodd/drop.py`, `python/tests/test_drop.py`) on the idea of
pairing each odd `n` with its signed distance to the next odd number on its
trajectory, and then asking which combinations of those distances sum to zero.
Labels follow the house scheme: **PROVED** (complete proof below), **COMPUTED**
(exact, this project, pinned by a test), **CITED**.  The page, by the user's
standing decision for the ledger family, treats **`3n+1` only**; the general
`q` in the module is the test harness.  Nothing in this document is claimed
new: see §4.

Setting as everywhere in this repo: for odd `n`, `x = v₂(3n+1)` (the
*height*), `s = S(n) = (3n+1)/2^x` (the *target*), and now the **drop**

    f(n) = n − s = ((2^x − 3)·n − 1) / 2^x .

For general `q`: `f_q(n) = n − S_q(n) = ((2^x − 3)n − q)/2^x`.  The drop is
minus the *net* `s − n` of the ledger pairs (`docs/LEDGER.md` §2) and is
`n − s` in the landing form (`docs/LANDING.md`); the three pages are one
bookkeeping in three coordinates.

---

## 1. The function (PROVED)

**D1 (parity, sign).** `f(n)` is even.  `f(n) < 0` iff `x = 1` iff
`n ≡ 3 (mod 4)`, and then `f(n) = −(n+1)/2`.  `f(n) = 0` iff `n = 1`.
Otherwise `x ≥ 2`, `n ≡ 1 (mod 4)`, `n > 1`, and `f(n) ≥ (n−1)/4`.

*Proof.* `n` and `s` are odd.  `2^x f(n) = (2^x − 3)n − 1`; for `x = 1` the
right side is `−n − 1 < 0`; for `x ≥ 2` it is `≥ n − 1 ≥ 0` with equality
iff `x = 2` and `n = 1`.  `x = 1` iff `3n+1 ≡ 2 (mod 4)` iff `n ≡ 3 (mod 4)`. ∎

**D2 (height classes).** The sources at height `x` are one residue class
`n ≡ n₀(x) (mod 2^{x+1})`; their targets are one odd class mod 6
(`s ≡ 1 (mod 6)` for even `x`, `s ≡ 5 (mod 6)` for odd `x`); on the class
`f` is affine with slope `1 − 3/2^x`, and the drops form the arithmetic
progression `d₀(x) + 2(2^x − 3)·k`, `k ≥ 0`.  The first source at an even
height is `(2^x − 1)/3`, landing on 1.

*Proof.* `n = (2^x s − 1)/3` is an integer iff `2^x s ≡ 1 (mod 3)` iff
`s ≡ (−1)^x (mod 3)`; with `s` odd that is one class mod 6, `s = s₀ + 6k`.
Then `n = n₀ + 2^{x+1}k` and `d = n − s = d₀ + 2(2^x − 3)k`. ∎

| `x` | `2^x − 3` | sources | first `n₀` | `→ s₀` | first drop | step |
|---|---|---|---|---|---|---|
| 1 | −1 | `3 (mod 4)` | 3 | 5 | −2 | −2 |
| 2 | 1 | `1 (mod 8)` | 1 | 1 | 0 | +2 |
| 3 | 5 | `13 (mod 16)` | 13 | 5 | 8 | +10 |
| 4 | 13 | `5 (mod 32)` | 5 | 1 | 4 | +26 |
| 5 | 29 | `53 (mod 64)` | 53 | 5 | 48 | +58 |
| 6 | 61 | `21 (mod 128)` | 21 | 1 | 20 | +122 |
| 7 | 125 | `213 (mod 256)` | 213 | 5 | 208 | +250 |
| 8 | 253 | `85 (mod 512)` | 85 | 1 | 84 | +506 |

(COMPUTED to `x = 14` against brute force, `test_d2_height_classes_against_brute_force`.)

## 2. Which numbers are drops (PROVED)

**D3 (fibers).** Every even integer is a drop; no odd integer is.  The odd
`n` with `f(n) = d` correspond one-to-one to the heights `x ≥ 1` with
`(2^x − 3) | (3d + 1)` and positive quotient, via `s = (3d+1)/(2^x − 3)`,
`n = s + d`.  Concretely:

* `d < 0`: exactly one source, `n = −2d − 1 = 2|d| − 1` (height 1);
* `d = 0`: only `n = 1`;
* `d > 0`: one source per divisor of `3d + 1` of the form `2^x − 3`,
  `x ≥ 2`, i.e. per member of `1, 5, 13, 29, 61, 125, 253, 509, 1021, …`
  dividing `3d+1`; the divisor 1 always works and gives the source
  `4d + 1 ≡ 1 (mod 8)`.

*Proof.* `n = s + d` and `3n + 1 = 2^x s` give `(2^x − 3)s = 3d + 1`.
Conversely, given such a divisor with quotient `s`: `3d+1` is odd (`d` even)
and `2^x − 3` is odd, so `s` is odd; `n = s + d` is odd; `3n + 1 = 2^x s`
with `s` odd, so `v₂(3n+1) = x` and `S(n) = s`.  For `d < 0` the only
negative coefficient is `x = 1`; for `d = 0` the equation is
`(2^x − 3)s = 1`; distinct `x` give distinct `n` since `n = d + (3d+1)/(2^x−3)`
is strictly decreasing in `x`.  If `d` is odd then `3d+1` is even and no odd
product equals it. ∎

**D4 (the fiber size is unbounded).** The `2^x − 3` are odd and prime to 3,
so `L_X = lcm(2^x − 3 : 2 ≤ x ≤ X)` is invertible mod 6 and has a multiple
`M ≡ 1 (mod 6)`; then `d = (M − 1)/3` is an even drop with at least `X − 1`
sources.  For `X = 7`, `L₇ = 5·13·29·61·25 = 2 874 625 ≡ 1 (mod 6)`,
`d = 958 208`, six sources (`test_d4_witnesses`); by D3 no smaller drop has
six, since six distinct `2^x − 3` with `x ≥ 2` must divide `3d+1`.

**COMPUTED** (`test_d3_records`, `test_d3_distribution`): first drop with
`k` sources: `k = 1, 2, 3, 4, 5, 6 → d = 2, 4, 48, 628, 15 708, 958 208`;
`d = 628` has sources `693, 773, 1005, 2513` at heights `5, 4, 3, 2`.  Over
the 50 000 even drops `2 … 100 000`: one source 34 806 times, two 13 313,
three 1 774, four 104, five 3.

## 3. The drop ledger (PROVED)

**D5 (telescoping).** Along the odd steps `n₀ → n₁ → … → n_k` the drops sum
to `n₀ − n_k`; for a trajectory reaching 1, `Σ f(nᵢ) = n₀ − 1`, so the falls'
total exceeds the rises' total by exactly `n₀ − 1`.  Around a cycle the sum
is 0, so the rises' ledger equals the falls' ledger:

    Σ_{rises} (n+1)/2  =  Σ_{falls} ((2^x − 3)·n − 1)/2^x .

This is the ledger identity `E = 4·O + 2L` of `docs/LEDGER.md` and the
landing balance `Σ sᵢ(2^{xᵢ} − 3) = L` of `docs/LANDING.md` in a third
vocabulary.  **COMPUTED** (`test_d5_trajectory_table`): `n = 27` takes 41
odd steps, 24 rises totalling 5 396 and 17 falls totalling 5 422, difference
26; `n = 837 799`: 195 odd steps, falls 2 606 982 852 − rises 2 606 145 054
= 837 798.  Every cycle of the 3n+q census balances (`test_d5_cycles_balance`).

## 4. Zero-sum combinations (PROVED / COMPUTED)

The question raised on the page: do combinations of drops that sum to zero
exist?  Yes, for every size, and none of them is a chain within any searched
range.

**Z1 (pairs).** For every even `d ≥ 2`, `{2d − 1, 4d + 1}` is a zero-sum
pair (`f(2d−1) = −d` by D3, `f(4d+1) = d` at height 2).  Every zero-sum pair
of distinct odd numbers `> 1` is `{2d − 1, n}` with `n` a source of `d`, so the
number of them below `N` equals the number of fall sources below `N` whose
drop is at most `(N−1)/2`.  **COMPUTED**: 83 below 400, 2 109 below 10 000
(`test_zero_sum_counts`, `test_zero_sum_pairs_are_rise_source_plus_a_source_of_d`).

**Z2 (every size).** For `k ≥ 2`, `{3, 7, 11, …, 4k − 5, (2k−1)²}` is a
zero-sum `k`-set: the rise sources `4i − 1` (`1 ≤ i < k`) have drops `−2i`,
total `−k(k−1)`, and `(2k−1)² = 4k(k−1) + 1 ≡ 1 (mod 8)` lands at height 2
with drop `k(k−1)`.  **COMPUTED** for `k < 60`; zero-sum triples below 120:
383 (plus the 25 that include 1 give the ledger page's 408), below 400:
4 701; quadruples below 60: 511, below 100: 2 737.

**Z3 (chains).** Call a set a *chain* if its members can be ordered so that
each one's target is the next, closing up.  A chain's drops sum to zero by D5,
and a chain is exactly a cycle of `S`.  So "zero-sum chain" is "cycle": below
`2^71` the only one is `{1}` (Barina 2025, CITED), and no cycle with fewer
than 92 rise-runs exists at any size (Hercher 2023, CITED).  In every search
above the chain count is 0.

**Z4 (no 2-chain).** A 2-chain is a rise `a → b = a + (a+1)/2` followed by a
fall back to `a`; then `d = b − a = (a+1)/2`, `a = 2d − 1`, `b = 3d − 1`, and
`S(3d−1) = 2d−1` needs `9d − 2 = 2^x(2d − 1)`, i.e.
`d·(2^{x+1} − 9) = 2^x − 2`.  At `x = 2` this is `d = −2`; for `x ≥ 3` the
coefficient exceeds the right side (`2^{x+1} − 9 > 2^x − 2` iff `2^x > 7`),
so `0 < d < 1`.  No solution.  (The `x = 1` case is `d = 0`, excluded.)  This
is the smallest case of Steiner's theorem (CITED: R. P. Steiner, *A theorem
on the Syracuse problem*, Proc. 7th Manitoba Conf. Numerical Math. 1977,
553–559: no cycle with a single rise-run other than `{1}`).

**Z5 (the gates at both ends).** A cycle's largest member `M` and smallest
member `m` satisfy conditions that involve only the number itself, so they can
be imposed on a zero-sum set that is not a chain (the user's question of
2026-09-23).  *Maximum gate at depth `D`* (`sieve.can_be_max_odd`, exact and
unconditional): `3 ∤ M`; `S^j(M) ≤ M` for `j ≤ D` (depth 1 is T1, depth 2
adds T8); some chain of `D` predecessors `≤ M` avoids multiples of 3 (depth 1
is T2 and T4).  *Minimum gate at depth `D`* (`drop.can_be_min_odd`): `3 ∤ m`
and `S^j(m) ≥ m` for `j ≤ D`, because every iterate of `m` is a member; it
has no backward half, since predecessors above `m` always exist
(`y_b = (2^b m − 1)/3 ≥ m` for `b ≥ 2`, and among `b, b+2, b+4` one avoids
multiples of 3 because `y_{b+2} = 4y_b + 1`).  In Terras's language (CITED,
Terras 1976) the minimum of a second cycle has infinite stopping time, and the
depth-`D` gate keeps the residue classes that have not stopped after `D` odd
steps.

PROVED: depth 1 of the minimum gate is `m ≡ 3 (mod 4)` and `3 ∤ m` (Lean
`Minimum.min_mod4_q1`, `min_not_three`).  Depth 2 adds `m ≢ 3 (mod 16)` for
`m > 5`: with `m ≡ 3 (mod 4)`, `S(m) = (3m+1)/2`, `3S(m)+1 = (9m+5)/2` and
`S²(m) = (9m+5)/2^{x+1}` with `x = v₂((9m+5)/2)`; `S²(m) ≥ m` forces
`2^{x+1} ≤ 9 + 5/m < 10`, so `x ≤ 2`, i.e. `16 ∤ 9m+5`, i.e. `m ≢ 3 (mod 16)`
(`9^{-1} ≡ 9 (mod 16)`).  Exact below `2^14`: `test_min_gate_depths`.

COMPUTED (`test_gated_zero_sum_counts`, `test_gated_pairs`,
`test_gate_survivor_shares`, `test_end_gates_on_the_census`):

| bound, size | ungated | depth 1 | 2 | 3 | 4 | 6 |
|---|---|---|---|---|---|---|
| < 400, pairs | 83 | 11 | 4 | 1 | 1 | 0 |
| < 10 000, pairs | 2 109 | 277 | 93 | 35 | 18 | 7 |
| < 120, triples | 383 | 11 | 5 | 2 | 0 | 0 |
| < 400, triples | 4 701 | 169 | 61 | 27 | 1 | 0 |
| < 60, quadruples | 511 | 14 | 9 | 0 | 0 | 0 |
| < 100, quadruples | 2 737 | 124 | 9 | 0 | 0 | 0 |

No gated set is a chain.  Survivors at depth 4: the pairs `{79, 161}`,
`{223, 449}`, `{295, 593}`, `{319, 641}`, `{967, 1937}`, …, and the one
triple below 400, `{31, 47, 161}` (drops `−16, −24, 40`).  Every gated pair is
`{2d − 1, 4d + 1}`: the larger member must be a fall source, `≡ 1 (mod 4)`,
and the fall source of `d` exceeds the rise source `2d − 1` only at height 2
(for `d ≥ 4`).  The smallest `d` giving a gated pair is 4 at depths 1–2, 40
at 3–4, 112 at 5–6, 592 at 7–8; below `d = 200 000` there are 22 222, 7 408,
2 776, 1 340, 570, 335, 221, 128 of them at depths 1–8.  Among odd numbers
below `2^16` the minimum gate passes 0.3333, 0.2500, 0.1354, 0.0597 at depths
1, 2, 4, 8 and the maximum gate 0.1111, 0.0556, 0.0183, 0.0041.  Every cycle
of the 3n+q census passes both gates, with its own `q`, at depth 6.  Whether
some depth excludes every gated pair is not settled here: for large members
both gates are conditions on residues (the forward halvings are fixed by the
class mod a power of 2, the backward chain by the class mod a power of 3), so
this is the sieve of the main page seen from a zero-sum set instead of a
chain, and it inherits the sieve's limits (`docs/GROUND_TRUTH.md`, the
equivalence theorem).

**Why zero-sum is so much weaker than chain.** The sum constrains only the
multiset of drops; a chain fixes each member from the previous one,
`nᵢ₊₁ = nᵢ − f(nᵢ)`, leaving one number free, and its closure is the cycle
equation `n₁(2^B − 3^L) = Σ 3^{L−1−i} 2^{B_i}` — the object of
`docs/LEDGER.md` §4 (the SAT box), `docs/LANDING.md` §1 (the chain closer) and
the multiplicative ledger.

## 5. Literature and novelty

* D2 is the standard description of `S` on residue classes mod `2^{x+1}`
  (Terras 1976; Lagarias 1985 §2.1) — CITED, not new.
* D3–D4 reorganise the inverse map `(2^x s − 1)/3` (Kaneda's `g_d`,
  `syracuse.py` docstring) by the drop instead of by the target.  Checked
  2026-09-23: the drop sequence `−2, 4, −4, 2, −6, 8, −8, 4, −10, 20, …`
  (odd `n = 3, 5, 7, …`) matches nothing in the OEIS; `2^x − 3` is OEIS
  A036563 and the exponents with `2^x − 3` prime (`3, 4, 5, 6, 9, 10, 12,
  14, 20, 22, 24, 29, 94, …`) are A050414; two web searches for the fiber
  statement found nothing.  The statement is a two-line consequence of the
  inverse map and we claim nothing beyond bookkeeping for it.
* D5, Z1–Z3 are telescoping and construction; Z4 is a special case of
  Steiner 1977; Z5's minimum gate is the stopping-time sieve of Terras 1976
  applied to the minimum, and its maximum gate is the repo's own sieve.
* The `q`-general remark (module only): `f_q(n) = 0` iff `(2^x − 3) | q`,
  i.e. the fixed points of `S_q` are `n = q/(2^x − 3)` — for `q = 5` the
  fixed points 1 (`x = 3`) and 5 (`x = 2`) of the census.

## 6. Verification

| claim | test |
|---|---|
| D1 sign/parity, closed form, `x ≥ 2 ⇒ 4f ≥ n − 1` | `test_d1_parity_and_sign`, `test_closed_form` |
| D2 classes for `x ≤ 14` vs brute force; the table; general `q` | `test_d2_*` |
| D3 fibers vs brute force for `|d| ≤ 2^14`; divisor count; general `q`; records; distribution | `test_d3_*` |
| D4 witnesses `x_max ≤ 10`, `958 208` has six sources | `test_d4_witnesses` |
| D5 telescoping `n < 20 001`; the six trajectories; the census balances; one lap for `q = 5` | `test_d5_*` |
| Z1–Z3 counts, pair structure, the family, chain = cycle on the census | `test_zero_sum_*`, `test_chain_iff_cycle_on_the_census` |
| Z4 | `test_no_two_cycle_in_drop_coordinates` |
| Z5 minimum gate depths 1–2, no backward half; both gates on the census at depth 6; gated counts; gated pairs `{2d−1, 4d+1}`, smallest `d`, 128 below 200 000 at depth 8; survivor shares | `test_min_gate_depths`, `test_end_gates_on_the_census`, `test_gated_zero_sum_counts`, `test_gated_pairs`, `test_gate_survivor_shares` |

Run: `cd python && uv run pytest tests/test_drop.py` (26 tests).
