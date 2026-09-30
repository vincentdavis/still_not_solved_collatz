# The loop sieve — crossing out numbers that cannot sit in a second loop

**Provenance.** A user-led pass of 2026-09-30 (`web/loopsieve.html`,
`python/collatz_maxodd/loopsieve.py`, `python/tests/test_loopsieve.py`), on the
user's rule *"if `3n+1 = 2^i`, then `n` falls into the known loop
`1 → 4 → 2 → 1` and cannot be in another loop"*, and the request to keep
exploring ways to eliminate sets of numbers.  Labels: **PROVED** (complete
proof here), **COMPUTED** (exact, pinned by a test), **CITED**.  The page is
**`3n+1` only**; general `q` appears only as a harness (`test_filter_a_q5_harness`).
Nothing in this document is claimed new (§7).  The backward tree of 1 is
already on the main page ("Every path back from 1 has the same closed form",
with the verdict that describing it is the conjecture restated); this document
measures it as a sieve and asks what else can cross numbers out.

Setting: `S(n) = (3n+1)/2^x`, `x = v₂(3n+1)`, on odd `n`.  A *loop* is a
closed orbit of `S`; the known loop is `{1}`.  A number is *crossed out* when
it provably lies in no loop other than `{1}`.

**The membership lemma** (used by every rule below).  If `n` is in a loop `C`
then `S(n) ∈ C`, since a loop is a closed orbit.  Hence if `S(n)` lies in no
loop other than `{1}`, neither does `n` (for `n ≠ 1`: `n ∈ C` would put
`S(n)` in `C ≠ {1}`).

---

## 1. The user's rule and its closure (PROVED)

**L1 (pass one).** `3n + 1 = 2^i` iff `n = (4^k − 1)/3`: `2^i ≡ 1 (mod 3)`
iff `i` is even.  For `k ≥ 2` these are `5, 21, 85, 341, 1365, 5461, 21845,
87381, …` (OEIS A002450, whose entry notes the 3x+1 link), in binary
`101, 10101, 1010101, …`; each has `S(n) = 1`, so by the lemma none is in a
loop other than `{1}`, and `n ≠ 1`.  `(4^k − 1)/3 ≡ k (mod 3)`, so
`k ≡ 0 (mod 3)` gives the dead ends `21, 1365, 87381, …`.

**Doorways (PROVED).** On any orbit that reaches 1 the last odd number before
1 is a pass-one number (it is an odd `n ≠ 1` with `S(n) = 1`).  **COMPUTED**
(`test_doorways`): over the odd `1 < n < 2^20`, doorway 5 carries 491 853
(93.8 %), 341 carries 19 819, 85 carries 12 317, 21 845 carries 231, 5 461
carries 42, 349 525 carries 21, and the dead ends 21, 1 365, 87 381 carry only
themselves; one number enters through 1 398 101.

**L2 (the closure).** Iterating the lemma from `{1}`: pass `d` crosses out
exactly the odd numbers that reach 1 in `d` odd steps (pass 0 is `n = 1`,
the known loop).  The union of all passes is the backward tree of 1; the
closed form of every path back from 1 (Böhm & Sontacchi 1978) is on the main
page.  **Pass two in closed form:** `n = (2^x (4^k − 1) − 3)/9` with
`k ≢ 0 (mod 3)`, `x` even for `k ≡ 1`, odd for `k ≡ 2` (because the target
`(4^k−1)/3 ≡ k (mod 3)`): `3, 13, 53, 113, 213, 227, …`; the formula
reproduces all 34 pass-two numbers below `2^20` (`test_pass_two_closed_form`).

**Bounded passes cross out a vanishing share (PROVED).**  If `n` reaches 1 in
`d` odd steps with `X` halvings, the product identity along the path gives
`2^X = 3^d n ∏(1 + 1/(3nᵢ)) ≤ 4^d n` (each factor is at most `4/3`).  So
`n < N` forces `X < log₂N + 2d`, and distinct paths are distinct words
`(x₁, …, x_d)` of positive integers with that sum:

    #{n < N crossed out at pass d}  ≤  C(⌊log₂N⌋ + 2d, d)  =  O((log N)^d).

Any fixed number of passes therefore crosses out a share of the odd numbers
below `N` that tends to 0.  **COMPUTED** (`test_pass_counts_are_polylogarithmic`):
below `2^20` passes 1–7 cross out 9, 34, 78, 176, 309, 508, 871 numbers
(bounds 22, 276, …).

**COMPUTED** (`test_last_survivors_and_means`, `test_survivors_below_1000`,
`test_pass_records`):

| `N` | last to be crossed out | at pass | mean pass |
|---|---|---|---|
| `2^10` | 871 | 65 | 22.21 |
| `2^12` | 3 711 | 87 | 27.49 |
| `2^14` | 13 255 | 101 | 32.04 |
| `2^16` | 52 527 | 125 | 36.49 |
| `2^18` | 230 631 | 164 | 41.36 |
| `2^20` | 837 799 | 195 | 46.15 |

The mean grows by about 2.4 passes per bit, the heuristic `1/(2 − log₂3)` of
an average odd step losing `2 − log₂3 = 0.415` bits.  Below 1000 the odd
numbers still standing after passes 0, 1, 2, 5, 10, 20, 40, 60, 64, 65 (with
the multiples of 3 crossed out at pass 0) are 332, 329, 324, 296, 231, 140,
78, 3, 1, 0; the last three are 703, 871, 937.  The pass records are OEIS
A033958/A033959 (`1, 3, 7, 9, 25, 27, 73, 97, …` at passes
`0, 2, 5, 6, 7, 41, 42, 43, …`).

## 2. The dead ends (PROVED — T0)

**L0.** `3m + 1 ≡ 1 (mod 3)`, so no odd number maps to a multiple of 3, and a
multiple of 3 has no predecessor in any loop.  It is the only rule here that
removes a fixed share — a third of the odd numbers — at every size, without
following any orbit.  (The multiples of 3 are also leaves of the tree of 1
and are crossed out again at their own pass.)  Kaneda 2015 (GROUND_TRUTH T0).

## 3. Where the passes stop, and the shadow above (CITED / PROVED / COMPUTED)

**L3 (CITED).** Every `n < 2^71` reaches 1 (Barina 2025;
`cycleeq.BARINA_2025_PAPER_LIMIT`).  So every pass has been run, by computer,
on every number below `V = 2^71`.

**L4 (the shadow).**  Above `V`, a number is crossed out as soon as its orbit
dips below `V`.  For odd `n` with halving word `(x₁, …, x_k)` and
`X_j = x₁ + … + x_j`, the product identity gives
`S^j(n) = 3^j n 2^{−X_j} ∏_{i<j}(1 + 1/(3nᵢ))`, and while the orbit is above
`V` the product lies in `[1, (1 + 1/(3V))^j]`.  So with `n = V·2^h`, the
orbit has dipped by step `k` iff `X_j > h + j log₂3` for some `j ≤ k`, up to
an error below `j/(2V)` bits.  The odd numbers with a given word form one
class mod `2^{X_k+1}` (Terras 1976), a share `2^{−X_k}`.  So the share still
standing after `k` odd steps is the exact word sum computed by
`shadow_survival(h, k)`: a dynamic program over `X` with the cap
`2^{X_j − h} ≤ 3^j`.  **COMPUTED** (`test_shadow_word_model_matches_numbers`):
the model equals brute force exactly for odd `n` just above `2^40` (`h = 0`,
`k ≤ 6`: `1/2, 3/8, 1/4, 13/64, 19/128, 1/8`) and just above `2^42`
(`h = 2`, `k ≤ 4`).

Share crossed out, `h` bits above `V`, after `k` odd steps (**COMPUTED**,
`test_shadow_table`):

| `h` \ `k` | 1 | 2 | 5 | 10 | 20 | 50 | 100 | 200 | 400 |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 0.5000 | 0.6250 | 0.8516 | 0.9355 | 0.9807 | 0.9987 | 1.0000 | 1.0000 | 1.0000 |
| 1 | 0.2500 | 0.3750 | 0.6914 | 0.8527 | 0.9531 | 0.9966 | 0.9999 | 1.0000 | 1.0000 |
| 5 | 0.0156 | 0.0391 | 0.2036 | 0.4501 | 0.7549 | 0.9754 | 0.9992 | 1.0000 | 1.0000 |
| 10 | 0.0005 | 0.0018 | 0.0252 | 0.1228 | 0.4170 | 0.8995 | 0.9958 | 1.0000 | 1.0000 |
| 20 | 0.0000 | 0.0000 | 0.0002 | 0.0031 | 0.0504 | 0.5517 | 0.9580 | 0.9998 | 1.0000 |
| 40 | 0.0000 | 0.0000 | 0.0000 | 0.0000 | 0.0001 | 0.0385 | 0.5628 | 0.9911 | 1.0000 |
| 60 | 0.0000 | 0.0000 | 0.0000 | 0.0000 | 0.0000 | 0.0004 | 0.1099 | 0.8934 | 1.0000 |

Steps needed for 50 % / 99 % / 99.9 %: `h = 0`: 1 / 27 / 54; `h = 10`:
23 / 87 / 123; `h = 20`: 47 / 127 / 169; `h = 40`: 95 / 198 / 246; `h = 60`:
144 / 264 / 317.  The `k = 1` column is the user's rule relaxed:
`3n + 1 = 2^i · s` with `s < 2^71`.

**The stragglers (PROVED / COMPUTED).**  For every `h` the share standing
tends to 0: `h + j log₂3 − X_j` is a random walk with mean step
`log₂3 − 2 < 0`.  Its exponential rate is
`min_t 3^t/(2^{t+1} − 1) = λ/3 = 0.946504…`, with `λ = α^α/(α − 1)^{α−1}`,
`α = log₂3` (the minimum sits at `2^{t+1} = α/(α−1)`, where the expression
equals `λ/3` exactly).  Numerically the exact survival decays at 0.946545
over `k = 600 … 1200` once the ballot factor `k^{−3/2}` is removed
(`test_shadow_rate_is_lambda_over_three`).  It is the same constant as the
repository's tail-rate upper bound (`docs/EXPLORE.md`; `docs/WORDS.md`, the
live mass `~ (λ/3)^i`): both are the words under the cap `B_j ≤ j log₂3`,
weighted `2^{−B}`.  The stragglers are whole residue classes — `n ≡ −1 (mod 2^{j+1})`
rises `j` times in a row — so the shadow never covers everything, and it is a
**density** statement: strategy-filter test D.

## 4. No remainder rule beyond the multiples of 3 (PROVED / COMPUTED)

**L5.** For every `a, b ≥ 0` and every `r` with `r` odd and `3 ∤ r` (when
`b ≥ 1`), some member of a rational 3n+1 loop lies in the class
`r (mod 2^a 3^b)`.  The rational loops are the periodic points
`c/(2^B − 3^L)`, one per halving word (Böhm–Sontacchi 1978; Lagarias 1990;
`rational_loop_point`).

*Proof.* 2-adic part: the odd numbers in `r mod 2^a` are those whose halving
word starts `(x₁, …, x_j)` (the longest prefix with `X_j + 1 ≤ a`) followed by
some `x_{j+1} ≥ a − X_j`.  The loop of the word `(x₁, …, x_j, a − X_j)`
starts with that prefix, so its first member is in the class (`B = a`).
3-adic part: `S^k(y) ≡ c_k 2^{−X_k} (mod 3^k)` for every `y` (the `3^k y`
term vanishes), so a loop member's class mod `3^b` depends only on the last
`b` letters of its word (docs/LANDING.md, definiteness).  Every unit class
mod `3^b` arises this way, because every odd `p ≢ 0 (mod 3)` has backward
chains of every length with no size bound (docs/LANDING.md E0).  Putting the
2-adic prefix first and a suitable 3-adic suffix last gives one word, and
its loop's first member lies in both classes.  Every rational loop member is
prime to 3 and odd (`c ≡ 2^{X_{L−1}} (mod 3)`), so the multiples of 3 are
never hit. ∎

**COMPUTED** (`test_rational_loops_cover_every_open_class`): every open class
mod `2^a 3^b`, `a ≤ 7`, `b ≤ 3`, is hit by loops with at most `B` halvings, `B`
first sufficient: `a` for `b = 0`; `a + 1` for `b = 1`; 5, 7, 8, 9, 10, 11, 12
for `b = 2`; 8, 9, 11, 12, 13, 14, 15 for `b = 3` (`a = 1 … 7`).  Examples
(`test_loop_through_class_examples`): `−1` lies in `15 (mod 16)`;
`−7` in `29 (mod 36)` and `5 (mod 12)`, the classes where a positive loop's
largest member must lie; `−29/11` in `17 (mod 36)`; `1/5` in `13 (mod 32)`;
`37/5` in `65 (mod 144)`.  Among loops with `B ≤ 15` the only positive
integer member is 1 (`test_positive_integer_rational_loops`).

**Consequence (filter test C).**  An argument that uses only remainders
applies verbatim to rational loops, which pass through every class except
the multiples of 3.  So no such argument can cross out a further class.
Every rule that crosses out more has to use the *size* of the numbers.  The
passes and the shadow do; T1–T8 and the minimum gates do too, through the
order `≤ M` and `≥ m` (§5).

## 5. Roles, not membership

The sieves of the main page (largest member `M`) and of `docs/DROP.md` Z5
(smallest member `m`) do not cross out members; they restrict where the
largest and smallest can be.  Shares of odd numbers below `2^16` passing at
depth 1, 2, 4, 8: largest 0.1111, 0.0556, 0.0183, 0.0041; smallest 0.3333,
0.2500, 0.1354, 0.0597 (`test_drop.py::test_gate_survivor_shares`).

## 6. Strategy-filter verdict (docs/FILTER.md)

| rule | A (q = 5) | B (q = −1) | C (completion) | D (density) | E (uniform) | verdict |
|---|---|---|---|---|---|---|
| passes: cross out what reaches 1 | ✓ sound (never crosses out a q = 5 loop member, `test_filter_a_q5_harness`) | ✓ | ✓ uses orbits of integers | ✓ exact per number | ✗ a semi-decision procedure | sound and complete for each number it reaches; cannot finish: its union is the verification |
| shadow of `2^71` | ✓ | ✓ | ✓ uses size | ✗ density only | — | measurement; never excludes a finite loop |
| remainder-only rules beyond T0 | — | — | ✗ (L5) | — | — | impossible |

What can finish has to couple size with the arithmetic of 2 and 3.  Hercher's
length floor (`docs/LEDGER.md` §6) and the Simons–de Weger circuit bounds do
this, and they eliminate loop *lengths*, not numbers.

## 7. Literature and novelty

* L0: Kaneda 2015.  L1: OEIS A002450.  L2: the backward tree of 1 (Lagarias
  1985; Wirsching, LNM 1681, 1998); closed form Böhm & Sontacchi 1978; the
  tree's counting function is at least `x^{0.84}` (Krasikov & Lagarias,
  *Acta Arith.* 109 (2003)), which is about all depths, not bounded ones.
  Records: OEIS A033958/A033959.
* L3: Barina 2025.  L4: Terras 1976 (`h = 0` is the stopping time); the rate
  `λ/3` is the repository's own tail constant.
* L5: Lagarias 1990 (rational cycles); Bernstein & Lagarias 1996 (the 2-adic
  conjugacy), FILTER test C.
* New to the repository, all elementary: the doorway counts, the
  `C(log₂N + 2d, d)` bound, the shadow table, the identification of the
  shadow's rate with `λ/3`, and L5 as a statement about membership.

## 8. Verification

| claim | test |
|---|---|
| L1 list, binary form, dead ends; doorways below `2^20` | `test_pass_one_is_exactly_the_powers_of_two`, `test_doorways` |
| L2 table vs iteration; closure recursion; last survivors, means; survivors below 1000; pass counts; pass-two closed form; records | `test_odd_steps_table_matches_iteration`, `test_closure_rule`, `test_last_survivors_and_means`, `test_survivors_below_1000`, `test_pass_counts_are_polylogarithmic`, `test_pass_two_closed_form`, `test_pass_records` |
| L4 exact small values; word model = numbers near `2^40`, `2^42`; table; steps to 50/99/99.9 %; rate `λ/3` | `test_shadow_exact_small`, `test_shadow_word_model_matches_numbers`, `test_shadow_table`, `test_shadow_rate_is_lambda_over_three` |
| L5 loops are loops; coverage `a ≤ 7`, `b ≤ 3`; examples; only positive integer member is 1 | `test_rational_loops_are_loops`, `test_rational_loops_cover_every_open_class`, `test_loop_through_class_examples`, `test_positive_integer_rational_loops` |
| filter test A harness | `test_filter_a_q5_harness` |

Run: `cd python && uv run pytest tests/test_loopsieve.py` (18 tests).
