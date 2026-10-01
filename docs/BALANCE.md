# Loops near perfect balance — the cycle equation in Q(2^(1/L))

**Provenance.** A user-led pass of 2026-09-30 / 10-01 (`python/collatz_maxodd/balance.py`,
`python/tests/test_balance.py`, `web/balance.html`).  The question was whether the idea
behind Knight's theorem on balanced loops can be pushed one step further.  Labels: **PROVED**
(complete proof here), **COMPUTED** (exact, pinned by a test), **CITED**.  Classical Collatz
only (`q = 1`); the 3n+q census is a harness.

**Credit.** The balanced case is **Kevin Knight's**: *Collatz high cycles do not exist*,
Discrete Mathematics 349 (2026) 114812 (preprint HAL hal-04261183, 2023).  He calls the
balanced loop the *high cycle*.  Halbeisen and Hungerbühler (*Acta Arith.* 78 (1997)
227–239) showed it has the largest smallest member among all loops with the same counts, and
Knight showed it is never integral.  Section 2 gives a second proof of Knight's theorem.
Lemmas 1 and 2 are standard facts — an index computation and a substitution — arranged for
this purpose; Corollary 4, Theorem 1 and the table of section 4 were not found in the sources
checked (section 6).  An independent referee pass re-derived every step and found no
mathematical error; its corrections to the presentation are folded in.

**A correction to the conversation.**  Before this write-up, the one-swap estimate was quoted
with an 8 % margin per member and Smyth's constant.  That estimate used the element
`2 + θ^e − θ^(e+1)`, which equals `θ^e (θ^k − θ + 1)` and so carries a factor `θ^e` of norm
`±2^e`.  That factor is invisible to the odd modulus `d`.  With it removed (Lemma 6) the
margin is large and the proof needs only Parseval's identity and a classical lower bound for
`2^B − 3^L`.

---

## 0. Setting

A positive loop of `3n+1` with `L` odd members `n_0, …, n_{L−1}` and halving word
`w = (x_0, …, x_{L−1})`, `n_{i+1} = (3n_i + 1)/2^{x_i}`, has `B = Σ x_i` halvings and, with
`X_i = x_0 + … + x_{i−1}` and `d = 2^B − 3^L > 0`, the cycle equation (Böhm–Sontacchi 1978)

    n_0 = c(w)/d,      c(w) = Σ_{i<L} 3^(L−1−i) 2^(X_i).

The product identity `2^B = Π(3 + 1/n_i)` gives `log₂3 < B/L < 2` for every positive loop
other than `{1}`.  A cyclic word is *balanced* when any two of its cyclic factors of equal
length have sums differing by at most 1.  For `gcd(L, B) = 1` the balanced cyclic words of
length `L` and sum `B` are exactly the rotations of the **Christoffel word**
`x_i = ⌊(i+1)B/L⌋ − ⌊iB/L⌋` (Lothaire, *Algebraic Combinatorics on Words*, ch. 2; Berstel,
Lauve, Reutenauer, Saliola 2009).  For `log₂3 < B/L < 2` its letters are 1 and 2, with
`b := B − L` twos; `b/L > log₂3 − 1 > 1/2`.

## 1. The cycle equation in `Q(2^(1/L))` (PROVED)

Let `gcd(L, B) = 1`, `θ = 2^(1/L)`, `K = Q(θ)` (degree `L`: `x^L − 2` is Eisenstein),
`O = Z[θ]`, `I = (θ^B − 3)·O`.

**Lemma 1.** `O/I ≅ Z/d`, the isomorphism sending `θ` to `θ₀ = 3^u 2^(−v) mod d`, where
`uB − vL = 1`.

*Proof.* In `O/I`: `θ^B = 3` and `θ^L = 2`, so `2^B = θ^(LB) = 3^L`: `d = 0`.  As `d` is odd
and prime to 3, both 2 and 3 are units of `O/I`; so is `θ`, since `θ·θ^(L−1) = 2`.  Hence
`θ = θ^(uB−vL) = 3^u 2^(−v)` is the image of an integer, and `Z/d → O/I` is onto.
`|O/I| = |N_{K/Q}(θ^B − 3)|`: for any order, the index of `αO` is `|N(α)|`, the determinant of
multiplication by `α` in a `Z`-basis.  And `|N(θ^B − 3)| = |Π_j (ζ^(jB) θ^B − 3)| =
|3^L − 2^B| = d`, because `ζ^(jB)` runs over all `L`-th roots of unity when `gcd(B, L) = 1`.
An onto map between two sets of `d` elements is a bijection.  ∎

Coprimality is essential: with `g = gcd(L, B) > 1`, `|O/I| = (2^(B/g) − 3^(L/g))^g`, which
differs from `d` in general (for `(L, B) = (10, 16)`: 169 against 6 487).

**Lemma 2 (θ-identity).** For every word `w` of length `L` and sum `B`,
`c(w) ≡ Σ_i θ^(B(L−1−i) + L X_i) (mod I)`, an element of `O`.  In `O/I`, where `θ` is
invertible, this reads `c(w) = θ^(B(L−1)) · A(w)` with `A(w) = Σ_i θ^(−D_i)`,
`D_i = iB − L X_i`.

*Proof.* Replace `3` by `θ^B` and `2^(X_i)` by `θ^(L X_i)`.  ∎

`D_i/L = iB/L − X_i` is how far the straight line from `(0, 0)` to `(L, B)` runs above the
halving path at step `i`, so `A(w)` adds up powers of 2 read off the path's deviations from
the line.  The terms `θ^(−D_i)` with `D_i > 0` are not in `O` (`θ` is not a unit of `O`, its
norm is `±2`); all statements involving `A(w)` are read in `O/I`.

**Corollary 3 (the norm test).** Put `P_w(θ) = θ^(max D)·A(w) = Σ_i θ^(max D − D_i) ∈ O`.  If
`d | c(w)` then `d` divides the odd part of `N_{K/Q}(P_w(θ))`.  So if that odd part is positive
and smaller than `d`, no positive loop has the word `w`.

*Proof.* `d | c(w)` puts `c(w)` in `I` (Lemma 1: `I ∩ Z = dZ`), hence `P_w(θ) ∈ I`, since
`P_w ≡ θ^(max D − B(L−1)) c(w)` in `O/I`.  Then `P_w(θ) = (θ^B − 3)β` with `β ∈ O` and
`N(P_w) = ±d·N(β)`, `N(β) ∈ Z`; `d` is odd.  `P_w(θ)` is a sum of positive reals, so its norm
is not 0.  ∎

`d | c(w)` is exactly the integrality of the loop: from `2^(x_i) N_{i+1} = 3N_i + d`
(`N_i` the numerator of the `i`-th member), `d | N_0` makes every member an integer, odd
because `c ≡ 1 (mod 2)`.  The test is a property of the cyclic word: rotating `w` multiplies
`A(w)` by a power of `θ` and leaves `P_w` unchanged.

COMPUTED (`test_theta_identity_on_random_words`, `test_norm_divisibility_holds_on_real_cycles`):
the identity on 1 000+ random words, and the divisibility `d | q^L N(P_w)` — the same argument
with `q·c(w) ≡ 0` — on all 709 cycles of the 3n+q census with coprime counts and `L ≤ 30`.

## 2. Balanced loops (CITED: Knight; second proof PROVED)

**Theorem 0 (Knight).** Let `L ≥ 2`, `gcd(L, B) = 1` and `2^B > 3^L`.  The balanced loop of
slope `B/L` is never integral.  (Both hypotheses matter: `(L, B) = (2, 4)` gives the word
`(2, 2)`, which is `{1}` run twice, and `(2, 3)` gives `d = −1` and the negative loop
`{−5, −7}`.)

Knight's proof uses the reversal symmetry of Christoffel words: two members of the high cycle
have parity vectors `1u0` and `0u1`, and `3f(v_h) − f(v_h^R) + 1 = 2^(k−1)/(2^k − 3^x)`,
which no odd denominator can divide.

*Second proof.* For the Christoffel word `D_i = iB mod L` runs over `0, …, L−1`, so
`A = Σ_{r<L} θ^(−r) = θ^(1−L)(1 + θ + … + θ^(L−1)) = θ^(1−L)/(θ − 1)`, because
`(θ − 1)(1 + θ + … + θ^(L−1)) = θ^L − 1 = 1`.  So `A` is a unit times a power of `θ`; it lies
in no prime ideal dividing `I`, and `c` is coprime to `d`.  The loop is then integral only
when `d = 1`.  And `2^B − 3^L = 1` forces `B` even (mod 3), then
`(2^(B/2) − 1)(2^(B/2) + 1) = 3^L` makes both factors powers of 3 differing by 2, so they are
1 and 3: `(L, B) = (1, 2)`, the loop `{1}`.  The decisive fact is `2 − 1 = 1`.  ∎

The number field is not even needed here: in `Z/d`, `θ₀ = 3^u 2^(−v)` satisfies
`(θ₀ − 1)(1 + θ₀ + … + θ₀^(L−1)) = θ₀^L − 1 = 1`, so `c` is a unit modulo `d` by plain modular
arithmetic.

The second proof gives slightly more: the balanced loop's fraction `c/d` is always in lowest
terms, so a balanced loop of `3n+q` exists exactly when `d | q`.  Knight's identity gives
this too, in two lines: from `2^(x_i) N_{i+1} = 3N_i + d`, a prime dividing `d` divides all of
a loop's numerators or none, and it would have to divide `2^(k−1)`.  COMPUTED
(`test_balanced_numerator_is_a_unit_and_coprime_to_d`, `test_balanced_integral_only_when_d_is_one`):
`gcd(c, d) = 1` for every coprime `(L, B)` with `L ≤ 160` and `log₂3 < B/L < 2`.

**Corollary 4 (spread).** Every positive loop of `3n+1` other than `{1}` has largest member
`M ≥ 1.8614·m`, `m` the smallest.

*Proof.* For a window of `ℓ` steps from member `n_i`,
`2^s = 3^ℓ (n_i/n_{i+ℓ}) Π_j (1 + 1/(3n_j))`, so its halving sum `s` lies in
`(ℓ log₂3 − R, ℓ log₂3 + R + ℓδ]`, `R = log₂(M/m)`, `δ = log₂(1 + 1/(3m))`.  Two windows of
equal length differ by less than `2R + Lδ`, and `L ≤ (M − m)/2 + 1` gives
`Lδ ≤ (2^R − 1)/(6 ln 2) + 1/(3m ln 2)`.  If `R + (2^R − 1)/(12 ln 2) < 1 − 1/(6m ln 2)` the
word is balanced.  A loop's word is primitive: if it were `u^k`, `k ≥ 2`, the loop point of
`u^k` equals that of `u` and the loop would have only `|u|` members.  A balanced word with
`g = gcd(L, B) > 1` is not primitive: its windows of length `L/g` have the integer mean `B/g`
and take at most two consecutive values, so they are all equal, and `x_(i+L/g) = x_i`.  So the
word is a rotation of the Christoffel word with `gcd(L, B) = 1`, and Theorem 0 says it is not
integral.  The threshold is `R* = 0.896432`, `2^(R*) = 1.861456`; it needs only `m > 4 769`,
far below the verified `m > 2^71` (Barina 2025), where the `m`-term is about `10^(−22)`.  ∎  COMPUTED
(`test_small_spread_forces_balance_on_the_census`): every census cycle whose spread meets the
hypothesis has a balanced word.  Not in Knight's paper; elementary, possibly folklore.

## 3. One swap from balance (PROVED, given the CITED bound of Ellison and a COMPUTED check for `L ≤ 17`)

A **one-swap word** comes from the Christoffel word (coprime `L, B`, `log₂3 < B/L < 2`) by
exchanging two cyclically adjacent, different letters.  Exchanging the last and first letters
gives the upper Christoffel word, a rotation of the balanced word; every other one-swap word
is an internal swap at positions `(i, i+1)`, `0 ≤ i ≤ L−2`, of the lower Christoffel word.

**Lemma 5 (where the swaps are).** With `D := D_{i+1} = (i+1)B mod L ∈ {1, …, L−1}`:
`x_i = 2` iff `D < b`, and `x_{i+1} = 2` iff `D ≥ L − b`.  Since `b > L/2`, the pair is
`12` iff `D ≥ b`, and `21` iff `D ≤ L − b − 1`.

*Proof.* `x_i = (B + D_i − D_{i+1})/L` and `D_{i+1} ≡ D_i + b (mod L)`, so `x_i = 2` exactly
when `D_i + b ≥ L`, i.e. when `D_{i+1} = D_i + b − L < b`.  The same with `i+1`.  ∎

**Lemma 6 (reduction).** For the internal swap at `(i, i+1)`, in `O/I` (where `θ` and
`θ − 1` are invertible):
* a `12 → 21` swap gives `c(w') ≡ θ^(B(L−1)) θ^(1−L) (θ−1)^(−1) · γ_e`, with
  `γ_e = θ^(e+1) − θ^e + 1`, `e = L − 1 − D ∈ [0, L − 1 − b]`;
* a `21 → 12` swap gives `c(w') ≡ θ^(B(L−1)) θ^(1−L) (θ−1)^(−1) θ^(−k) · η_k`, with
  `η_k = θ^k − θ + 1`, `k = D + 1 ∈ [2, L − b]`.

*Proof.* The swap changes only `X_{i+1}`, by `+1` or `−1`, so only `D_{i+1}` changes, to
`D − L` or `D + L`.  Hence `A(w') = θ^(1−L)/(θ − 1) + θ^(−D)` (using `θ^L − 1 = 1`) or
`θ^(1−L)/(θ − 1) − θ^(−D)/2 = θ^(1−L)/(θ − 1) − θ^(−D−L)`.  Multiplying by `(θ − 1)θ^(L−1)`
gives `1 + (θ − 1)θ^(L−1−D) = γ_e`, or `1 − (θ − 1)θ^(−D−1) = θ^(−k) η_k`.  The ranges are
Lemma 5.  ∎

Each `D ∈ [1, L−1]` occurs once, so there are `2(L − b) − 1` internal swaps.  Two of them add
nothing new: the `e = 0` swap gives another rotation of the balanced word (`γ_0 = θ` is a
unit), and the `e = 1` and `k = 2` swaps give the same cyclic word (`γ_1 = η_2`).  So there
are `2(L − b) − 3` distinct unbalanced cyclic words at distance 1 — the distance-1 column of
section 4.  The counts 159, 2 059 and 3 034 below are of internal swaps.

**Theorem 1.** Let `L ≥ 2`, `gcd(L, B) = 1`, `log₂3 < B/L < 2`.  No one-swap word of slope
`B/L` is the halving word of a positive integer loop of `3n+1`.

Every one-swap cyclic word is covered: swaps commute with rotations, integrality does not
depend on the rotation, and the wrap-around swap is a rotation of the balanced word.

*Proof.* By Lemmas 1 and 6 a loop would put `γ = γ_e` or `γ = η_k` in `I`, so `d | N(γ)`
(as in Corollary 3), with `N(γ) ≠ 0` because `γ(θ) > 0`.

*Upper bound for the norm (Parseval).*  For `g(z) = Σ c_m z^m` with distinct exponents
`0 ≤ m < L`, the conjugates `z_j = ζ^j θ` satisfy `(1/L) Σ_j |g(z_j)|² = Σ_m c_m² θ^(2m)`
(orthogonality of the characters `j ↦ ζ^(jm)`), so by the AM–GM inequality
`|N(g(θ))| = Π_j |g(z_j)| ≤ (Σ_m c_m² θ^(2m))^(L/2)`.  Every exponent in `γ_e` and `η_k` is at
most `L − b`, and `θ^(2(L−b)) = 4^(2 − B/L) < 4^(2 − log₂3) = 16/9`.  So
`|N(γ_e)| < (1 + 32/9)^(L/2) = (41/9)^(L/2)` for `e ≥ 1` (and `|N(γ_0)| = |N(θ)| = 2`), and
`|N(η_k)| ≤ (1 + 4^(1/L) + 16/9)^(L/2) ≤ (41/9)^(L/2)` for `L ≥ 3`.  In all cases
`|N(γ)| < 2.1344^L`.

*Lower bound for `d` (CITED).*  `2^B − 3^L > 2.56^L` whenever `2^B > 3^L` and `L ≥ 18`
(Knight's Lemma 3.3, from Ellison 1971: `2^B − 3^L > 2^B e^(−B/10)` for `B > 27`).

So `0 < |N(γ)| < d` for `L ≥ 18`, and `d` cannot divide `N(γ)`.  For `L ≤ 17` the 159
one-swap words were checked directly: `d ∤ c(w')` (`test_small_lengths_directly`).  For
`L = 2` there is no admissible `B`.  ∎

**Remarks.**
* The only deep input is the lower bound for `2^B − 3^L`, and only for `B = ⌊L log₂3⌋ + 1`:
  for larger `B`, `d > 3^L` already.  Ellison's statement is confirmed through a second
  source, Rozier and Terracol (arXiv 2502.00948, appendix B).  Rhin's bound (Simons–de Weger
  2005, Lemma 12) would also do, but only together with a finite check: it gives
  `d > (41/9)^(L/2)` from `L > 252` on.  Numerically the smallest `d` exceeds `2.56^L` for every
  `18 ≤ L ≤ 6 000` and fails at `L = 17`, so the direct check for `L ≤ 17` is genuinely needed
  on this route.
* The theorem is about `q = 1`.  For `3n+13`, where `2^8 − 3^5 = 13`, both the balanced loop
  `319 → 485 → 367 → 557 → 421` and the one-swap loop `283 → 431 → 653 → 493 → 373` exist
  (`test_q13_has_balanced_and_one_swap_loops`).
* COMPUTED: Lemma 6 on 2 059 one-swap words (every coprime `(L, B)`, `L ≤ 40`); exact norms
  (Bareiss) of all 3 034 one-swap elements with `3 ≤ L ≤ 45`, each below `d` in odd part and
  below its Parseval bound; the cited inequality `d > 2.56^L` checked exactly for
  `18 ≤ L < 1500` at `B = ⌊L log₂3⌋ + 1`.  Outside the suite, all 11 389 one-swap words with
  `L ≤ 70` pass the exact norm test, and the referee pass checked directly that all
  60 150 617 one-swap words with `3 ≤ L ≤ 1200` are non-integral, without Parseval or
  Ellison (not pinned in the suite).

## 4. How far the norm test reaches (COMPUTED)

Corollary 3 applies to every word.  Among the primitive cyclic words made of 1s and 2s with
the balanced counts, grouped by how many adjacent swaps separate them from the balanced word,
the share for which the exact norm test is conclusive (`test_reach_profiles` pins the first
two rows):

| `L, B` | words | distance 1 | 2 | 3 | 4 | 5 | 6 | all |
|---|---|---|---|---|---|---|---|---|
| 13, 21 | 99 | 7/7 | 18/18 | 22/22 | 19/20 | 13/14 | 7/9 | 88.9 % |
| 18, 29 | 1 768 | 11/11 | 51/51 | 128/129 | 204/210 | 225/260 | 184/264 | 54.9 % |
| 21, 34 | 9 690 | 13/13 | 75/75 | 250/251 | 535/544 | 782/852 | 816/1061 | 39.3 % |
| 23, 37 | 35 530 | 15/15 | 100/100 | 391/392 | 991/1017 | 1721/1913 | 2116/2839 | 26.9 % |

Every two-swap word passes in all four cases.  The share then falls with distance, and words
far from balance have large norms, as random words do.  So the method rules out
patterns close to perfect balance — proved at distance 1 (Theorem 1), computed at distance 2
for these four pairs only (the suite pins `(13, 21)` and part of `(18, 29)`) — and not the whole
space, which matches the heuristic picture where integrality for a generic word is the whole
problem.  Everything here assumes `gcd(L, B) = 1`; when `gcd(L, B) > 1` no loop's word is
balanced, the most balanced primitive words are one swap from a power of a Christoffel word,
and Lemma 1 and Theorem 1 do not cover them.  The natural next theorem is two
swaps.  Most two-swap elements have Parseval mass `Σ c_m² θ^(2m)` below 9, which Rhin's bound
(`d ≥ 3^L e^(−13.3(0.46057 + log L))`) turns into a proof for large `L`; a few do not — 1 of
18 at `L = 13`, 1 of 75 at `L = 21`, 45 of 2 323 at `L = 89`, with mass up to 9.86 — and need
a sharper estimate than Parseval.

## 5. Strategy filter (`docs/FILTER.md`)

| test | verdict |
|---|---|
| A, q = 5 has loops | passes: the argument is `q`-sensitive; for `3n+13` the excluded shapes exist |
| B, sign | passes: it uses `2^B > 3^L` |
| C, completions | passes: it uses integrality through norms of algebraic integers, a global fact |
| D, density | passes: the statement is exact |
| E, uniformity | passes: it uses `2 − 1 = 1` (the unit `θ − 1`) and a bound for `2^B − 3^L` |

Like Steiner's theorem (one circuit) and Simons–de Weger's (few circuits), Theorem 1 excludes
a family of loop shapes, but at the opposite end: theirs are the most unbalanced loops,
these the loops next to perfect balance, for coprime `(L, B)`.

## 6. Literature and novelty

Knight (2023/2026) settles balanced loops; Halbeisen–Hungerbühler (1997) give their extremal
property; Fernández and Ibáñez (arXiv 2607.24844, 2026) study Christoffel words as extremal
structures.  None of these uses norms in `Q(2^(1/L))` or treats one-swap words; Lemmas 1 and 2 are
standard (an index computation and a substitution).  Corollary 4, Theorem 1 and the table of
section 4 were not found in these sources.  A wider literature search is needed before calling
Theorem 1 new mathematics; it is new to this repository.

## 7. Verification

| claim | test |
|---|---|
| Lemma 1 (`θ₀^L = 2`, `θ₀^B = 3` mod `d`) | `test_theta0_is_a_root_of_both_equations` |
| Lemma 2 on random words | `test_theta_identity_on_random_words` |
| Corollary 3 sound on real 3n+q loops | `test_norm_divisibility_holds_on_real_cycles` |
| Theorem 0: unit, lowest terms, integral only at `(1, 2)` | `test_balanced_numerator_is_a_unit_and_coprime_to_d`, `test_balanced_integral_only_when_d_is_one` |
| Corollary 4 threshold; census harness | `test_spread_threshold`, `test_small_spread_forces_balance_on_the_census` |
| Lemmas 5–6 | `test_swap_kinds_ranges_and_reduction` |
| Theorem 1: Parseval bound, small `L`, cited inequality, exact norms | `test_parseval_bound`, `test_small_lengths_directly`, `test_ellison_inequality_exactly_and_the_margin`, `test_exact_norm_test_on_all_one_swap_words` |
| section 4 | `test_reach_profiles` |
| filter test A | `test_q13_has_balanced_and_one_swap_loops` |

Run: `cd python && uv run pytest tests/test_balance.py` (14 tests).
