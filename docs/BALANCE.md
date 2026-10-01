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
this purpose; Corollary 4, Theorems 1, 2 and 3 and the table of section 6 were not found in
the sources checked (section 8).  Independent referee passes re-derived every step of Theorems 1
and 2.  Neither found an error in a theorem.  The second found that the citation of Rhin's
bound was justified by a false inequality; the bound actually used is Rhin's own statement,
and the citation is now exact.  All their corrections are folded in.  Theorem 3 (section 5)
has not been refereed yet.

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
section 6.  The counts 159, 2 059 and 3 034 below are of internal swaps.

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
  source, Rozier and Terracol (arXiv 2502.00948, appendix B).  Rhin's bound
  `B log 2 − L log 3 ≥ B^(−13.3)` (section 4) would also do, but only together with a finite
  check: it gives `d > (41/9)^(L/2)` from `L > 230` on.  Numerically the smallest `d` exceeds `2.56^L` for every
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

## 4. Two swaps from balance (PROVED, given the CITED bound of Rhin and a COMPUTED finite check)

**Corners.**  Draw the lower Christoffel word as a staircase.  Corner `p` (`0 ≤ p < L`) sits
between the letters `x_(p−1)` and `x_p`, cyclically (corner 0 between `x_(L−1)` and `x_0`), at
height `X_p`.  Its *level* `D_p = pB mod L` says how far it lies below the line, in steps of
`1/L`; every level `0, …, L−1` occurs once.  Put `a := L − b` (the number of 1s) and
`s := 2b − L` (the number of adjacent pairs `22`).  By Lemma 5, corner `p` is a `21` corner
when `D_p < a`, a `22` corner when `a ≤ D_p < b`, and a `12` corner when `D_p ≥ b`.  Lemma 5 is
stated for `p ≥ 1`; corner 0 has `D_0 = 0` and is the pair `x_(L−1) x_0 = 21`, which fits.
There is no `11` corner: the 1s are isolated, as `b > L/2`.

*Raising* corner `p` means `x_(p−1) += 1`, `x_p −= 1`.  For `p ≥ 1` it adds 1 to `X_p` and
changes no other `X_i`, so `D_p` becomes `D_p − L`.  For `p = 0` it is the same cyclic move
written in shifted coordinates; the proof of Lemma 8 treats it.  *Lowering* does the
opposite.  Exchanging the adjacent letters `x_(p−1) x_p` is exactly a raise (`12 → 21`) or a
lowering (`21 → 12`) of corner `p`.  Two swaps therefore either undo each other, which gives
back a balanced word (Theorem 0), or move two distinct corners by one step each.  Moving one
corner twice the same way would create a letter 0 or 3.  Swaps commute with rotations.  So
up to rotation every word two swaps from balance is obtained from the lower Christoffel word
by moving two distinct corners `p₁ ≠ p₂` by one step each, with every letter still 1 or 2.
The theorem needs only this inclusion.  The converse also holds: adjacent raises are reached
by swapping at `p` and then at `p+1`, adjacent lowerings at `p+1` and then at `p`
(`test_two_swap_words_are_the_distance_two_classes`).  In the picture: the loop's staircase
meets the balanced one at every corner but two, and those two are one step off.

**Lemma 7 (which corners move).**  A raised corner is a `12` corner and a lowered corner is a
`21` corner, with two exceptions for cyclically adjacent corners `p, p+1`.  Two adjacent
raises need `x_(p−1) = 1` and `x_(p+1) = 2`, so `x_p = 2`: a `12` corner followed by a `22`
corner.  Two adjacent lowerings need `x_(p−1) = 2` and `x_(p+1) = 1`: a `22` corner followed
by a `21` corner.  A raise next to a lowering never gives a word of 1s and 2s.

*Proof.* Moves at non-adjacent corners change disjoint pairs of letters, and each needs its
own pattern.  At adjacent corners the letters `x_(p−1), x_p, x_(p+1)` change by `(+1, 0, −1)`
for two raises, by `(−1, 0, +1)` for two lowerings, and by `(+1, −2, +1)` or `(−1, +2, −1)` for
a mixed pair, which would need a letter 3 or 0.  In the first two cases `x_p = 2`, since the
word has no `11`.  ∎

When `x_p = 2`, `D_(p+1) = D_p − a`.  So adjacent raises have `D_p ∈ [max(b, 2a), L − 1]` and
`D_(p+1) = D_p − a`, and adjacent lowerings have `D_p ∈ [a, min(b, 2a) − 1]` and
`D_(p+1) = D_p − a`.

**Lemma 8 (the element).**  Put `e = L − 1 − D` for a raised corner and `k = D + 1` for a
lowered one.  Then `d | c(w)` if and only if `q ∈ I`, where:

* **two raises**, `e₁ < e₂`: `q = 1 − θ^(e₁) + θ^(e₁+1) − θ^(e₂) + θ^(e₂+1)`;
* **two lowerings**, `k₁ > k₂`, `g = k₁ − k₂`: `q = θ^(k₁) − θ + 1 − θ^(g+1) + θ^g`;
* **a raise and a lowering**, `t = k + e`: `q = 1 − θ + θ^k − θ^t + θ^(t+1)`.

The ranges are `0 ≤ e ≤ a − 1` and `1 ≤ k ≤ a` for non-adjacent corners.  Adjacent raises
have `0 ≤ e₁ ≤ min(a, s) − 1` and `e₂ = e₁ + a`.  Adjacent lowerings have
`a + 1 ≤ k₁ ≤ min(b, 2a)` and `g = a`.  Every exponent is below `L`.

*Proof.* As in Lemma 6, `A(w) = Σ_corners θ^(−D)`.  A raise turns `θ^(−D)` into
`θ^(−D+L) = 2θ^(−D)`, adding `θ^(−D)`.  A lowering subtracts `θ^(−D)/2`.  Since
`(θ − 1)θ^(L−1)` times the balanced sum is `θ^L − 1 = 1`,

    (θ − 1) θ^(L−1) A(w) = 1 + Σ_raises (θ − 1) θ^e − Σ_lowerings (θ − 1) θ^(−k).

Multiplying by `θ^K`, with `K` the largest `k` (or 0), clears the negative powers and gives
`q`.  The factors `θ`, `θ − 1` and 2 are units modulo `I` (Lemma 1).  By Lemma 2,
`c(w) ≡ θ^(B(L−1)) A(w)`.  If corner 0 moves by `σ = ±1`, then `x_0` changes by `−σ`, every
`X_i` with `i ≥ 1` shifts by `−σ`, and `A(w)` equals `2^(−σ)` times the sum over corners
above.  This factor is again a unit.  So `d | c(w)` if and only if `q ∈ I`.  The ranges come
from Lemma 7.  ∎

**Lemma 9 (norm bound).**  Let `W(m) = θ^(2m) = 4^(m/L)` and suppose `s ≥ 2`, which holds
for `L ≥ 6`.  Every two-swap element satisfies `|N(q)| ≤ F^(L/2) / (1 − 2^(1−L))`, where `F`
is the largest of these six bounds:

| family | bound on the Parseval mass |
|---|---|
| two raises | `1 + 4W(a)` |
| two adjacent raises, `m = min(a, s)` | `1 + 2W(m) + 2W(m + a)` |
| two lowerings | `1 + W(1) + 3W(a)` |
| two adjacent lowerings | `1 + W(1) + W(min(b, 2a)) + W(a+1) + W(a)` |
| raise and lowering, `e = 0` or `k = 1` | `max(1 + W(1) + W(a+1), 1 + W(a) + W(a+1))` |
| raise and lowering, `e ≥ 1`, `k ≥ 2`, after multiplying by `1 + θ/2` | `(1 + W(1)/4 + W(2)/4) + W(a)(1 + W(1)/4) + W(2a−1)(1 + W(1)/4 + W(2)/4)` |

*Proof.* Use the Parseval and AM–GM bound from Theorem 1: for a real polynomial `g` with
distinct exponents in `[0, L)`, `Π_j |g(ζ^j θ)| ≤ (Σ c_m² W(m))^(L/2)`.  Two points make
it apply.

* *Coinciding exponents.*  In the two-raise and two-lowering families, no exponent carries
  more than two listed terms, and two terms that share an exponent have opposite signs.  For
  two raises, `e₁ = 0` cancels the 1 and `e₂ = e₁ + 1` cancels `θ^(e₁+1)` against `θ^(e₂)`.
  For two lowerings, `k₂ = 1` cancels `θ^(k₁)` against `θ^(g+1)`, and `g = 1` cancels `θ`.
  Merging two terms of opposite signs lowers the mass.  So the mass is at most the sum over
  the listed terms, and each bound follows from the largest allowed exponents.
* *Flattening.*  For a raise and a lowering the plain mass reaches
  `2 + 16/9 + 2(16/9)² ≈ 10.1`.  Multiply by `h = 1 + θ/2`.  Evaluating `x^L − 2` at
  `x = −2` gives `N(h) = Π_j (1 + ζ^j θ/2) = 1 − (−1)^L 2^(1−L)`.  Then
  `qh = (1 − θ/2 − θ²/2) + θ^k (1 + θ/2) + θ^t (−1 + θ/2 + θ²/2)`, with exponents up to
  `t + 2 ≤ 2a + 1 < L`, which uses `s ≥ 2`.  For `e ≥ 1` and `k ≥ 2` the only coinciding
  exponents are at `k = 2` (on `θ²`: `−1/2` and `+1`) and at `t = k + 1` (on `θ^(k+1)`: `+1/2`
  and `−1`), both of opposite signs, with `t ≤ 2a − 1`.  So `|N(q)| = |N(qh)|/|N(h)|` obeys the
  last row.  When `e = 0`, `q = θ^(k+1) − θ + 1`; when `k = 1`, `q = θ^(e+2) − θ^(e+1) + 1`.  Both
  have three distinct exponents, at most `a + 1`, which gives the fifth row.  ∎

At `B = ⌊L log₂3⌋ + 1`, as `L → ∞`, `W(a) → 16/9`, `W(s) → 4^(2 log₂3 − 3) ≈ 1.2656` and
`W(b) → 9/4`.  The six bounds tend to 8.111, 8.031, 7.333, 7.806, 4.556 and 8.463, all below
`9 = lim (3^L)^(2/L)`.  The flattened raise-and-lowering family is the largest.

**Theorem 2.** Let `L ≥ 2`, `gcd(L, B) = 1`, `log₂3 < B/L < 2`.  No word two swaps from a
balanced word of slope `B/L` is the halving word of a positive integer loop of `3n+1`.

*Proof.* If the two swaps undo each other the word is balanced, and Theorem 0 applies.
Otherwise two distinct corners move, and by Lemma 8 a loop puts `q` in `I`, so `d` divides
`N(q)`.  Here `q ≠ 0`: by the proof of Lemma 8 it equals `θ^K (θ − 1) θ^(L−1)` times the sum
`Σ_corners θ^(−D)`, whose terms are positive real numbers for `θ = 2^(1/L)`.  So `N(q) ≠ 0`,
hence `d ≤ |N(q)|`, and it suffices to show `|N(q)| < d`.  Write `β = b/L` and
`B₀ = ⌊L log₂3⌋ + 1`.

*(a) `B ≥ B₀ + 1` and `L ≥ 100`.*  Then `2^(B−1) > 3^L`, so `d > 2^(B−1)`.  Each bound of
Lemma 9 is at most `4^(2/L) G(β)`, with

* `G = 1 + 4^(2−β)` for two raises;
* `G = 1 + 2·4^μ + 2·4^(μ+1−β)`, `μ = min(1 − β, 2β − 1)`, for two adjacent raises;
* `G = 2 + 3·4^(1−β)` for two lowerings;
* `G = 2 + 4^(min(β, 2−2β)) + 2·4^(1−β)` for two adjacent lowerings;
* `G = 2 + 2·4^(1−β)` and `G = 1.5 + 1.25·4^(1−β) + 1.5·4^(2−2β)` for the two kinds of raise
  and lowering.

On `log₂3 − 1 < β < 1` every ratio `G/4^(1+β)` decreases, except for two adjacent raises,
whose ratio increases up to `β = 2/3` and then decreases (maximum 0.9142).  The overall
supremum is the raise-and-lowering value as `β → log₂3 − 1`: `8.46296/9 = 0.94033`.  So
`|N(q)| ≤ 4 G^(L/2)/(1 − 2^(1−L)) < 2^(B−1)` as soon as
`0.94033 < 4^(−3/L)(1 − 2^(1−L))^(2/L)`.  The right side is 0.95926 at `L = 100` and
increases with `L`.

*(b) `B = B₀` and `L ≥ 4 000`.*  Here `β < log₂3 − 1 + 1/L`, so every `G` is at most
8.46296; the next largest, for two raises, is below 8.12.  So
`|N(q)| ≤ 4·8.46296^(L/2)/(1 − 2^(1−L))`.

CITED (Rhin 1987, as stated by Rozier and Terracol, arXiv 2502.00948, Proposition 6.3): if
`u₀, u₁, u₂` are integers with `H = max(|u₁|, |u₂|) ≥ 2`, then
`|u₀ + u₁ log 2 + u₂ log 3| ≥ H^(−13.3)`.  With `(u₀, u₁, u₂) = (0, B, −L)` this gives
`Λ = B log 2 − L log 3 ≥ B^(−13.3)`, so `d = 3^L(e^Λ − 1) > 3^L B^(−13.3)`.

It remains to check `(L/2) log(9/8.46296) > log(4/(1 − 2^(1−L))) + 13.3 log B`.  Since
`B < L log₂3 + 1`, it is enough that

    σ(L) := (L/2) log(9/8.46296) − log(4/(1 − 2^(1−L))) − 13.3 log(L log₂3 + 1) > 0.

Now `σ(4 000) > 5.2`, and `σ` increases for `L > 2·13.3/log(9/8.46296) = 432.4`, because
its derivative exceeds `(1/2) log(9/8.46296) − 13.3/L`.  (With `log B` itself the inequality
fails at `L = 3 808` and holds for every `L` from 3 809 to `10^5`.)

A form often quoted for loops, `Λ > exp(−13.3(0.46057 + log L))` (Simons–de Weger 2005,
Lemma 12), is not used here.  It is slightly stronger than Rhin's statement for most `L`,
because `e^0.46057 = 1.584977` exceeds `log₂3 = 1.584963`.

*(c) The finite rest* is `L < 100` with any `B`, and `B = B₀` with `100 ≤ L < 4 000`: 3 622
coprime pairs.  COMPUTED (`test_theorem2_finite_range`):

* For 3 602 pairs, the exact `d` exceeds the bound of Lemma 9, by at least 0.079 in
  logarithm.
* The other 20 pairs are settled by a direct check: (3, 5), (4, 7), (5, 8), (8, 13), (11, 18),
  (13, 21), (14, 23), (17, 27), (18, 29), (22, 35), (27, 43), (29, 46), (32, 51), (39, 62),
  (41, 65), (46, 73), (63, 100), (70, 111), (94, 149), (147, 233).
* The direct check takes every pair of levels and every pair of signs.  It computes `A(w)`
  modulo `d` from `θ₀` with `O(L)` work, looking up the needed `θ₀^(−D)` in a table.  Its only
  zeros (6 for `L ≤ 30`) need a letter 0 or 3.  ∎

**Remarks.**
* Together with Theorems 0 and 1: no positive loop of `3n+1` has a halving word within two
  swaps of a balanced word of coprime slope.  Equivalently, no loop staircase misses the
  balanced corners in only one or two places, each by one step.
* The deep input is again a lower bound for `2^B − 3^L` at `B = B₀`.  Ellison's
  `d > 2.56^L` would need mass below `6.5536` and is too weak here.  Rhin's bound costs the
  finite check up to `L = 4 000`.
* COMPUTED, in the suite.  The counts are of two-corner moves `(p₁, s₁, p₂, s₂)`; several
  moves can give the same cyclic word.
  * Lemma 8's two congruences hold on all 2 438 moves with `L ≤ 24`.
  * The masses of all 93 417 moves with `6 ≤ L ≤ 60` are within the bounds of Lemma 9.
  * The exact norms of the elements of all 1 722 moves with `6 ≤ L ≤ 22` lie below their
    Parseval bounds, with odd part at most `0.216 d`, at `(17, 27)`.
  * The direct check agrees with `d | c(w)` word by word for `L ≤ 30`.
  * For every coprime pair with `L ≤ 40`, the moves give exactly the cyclic words at swap
    distance 2, found by a breadth-first search over actual swaps.
* COMPUTED, outside the suite.
  * The mass check also passed on 4 743 175 moves with `L ≤ 160`.
  * The direct check alone, with no norm bound, found no loop for `B₀` and `B₀ + 1` at every
    `L < 4 000` and for every `B` at `L < 200`: 9 668 coprime pairs.
  * The referee pass enumerated the whole finite range without Lemma 9 or `θ`: all 3 622
    pairs, 8 942 349 896 words obtained by two successive swaps, no loop.  It also found
    72 431 cyclic words at swap distance 2 for `3 ≤ L ≤ 60`, none a loop, and recomputed the
    1 722 exact norms by resultants, plus 8 233 more for `23 ≤ L ≤ 34`, the largest odd part
    being `0.426 d` at `(29, 46)`.
* Three swaps.  Three corner moves give seven-term elements.  At `(L, B) = (89, 142)` their
  Parseval masses reach 15.9, or 12.8 after the same flattening, over the 58 206 of 58 212
  moves whose flattened exponents stay below `L`; the other 6 wrap around and reach 20.2 and
  14.9.  These maxima are above 9, so the Parseval route stops at two swaps.  A sharper estimate of
  the norm cannot settle every three-swap word either.  COMPUTED
  (`test_three_swap_norm_can_exceed_d`): at `(233, 370)`, lowering the corner at level 95 and
  raising those at levels 141 and 187 gives a word of 1s and 2s whose element
  `1 − θ + θ^96 − θ^141 + θ^142 − θ^187 + θ^188` has an odd norm of about `11.33 d`.  The word
  is not a loop, because `d` does not divide that norm, but no bound on its size can show it.
  Section 5 shows what to count instead of swaps.

## 5. One run of levels (PROVED, given the CITED bound of Ellison and a COMPUTED check for `L ≤ 17`)

The number of swaps is not what the norm test measures.  Section 4 ended with a three-swap
word whose norm exceeds `d`.  This section shows the other side: some words many swaps from
balance are as easy as one swap.  They are the words whose moved corners form a *run* of
consecutive levels.  Corners, levels, raising and lowering are as in section 4.

**Profiles.**  Let `w'` be any word of length `L` and sum `B` with positive letters, and
`X'_p` its staircase.  Its *profile* against the lower Christoffel word is
`m_p = X'_p − X_p`, the displacement of corner `p`; `m_0 = 0`.  Write `m(D)` for the
displacement of the corner of level `D`, and `u_j = 2^(m(L−1−j))` for `0 ≤ j ≤ L − 1`.

**Lemma 10 (profile formula).**

    (θ − 1) θ^(L−1) A(w') = (2u_(L−1) − u_0) + Σ_{j=1}^{L−1} (u_(j−1) − u_j) θ^j.

*Proof.* `D'_p = pB − L X'_p = D_p − L m_p`, so `A(w') = Σ_p θ^(−D'_p) = Σ_D 2^(m(D)) θ^(−D)`
and `θ^(L−1) A(w') = Σ_j u_j θ^j`.  Multiply by `θ − 1` and use `θ^L = 2`.  ∎

The coefficient of `θ^j` is the difference between the weights `2^m` of the neighbouring
levels `L − j` and `L − 1 − j`.  The constant term compares level `L − 1` with level 0 one
full turn lower.  The balanced word has `u ≡ 1` and gives 1.  When every `m_p ≥ 0`, call the
right side `q_(w')`.  It lies in `O` and its exponents are `0, …, L − 1`.  Since `θ` and
`θ − 1` are units modulo `I`, Lemma 2 gives: `d | c(w')` if and only if `q_(w') ∈ I`.
Lemma 6 and the two-raise case of Lemma 8 are the profiles with one or two isolated levels
raised.

Every cyclic word has a rotation with `m_p ≥ 0` for all `p`.  Rotating by `r` turns `m_p`
into `m_(p+r) − m_r + ε`, with `ε = X_(p+r) − X_r − X_p ∈ {0, 1}`.  So it is enough to start
the word at a corner of least displacement.

**Corollary 11 (mass criterion).**  Let every `m_p ≥ 0` and

    M(w') = (2u_(L−1) − u_0)² + Σ_{j=1}^{L−1} (u_(j−1) − u_j)² 4^(j/L).

If `M(w')^(L/2) < d`, then `w'` is not the halving word of a positive integer loop.

*Proof.* `q_(w') ≠ 0`, because `A(w') > 0` at the real embedding.  A loop would put `q_(w')`
in `I`, so `d ≤ |N(q_(w'))|`.  And `|N(q_(w'))| ≤ M(w')^(L/2)` by the Parseval and AM–GM
bound of Theorem 1, whose only requirement is that the exponents be distinct and below
`L`.  ∎

`M` counts the places where neighbouring levels are moved differently, each with a weight
`4^(j/L)` between 1 and 4.  COMPUTED (`test_mass_criterion_is_sound_on_all_small_words`): on
all 85 358 words with `L ≤ 10` the criterion applies to 1 375, and never to a word with
`d | c(w)`.

**Runs.**  A *run* is a set of corners whose levels are consecutive: `D₁, D₁ + 1, …, D₂`,
with `1 ≤ D₁ ≤ D₂ ≤ L − 1`.  *Raising the run* means raising each of its corners by one
step: `m = 1` on the run and `m = 0` elsewhere.

**Lemma 12 (which runs give words).**  Raising the run `[D₁, D₂]` gives a word with positive
letters if and only if `D₁ ≥ a` or `D₂ = L − 1`.  Its letters are then 1, 2 or 3.  If
`D₁ ≥ b`, the word is the balanced word with the `12` pairs of the run swapped to `21`, a
word of 1s and 2s.

*Proof.* The new letter is `x'_p = x_p + m_(p+1) − m_p ≤ 3`.  It is 0 exactly when
`x_p = 1`, `m_p = 1` and `m_(p+1) = 0`.  By Lemma 5, `x_p = 1` if and only if `D_p < a`, and
then `D_(p+1) = D_p + b`.  So the word is valid if and only if every level `D < a` of the run
has `D + b` in the run.  If `D₁ ≥ a` there is no such level.  If `D₁ < a`, the level
`D = min(D₂, a − 1)` forces `D₂ ≥ a`, and then `D = a − 1` forces `D₂ ≥ a − 1 + b = L − 1`.
Conversely `[D₁, L − 1]` satisfies the condition.  If `D₁ ≥ b`, every corner of the run is a
`12` corner.  The corner after a `12` corner begins with a 2, so no two `12` corners are
adjacent, and the raises are swaps of disjoint pairs.  ∎

**Theorem 3 (one run).**  Let `L ≥ 2`, `gcd(L, B) = 1`, `log₂3 < B/L < 2`.  Raise one run of
levels of the lower Christoffel word by one step.  If the result is a word with positive
letters, then neither it nor any of its rotations is the halving word of a positive integer
loop of `3n+1`.

*Proof.* Integrality does not depend on the rotation.  Put `g = L − 1 − D₂` and
`f = L − D₁`, so `0 ≤ g < f ≤ L − 1`.  In Lemma 10, `u_j = 2` for `g ≤ j ≤ f − 1` and
`u_j = 1` otherwise, and `u_(L−1) = 1` because level 0 is not in the run.  So

    q = θ^f              if g = 0,
    q = 1 − θ^g + θ^f     if g ≥ 1.

If `g = 0`, `q` is a unit modulo `I`.  So `q ∉ I`, because `d > 1` by the proof of Theorem 0.
The word is then a rotation of the balanced word.

Let `g ≥ 1`.  By Lemma 12, `D₁ ≥ a`, so `1 ≤ g < f ≤ b`.  As `q > 0` at the real embedding,
`N(q) ≠ 0`, and a loop would give `d ≤ |N(q)|`.  Parseval gives
`|N(q)| ≤ (1 + 4^(g/L) + 4^(f/L))^(L/2) ≤ (1 + 4^((b−1)/L) + 4^(b/L))^(L/2)`.  Write
`β = b/L` and `B₀ = ⌊L log₂3⌋ + 1`.

*(a) `B ≥ B₀ + 1`.*  Then `d > 2^(B−1)`.  The mass is at most `1 + 2·4^β`, and
`(1 + 2·4^β)/4^(1+β) = 4^(−1−β) + 1/2 < 1/9 + 1/2 = 11/18`, because `β > log₂3 − 1`.  So
`|N(q)| < (11/18)^(L/2) 2^B ≤ 2^(B−1) < d`, since `(11/18)^(L/2) ≤ 1/2` for `L ≥ 3`.

*(b) `B = B₀` and `L ≥ 18`.*  Here `b < L(log₂3 − 1) + 1`, so `4^(b/L) < (9/4)·4^(1/L)` and
`4^((b−1)/L) < 9/4`.  The mass is below `13/4 + (9/4)·4^(1/18) < 5.681 < 6.5536 = 2.56²`.  So
`|N(q)| < 2.56^L < d` by Ellison's bound (section 3).

*(c) `B = B₀` and `L ≤ 17`.*  COMPUTED (`test_run_theorem`): all 2 218 run words with
`L ≤ 17`, for every `B`, were checked directly.  None has `d | c(w)`.  ∎

**Remarks.**
* What it covers.  COMPUTED for every coprime pair with `6 ≤ L ≤ 30`
  (`test_run_duality_and_counts`): the runs inside `[a, L − 2]` give `b(b − 1)/2` distinct
  cyclic words.
  * Exactly `a(a − 1)/2` of them consist of 1s and 2s.  They are the runs of `12` corners:
    swap to `21` every `12` pair whose level lies in the run.
  * The other words contain a 3.  No number of swaps reaches them.
  * Theorem 1 is contained in it.  A `12 → 21` swap is a run of length one.  A `21 → 12`
    swap at level `D` is, by the remark on lowering below, the run `[L − 1 − D, L − 2]`, with
    `g = 1` and `f = D + 1`: the element `η_(D+1)`.
* Distance.  The runs of `12` corners lie up to `⌊a/2⌋ ≈ 0.2 L` swaps from balance.  COMPUTED
  at `(18, 29)` and `(23, 37)` (`test_run_words_reach_far_from_balance`): exactly
  `2a + 1 − 4n` of them are at swap distance `n`, for `1 ≤ n ≤ ⌊a/2⌋`.
* Lowering gives nothing new.  A word is determined by the set `R = {D'_p}` of its
  generalized levels `D'_p = pB − L X'_p`, one in each residue class modulo `L`; rotating the
  word by `r` replaces `R` by `R − D'_r`.  Raising `[E₁, E₂]`, with `a ≤ E₁ ≤ E₂ ≤ L − 2`,
  gives `R = [E₁ − L, E₂ − L] ∪ [0, E₁ − 1] ∪ [E₂ + 1, L − 1]`.  Lowering `[D₁, D₂]`, with
  `1 ≤ D₁ ≤ D₂ ≤ b − 1`, gives `[0, D₁ − 1] ∪ [D₂ + 1, L − 1] ∪ [D₁ + L, D₂ + L]`.  This is
  the first set moved by `L − E₁` when `D₁ = E₂ − E₁ + 1` and `D₂ = L − 1 − E₁`.  That move
  is the rotation that starts the raised word at its corner of level `E₁`, where
  `D' = E₁ − L`.  So the two families contain the same cyclic words.
* Why runs.  By Lemma 10 the coefficients of `q` are the differences of `u` along the
  levels.  A run of any length has two jumps and three terms.  `k` isolated corners have
  `2k` jumps and `2k + 1` terms.  That is why the size argument reaches runs of `0.2 L` swaps
  but not every word at three swaps.
* Two runs.  Raising two separate runs gives five terms,
  `1 − θ^(g₁) + θ^(f₁) − θ^(g₂) + θ^(f₂)`.  If both runs consist of `12` corners the mass is
  below `1 + 4·16/9 = 73/9 < 9`, the two-raise bound of Lemma 9, so the proof of Theorem 2
  should carry over, with Rhin's bound and a finite check.  This is not done here.  Three
  runs can exceed 9.
* COMPUTED, in the suite.
  * Lemma 10 and the normalization hold on 4 600 random words with `L ≤ 30`.
  * Lemma 12 and the element of the proof hold on all 79 323 intervals of levels with
    `L ≤ 40`; 55 855 give words, 46 522 of these contain a 3, and none is a loop.
  * The exact `d` exceeds the Parseval bound on all 20 166 coprime pairs with
    `18 ≤ L ≤ 400`, by at least 3.2 in logarithm.
  * The exact norms of all 4 589 run elements with `L ≤ 22` are odd, below their Parseval
    bounds, and below `d` except at `(3, 5)` and `(5, 8)` (`test_run_exact_norms`).

## 6. How far the norm test reaches (COMPUTED)

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
patterns close to perfect balance — proved at distance 1 (Theorem 1), at distance 2
(Theorem 2) and along one run of levels at any distance (Theorem 3) — and not the whole
space, which matches the heuristic picture where integrality for a generic word is the whole
problem.  The norm of a typical word grows with its
distance: in samples of 4 000 moves of `k` corners at `(610, 967)`, the share with norm below
`d` is 99.8 % for `k = 4`, 63.5 % for `k = 6` and 0.1 % for `k = 10` (not pinned).  Everything here assumes `gcd(L, B) = 1`; when `gcd(L, B) > 1` no loop's word is
balanced, the most balanced primitive words are one swap from a power of a Christoffel word,
and Lemma 1 and Theorems 1, 2 and 3 do not cover them.  At distance 3 the size argument
fails for some words (section 4, last remark).

## 7. Strategy filter (`docs/FILTER.md`)

| test | verdict |
|---|---|
| A, q = 5 has loops | passes: the argument is `q`-sensitive; for `3n+13` the excluded shapes exist |
| B, sign | passes: it uses `2^B > 3^L` |
| C, completions | passes: it uses integrality through norms of algebraic integers, a global fact |
| D, density | passes: the statement is exact |
| E, uniformity | passes: it uses `2 − 1 = 1` (the unit `θ − 1`) and a bound for `2^B − 3^L` |

Like Steiner's theorem (one circuit) and Simons–de Weger's (few circuits), Theorems 1, 2
and 3 exclude families of loop shapes, but at the opposite end: theirs are the most
unbalanced loops, these the loops within two swaps of perfect balance or one run of levels
away from it, for coprime `(L, B)`.

## 8. Literature and novelty

Knight (2023/2026) settles balanced loops; Halbeisen–Hungerbühler (1997) give their extremal
property; Fernández and Ibáñez (arXiv 2607.24844, 2026) study Christoffel words as extremal
structures.  None of these uses norms in `Q(2^(1/L))` or treats words one or two swaps, or
one run of levels, from balance; Lemmas 1 and 2 are standard (an index computation and a substitution).  Corollary 4,
Theorems 1, 2 and 3 and the table of section 6 were not found in these sources.  A wider
literature search is needed before calling Theorems 1, 2 and 3 new mathematics; they are new
to this repository.

## 9. Verification

| claim | test |
|---|---|
| Lemma 1 (`θ₀^L = 2`, `θ₀^B = 3` mod `d`) | `test_theta0_is_a_root_of_both_equations` |
| Lemma 2 on random words | `test_theta_identity_on_random_words` |
| Corollary 3 sound on real 3n+q loops | `test_norm_divisibility_holds_on_real_cycles` |
| Theorem 0: unit, lowest terms, integral only at `(1, 2)` | `test_balanced_numerator_is_a_unit_and_coprime_to_d`, `test_balanced_integral_only_when_d_is_one` |
| Corollary 4 threshold; census harness | `test_spread_threshold`, `test_small_spread_forces_balance_on_the_census` |
| Lemmas 5–6 | `test_swap_kinds_ranges_and_reduction` |
| Theorem 1: Parseval bound, small `L`, cited inequality, exact norms | `test_parseval_bound`, `test_small_lengths_directly`, `test_ellison_inequality_exactly_and_the_margin`, `test_exact_norm_test_on_all_one_swap_words` |
| Lemma 7 (corner kinds, exponent ranges) | `test_two_swap_corner_types`, `test_two_swap_words_are_the_distance_two_classes` |
| Lemma 8 (both congruences) | `test_two_swap_congruences` |
| Lemma 9 (mass bounds), against exact norms | `test_two_swap_mass_bounds`, `test_two_swap_parseval_against_exact_norms` |
| Theorem 2: finite range, direct check, analytic ranges and Rhin step | `test_theorem2_finite_range`, `test_two_swap_direct_agrees_with_brute_force`, `test_theorem2_analytic_ranges` |
| the size argument stops at two swaps | `test_three_swap_norm_can_exceed_d` |
| Lemma 10 (profile formula) and the normalization | `test_profile_formula_on_random_words` |
| Corollary 11 (mass criterion) | `test_mass_criterion_is_sound_on_all_small_words` |
| Lemma 12 and the element of a run | `test_run_validity_and_element` |
| Theorem 3: constants, exact `d`, `L ≤ 17` directly, exact norms | `test_run_theorem`, `test_run_exact_norms` |
| runs: lowering, counts, swap distance | `test_run_duality_and_counts`, `test_run_words_reach_far_from_balance` |
| section 6 | `test_reach_profiles` |
| filter test A | `test_q13_has_balanced_and_one_swap_loops` |

Run: `cd python && uv run pytest tests/test_balance.py` (30 tests).
