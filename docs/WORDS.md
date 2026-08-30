# Words, residues, collisions — the classification lemmas and the sign law

**Provenance.** Produced by the collision-classification run of 2026-08-30:
every PROVED item below was written by one agent and then re-derived line by
line by an independent adversarial checker, with every load-bearing number
recomputed from fresh code; the checkers' corrections are incorporated (and
noted where they changed a statement).  Witnesses: `python/tests/test_words.py`
(26 tests) and `lean/Collatz/Words.lean`.  Labels follow the house scheme:
**PROVED** (complete proof, adversarially checked), **COMPUTED** (exact, this
project), **CONJECTURE** (witnessed, unproved), **CITED**.

**Reading guide.** Everything here classifies the *magnitude-free* sieve of
docs/DEATH_DEPTH.md.  By the q-transfer theorem (docs/FILTER.md test A) all of
it is identical at `q = 5`, which has a real cycle — so this chapter can
steer and measure, never finish.  Its two headline items are Theorem A (a new
proved half-law) and the no-rate-gain theorems (a proved explanation of why
the collision program cannot beat `lambda` with bounded windows).

---

## 0. Objects (W0)

`alpha = log2 3`; `f(t) = floor(t*alpha)`, computed exactly as
`bit_length(3^t) - 1` — i.e. the unique integer with `2^f(t) <= 3^t < 2^f(t)+1`
(`2^B = 3^t` is impossible by parity, so all comparisons are strict and
irrationality of `alpha` is never needed as an analytic input).
`jump(k) = f(k+1) - f(k) ∈ {1, 2}` is the Sturmian word of `alpha`; it
contains no `11` (`f(k+2) >= f(k) + 3`, since `9 * 2^{f(k)} <= 3^{k+2}`) and
no `222` (`f(k+3) <= f(k) + 5`, since `3^3 < 2^5`).

A **word** of length `k` is `(b_1..b_k)`, integers `b_t >= 1`, partial sums
`B_t`; it is **admissible** iff `B_t <= f(t)` for all `t` (the symbolic caps of
`backtree.py`).  `N_k` counts admissible words:
`1, 2, 3, 7, 12, 30, 85, 173, 476, 961, 2652, 8045, ...` (= OEIS A100982
shifted, `A100982(n+1) = N_n`).  The constant recursion is `c_0 = 0`,
`c_t = 2^{b_t} c_{t-1} + 3^{t-1}`, and the **residue map** is

    Phi_k(b)  =  c_k * 2^{-B_k}   (mod 3^k)
              ==  sum_{t=1..k} 3^{t-1} 2^{-B_t}   (mod 3^k)      [C1]

**Liveness** (matching `deathdepth.live_chains`): `b` is live at `r` mod `3^k`
iff from every `y ≡ r` all `k` backward divisions `y -> (2^{b_t} y - 1)/3` are
exact.  Survivors `S_k`, `a_k = |S_k|`.

## 1. Realization (W1) — PROVED

**For every word (admissible or not), there is exactly one live residue class:
`Phi_k(b)`.**  Moreover the depth-`k` congruence `2^{B_k} y ≡ c_k (mod 3^k)`
implies every prefix congruence `2^{B_t} y ≡ c_t (mod 3^t)` (prefix collapse:
`c_k ≡ 2^{B_k - B_t} c_t mod 3^t`, downward induction), `Phi_k(b) ≡
Phi_t(prefix) (mod 3^t)`, `3 ∤ Phi_k(b)`, and exactness bookkeeping is
automatic (step `t` exact forces `y_{t-1} ≢ 0` and the parity of `b_t`).

*Proof core.* Induction gives: divisions `1..t` all exact iff
`3^s | 2^{B_s} y - c_s` for `s <= t`, with `y_t = (2^{B_t} y - c_t)/3^t`
(multiply step-`t` divisibility by `3^{t-1}` and substitute the closed form).
The depth-`k` condition alone then pins `y ≡ c_k 2^{-B_k} (mod 3^k)` — one
class.  ∎

**Consequences.** Live (word, residue) pairs number `N_k`; `S_k = image(Phi_k)`
over admissible words; `a_k = |image| <= N_k`; and ALL arithmetic content of
the sieve beyond lattice-path combinatorics is the **collision** structure
`N_k - a_k = 0, 0, 0, 1, 2, 8, 35, 69, 222, 423, 1350, 4843, 10084, 31827,
64218, 199421, 401292, 1239516, 4242959, 9268281, 28998785` (k <= 21).

**Prior art (audit).** The uncapped core is **Wirsching's** (LNM 1681, 1998;
quoted verbatim in Monks–Monks–Monks–Monks, arXiv:1204.3904 §4, whose Thm 5.1
gives the 3-adic version); the forward mirror is Terras 1976 (mod `2^k`
bijection).  Kramer (arXiv:2607.10041, 2026) independently writes the closed
form of `Phi_k` as a "3-adic endpoint representative", uncapped, no counting.
What is this repo's: the Sturmian-cap restriction, the survivor-image count
`a_k` (still untabulated anywhere found), and everything downstream.

## 2. Slope-blindness (W2) — PROVED

`B_k >= k` with equality iff `b = 1^k` (unique minimal-slope chain, admissible
at every `k`); `c_k(1^k) = 3^k - 2^k` and `Phi_k(1^k) = 3^k - 1 = -1`
(the fixed point of `y -> (2y-1)/3`).  So the defect `k*alpha - B_k` over live
chains reaches exactly `k(alpha - 1) ≈ 0.585k` — linear growth, attained only
on the `-1` class: the sieve caps the slope from one side and is provably
blind to it from the other (filter test C made quantitative).

*Correction kept from the checking pass:* what is unique is the minimal-slope
**chain**, not the chain at `-1`: the residue `-1` carries additional live
words from `k = 4` on — chain counts `1,1,1,2,2,2,3,3,4,4,5,7,8` (k <= 13) —
and its first extra word is exactly the first collision (see W3).  A tempting
generalization is **false**: not every rational/negative `T`-cycle pins an
ever-surviving residue — the backward 2-cycle at `-5` uses word `(2,1)` which
violates the caps (`B_1 = 2 > 1`), and `-5` dies at depth 1; phase matters
(`-7`, the other phase, survives every depth checked via `(1,2,1,2,...)`).

## 3. The bump law (W3) — PROVED (and one FALSE claim retired)

**W3a (FALSE).** "Admissible words stay admissible under `b_k -> b_k + 2`" is
wrong: `(1)` is admissible, `(3)` is not.  The bump is admissible iff the last
cap has slack `>= 2`.

**W3b (bump law).** For ANY word and any `j` with `b_k + j >= 1`:
`c'_k = 2^j c_k - (2^j - 1) 3^{k-1}`, so

* `j` even  ⟹  `Phi_k` **unchanged** mod `3^k` (unconditionally);
* `j` odd  ⟹  `Phi_k` unchanged mod `3^{k-1}` but shifted by a *unit* multiple
  of `3^{k-1}` — exactly the top 3-adic digit moves.

This is the mod-`3^k` shadow of the classical merging of `z` and `4z + 1`
(`(2^{b+2} y - 1)/3 = 4z + 1`).  Every admissible word with last-cap slack
`>= 2` therefore certifies a collision; the first one in existence,
`{(1,1,1,1), (1,1,1,3)}` at `80 ≡ -1 (mod 81)`, is exactly such a pair.

**W3c (cap saturation).** Every survivor carries a live chain with
`B_k >= f(k) - 1` (bump the last letter by `2*floor((f(k)-B_k)/2)`).  The
`-1` is sharp at every `2 <= k <= 12` (witness `k = 2`: `r = 8` has the single
chain `(1,1)`); the obstruction is parity, by W3b.

## 4. Extension count and gap bounds (W4) — PROVED

`f(k-1) + 1 <= f(k) <= f(k-1) + 2`, by pure `Nat` inequalities (`2 < 3 < 4`);
and `(b_1..b_{k-1}) -> (b_1, ..., b_{k-1}, f(k) - B_{k-1})` is a **bijection**
from admissible `(k-1)`-words onto the cap-hitting `k`-words, so

    #{admissible b of length k with B_k = f(k)}  =  N_{k-1}.

## 5–6. Leafless and forced doubling (W5, W6) — PROVED

For a survivor `r` with live word `b`, the endpoint class
`y_k ≡ u + 2^{B_k} t (mod 3)` is a **bijection** of the lift digit
`t ∈ {0,1,2}` (2 is a unit).  Choosing the digit with `y_k ≡ -1` and appending
letter 1 always works (cap OK since `f(k+1) >= f(k)+1`): **every survivor has
a surviving lift** (`a_{k+1} >= a_k`; the survivor tree is leafless — an
integer dies by its own digits leaving the tree, never at a dead end).  When
`jump(k) = 2`, the digit with `y_k ≡ 1` and letter 2 gives a **second,
distinct** lift: `a_{k+1} >= 2 a_k` at every jump-2 level — sharp (equality
exactly at `k = 1, 3`; and at every jump-1 level `k <= 12` some survivor has
exactly one child: `r = 2` at `k = 2`, `r ∈ {44, 74}` at `k = 4`), so the
doubling is genuinely slaved to the Sturmian word.

---

## 7. The Sturmian sign law — Theorem A, Conjecture B

**The law** (COMPUTED; zero violations, zero ties, `k = 2..2216`, checked on
independently recomputed A100982 data):

    sign(N_k^2 - N_{k-1} N_{k+1})  =  +1   iff   jump(k) = 1.

The second difference of `log N_k` is slaved to the binary digits of
`log2 3`.  Not found anywhere in the literature (audit §9).

**Reduction (PROVED).** With `S_k = sum of B_k`, `sbar = S/N`, slack
`X = f(k) - B_k`:

* every admissible word has exactly `X + jump(k)` one-letter extensions, so
  `N_{k+1} = f(k+1) N_k - S_k`, and the children of a slack-`X` parent carry
  each slack in `{0, ..., X + jump - 1}` exactly once;
* `D_k := N_k^2 - N_{k-1} N_{k+1} = N_k N_{k-1} ((sbar_k - sbar_{k-1}) - jump(k))`;
* the slack profiles `g_k` are **log-concave with full interval support**
  (strictly, at every internal point, `k <= 200` checked) — proof: in slack
  coordinates the level recursion is `g -> tail-sums(g)` at jump-1 and
  `g -> duplicate-head(tail-sums(g))` at jump-2, with NO truncation (the
  staircase cut dissolves under `X = f(k) - B`), and partial/tail sums
  preserve log-concavity;
* for a discrete log-concave law on `{0..M}`, `T(a+b) <= T(a) T(b)` and hence
  `E[X(X-1)] < 2 mu^2` strictly (geometric = equality case);
* four-case criterion: `sign(D_k)` is determined by the slack moments at
  `n = k-1` via `E[X(X-1)] vs 2 mu^2 + 2(j-j') mu + j(j+1-2j')`,
  `j = jump(k-1)`, `j' = jump(k)`.

**Theorem A (PROVED).**  For every `k >= 2` with `jump(k) = 1`:
`N_k^2 > N_{k-1} N_{k+1}`.  *(Composition of the four bullets; the `j = 2`
case is a fortiori.  Scope note from checking: the argument as written needs
`alpha > 3/2` — fine for `alpha = log2 3`; for `alpha <= 3/2` ties can occur.)*

**Conjecture B (open; = the jump-2 half).**  `c_n := mu(mu+1) - Var(X_n) < 2`
for all `n` — equivalently, integerized, `W_n := 2*S1^2 + S1*S0 - S2*S0 <
2*S0^2` (moments of `g_n`; e.g. `g_5 = (7,4,1)`, `W_5 = 48 < 288`).  PROVED
equivalent to the jump-2 half given the reduction; verified to `n ~ 1200`
(sup `c_n = 1.4715` on (1,2)-levels; on the binding (2,2)-levels sup
`= 0.5651`, decreasing).  **Named obstruction:** `c < 2` is FALSE for general
log-concave profiles (uniform gives `~M^2/6`), so no local/shape-class
argument suffices; a proof must propagate a quantitative invariant (e.g.
two-sided tail-ratio bounds) along the Sturmian orbit — the no-`11`/no-`222`
facts route every tight `(2,2)`-test to a maximally-smoothed `U`-image level,
which is *why* the law holds.

**Zarubin's recursion (CONJECTURE as used here).**  The A100982 comment
(Zarubin 2015, labeled "Theorem 1" there) `N_k = sum_{m>=1} (-1)^{m-1}
C(f(k-m+1)+m-1, m) N_{k-m}` has **no published proof anywhere found**; exact
here to `k = 250` (two agents), shaped like a Steck–Mohanty staircase
determinant expansion.  It does not by itself yield the sign law.

**Transfer fact TF (CONJECTURE).**  At every `2 <= k <= 23`, the `a`-ratio
`a_k^2/(a_{k-1} a_{k+1})` lies strictly between 1 and the *square* of the
`N`-ratio, on the same side: collisions erode but never overturn the `N`-side
sign.  TF + the `N` sign law would prove the `a_k` sign law (itself verified
22/22).  The binding cases are the `(2,2)`-levels — the same hard case as
Conjecture B, now tied to fiber sizes.

## 8. Collisions — the rewrite structure (C-lemmas)

All PROVED unless marked; complete census to `k = 16` (double-verified;
~875k colliding pairs).

* **C1 (evaluation).** `Phi_k(b) ≡ sum_t 3^{t-1} 2^{-B_t}`; `Phi_k` depends
  only on the partial-sum vector, and mod `3^m` only on `B_t mod 2*3^{m-t}`.
* **C2 (prefix-free criterion).** Words with common prefix length `j` collide
  iff their *tails* satisfy `sum_s 3^{s-1}(2^{-D_s} - 2^{-D'_s}) ≡ 0 (mod
  3^{k-j})`.  **The prefix enters in no way** — the expected "enabling
  congruence on the prefix" does not exist; the only enabling condition is
  cap slack (admissibility of both words).  Colliding tails transfer to every
  admissible prefix.
* **C3 (window-1 rule + closed form).** Same-prefix last letters collide iff
  equal parity.  Hence every fiber has a word with `b_k ∈ {1,2}`, and

      a_k  <=  E_k  =  2 N_{k-1} - [f(k)-f(k-1) = 1] * N_{k-2}

  (`E_13 = 13438`, `E_16 = 217900`; vs `a_16 = 113034`).
* **C4 (window-2 rule).** Classified exactly by `(D_1 mod 6, D_2 mod 2)` data
  (order of 2 mod 9 is 6); brute-verified on 100k+ tail pairs, 0 mismatches.
* **C5 (normalization).** Subtracting `2*3^{m-1}` from letter `b_{k-m+1}`
  preserves `Phi` (LTE: `v_3(2^{2*3^{m-1}} - 1) = m`); every fiber contains a
  word with `b_{k-i} <= 2*3^i`.
* **C6 (window-m bounds; NO-RATE-GAIN).** `a_k <= U_k^{(m)}` for every window
  `m`, computable in `O(k^2)`; but `N_{k-m} <= U_k^{(m)} <= 2*3^{m-1} N_{k-m}`,
  so **every fixed-window bound has exactly `N`'s growth rate**: bounded-window
  merging can improve constants (`U^{(6)} ~ 0.30 N`), never prove `mu < lambda`.
* **C7 (unit saturation).** Over *uncapped* tails the window image is ALL
  `2*3^{m-1}` units mod `3^m` — consistent with Tao's support-totality for the
  uncapped model: **the caps are the sole possible source of any `mu < lambda`
  deficit.**
* **C8 (minimal prefix).** Every colliding pair has common prefix `>= 3`;
  `j = 3` pairs are exactly `(1,1,1)` with divergence letters `{1,3}` (the
  first-collision seed).  Census: the minimal window connecting all fibers is
  `k - 3` at EVERY level `4 <= k <= 16` (fibers needing the maximal window:
  `1,1,1,2,2,5,7,15,31,54,123,231,523`), and the bounded-window share of
  merges declines (73% -> 61% over `k = 12..16`): collisions are NOT generated
  by bounded-window rewrites.
* **C9 (interior-rewrite rigidity).** *(Restated per checking: the exponent-sum
  map is injective on strictly decreasing sequences of FIXED length; variable
  length fails — `38 = 2^5 + 3*2 = 2^3 + 3*2^2 + 9*2`.)*  Consequence: a
  colliding pair whose partial sums re-agree from position `i` on has shared
  suffix `< 0.36908 i + log_3 2`.  Reconvergent pairs first exist at `k = 11`
  (`0,...,0,10,30,213,1159,2667,11380` for `k <= 16`), all within the bound.
* **C10 (descendant submultiplicativity — and its collapse).** `h_{m+n} <=
  h_m h_n` for max descendant counts, so `mu <= inf h_m^{1/m}`; but `h_m = 3^m`
  for `m <= 5` (full ternary subtrees of depth 5 exist in the survivor tree;
  `h_6 >= 715/729`, `h_7 >= 1878/2187`, still rising) — this route certifies
  nothing below 3.  Max fiber sizes `2,2,3,4,4,5,5,7,10,11,16,17,23`
  (`k = 4..16`).
* **C11 (enabled density).** The window-1 rewrite is enabled on a fraction
  exactly `1` (jump-2 levels) or `1 - N_{k-2}/N_{k-1} ∈ [0.637, 0.700]`
  (jump-1 levels) of prefixes — majority density everywhere, `>= N_{k-3}/N_{k-1} > 0` always.
* **C12 (phase lock — CONJECTURE).** The collision-rate increment is
  sign-locked to the cap increment: `1 - a_k/N_k` rises exactly at levels
  where the cap grows by 2 — 14/14 for `k = 8..21` (Pearson 0.957; sharpens
  the survey's +0.67 correlation to an exact sign law over the range).
* **C13 (CONJECTURE).** `#(pairs with prefix exactly 3) = #(pairs with prefix
  exactly 4)` at every level `5 <= k <= 16` (12/12; trivially false at `k=4`).
  Unexplained self-similarity across one Beatty step.
* **C14 (program status — the honest bottom line).** The proved bounds (C3,
  C5, C6) improve *constants only*; by C6/C7/C10 the three natural routes to
  `mu < lambda` (bounded windows, slack-free merging, uniform branching) are
  **closed by theorems, not by ignorance**.  What a rate gain needs: merge
  mass in windows of width `~ k` — exactly the regime with no finite-state
  technology (the repo's no-finite-transfer-matrix fact).  `mu <= lambda`
  stays the only proved upper rate bound; the bracket in DEATH_DEPTH.md is
  untouched at the top.

## 9. Prior art / novelty (audit of 2026-08-30, all sources fetched)

* **Known:** realization core (Wirsching LNM 1681; Monks et al. 1204.3904);
  Terras 1976 forward bijection; `N_k` = A100982 (Roosendaal, Zarubin's
  unproved recursion, Winkler's tree recursion arXiv:1709.03385, Hikawa's DP);
  Applegate–Lagarias / Krasikov–Lagarias bound a *different* quantity
  (integers below `x` in the *uncapped* tree, lower bounds); Tao 2022/2020:
  uncapped support mod `3^n` is everything coprime to 3.
* **Adjacent, cited, distinct:** Terras's coefficient stopping time
  conjecture (open since 1976; records: `kappa <= 2593` Terras, `< 105000`
  Garner 1981; Rozier–Terracol, Discrete Math. 349 (2026): 593 paradoxical
  sequences, mod `2^j` only) — one integer's two forward statistics, not two
  backward words' one residue; Garner 1985 coalescence pairs (+ Wu 1992
  counterexamples) — forward value coalescence, not residue fibers.  The
  project does **not** inherit a named conjecture.
* **Not found anywhere:** the sign law (or ANY log-concavity statement about
  A100982); an upper bound on capped 3-adic survivor growth below `lambda`
  (`mu` vs `lambda` appears to be an open, unclaimed question); the collision
  classification; the `a_k` sequence itself.
* Nearby-but-generic: log-concavity via lattice paths (e.g. Liang–Sagan,
  arXiv:2408.02782 — generic technology, nothing Beatty-slaved).

## 10. Verification

| item | Python (`test_words.py`) | Lean (`Words.lean`) |
|---|---|---|
| W0 caps/jump word | exact to `t = 2000` / `k = 1000` | `decide` instances |
| W1 realization | brute force all residues, `k <= 5`; image = `surviving_residues(10)` | collision pair + uniqueness at `k = 4` by `decide` |
| W2 slope-blindness | `phi(1^k) = -1`, `-1` chain counts, unique min slope | `c(1^k) = 3^k - 2^k` instances |
| W3 bump law | all words `k <= 10`, `j ∈ {-2,-1,1,2,3,4}` | `decide` at `k = 4` |
| W4 extension count | `= N_{k-1}`, `k <= 13` | gap bounds by `decide` |
| W5/W6 children | min = 1 / 2 per jump, witnesses pinned | — |
| Theorem A chain | identity, criterion, strict LC (`k <= 200`), law to 400 | sign-law witness `k <= 12` by `decide` |
| Conjecture B | `0 < c_n < 2`, `n <= 300`; `W_5 = 48` | `W_5 = 48 < 288` by `decide` |
| C-lemmas | parity rule, closed form, min-prefix, LTE, saturation, rigidity fixture | first-collision equality by `decide` |
| TF / phase lock / Zarubin | exact ranges as scoped | — |
