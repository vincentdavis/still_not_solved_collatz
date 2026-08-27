/-
  Collatz/Core.lean

  Cycle-free lemmas.  These carry the actual mathematical content: every
  statement here is about a *single* multiplicative step `3 * y + q = 2^b * x`,
  with no cycle machinery in sight.  The `Cycle` layer is a thin wrapper.

  Mathlib-free: Lean 4 core only.
-/
import Collatz.Odd

namespace Collatz

/-! ## 0. The three facts about powers of two that we need -/

theorem two_pow_le {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

/-- `2 ^ b = 2 ^ k * 2 ^ (b - k)` for `k ≤ b`. -/
theorem two_pow_split {k b : Nat} (h : k ≤ b) : 2 ^ b = 2 ^ k * 2 ^ (b - k) := by
  have hb : k + (b - k) = b := by omega
  calc (2:Nat) ^ b = 2 ^ (k + (b - k)) := by rw [hb]
    _ = 2 ^ k * 2 ^ (b - k) := Nat.pow_add 2 k (b - k)

/-- `2 ^ k * 2 ^ b ≤ 2 ^ b'` whenever `b + k ≤ b'`. -/
theorem two_pow_shift (k : Nat) {b b' : Nat} (h : b + k ≤ b') :
    2 ^ k * 2 ^ b ≤ 2 ^ b' := by
  have e  : (2:Nat) ^ (b + k) = 2 ^ b * 2 ^ k := Nat.pow_add 2 b k
  have e2 : (2:Nat) ^ k * 2 ^ b = 2 ^ b * 2 ^ k := Nat.mul_comm _ _
  have h1 : (2:Nat) ^ (b + k) ≤ 2 ^ b' := two_pow_le h
  omega

/-! ## 1. T0 — odd multiples of 3 have no odd predecessor -/

/-- **T0 (core).**  If `3 ∤ q` then `3 * y + q = 2 ^ b * x` forces `3 ∤ x`.
    Read backwards: an odd multiple of 3 has no odd `S_q`-predecessor. -/
theorem T0_core {q y x b : Nat} (hq3 : q % 3 ≠ 0) (h : 3 * y + q = 2 ^ b * x) :
    x % 3 ≠ 0 := by
  intro hx
  obtain ⟨t, ht⟩ : ∃ t, x = 3 * t := ⟨x / 3, by omega⟩
  subst ht
  have e : 2 ^ b * (3 * t) = 3 * (2 ^ b * t) := Nat.mul_left_comm _ _ _
  rw [e] at h
  omega

/-- **T0, functional form.**  An odd multiple of 3 is not in the image of `S_q`
    restricted to odd numbers: it has *no* odd predecessor at all, hence it lies
    on no `S_q`-cycle. -/
theorem no_odd_pred_of_three_dvd {q n y : Nat} (hq : q % 2 = 1) (hq3 : q % 3 ≠ 0)
    (hn3 : n % 3 = 0) (hy : y % 2 = 1) : S q y ≠ n := by
  intro h
  obtain ⟨b, _, hb, _⟩ := S_spec hq hy
  have hne := T0_core hq3 hb
  rw [h] at hne
  exact hne hn3

/-! ## 2. T1 — the maximum of a cycle needs at least two halvings -/

/-- **T1 (core).**  A *single* halving always increases: `3n + q = 2m` with
    `q > 0` forces `m > n`.  This is the user's seed observation, and it is
    literally one call to `omega`.  No hypothesis relating `n` and `q`. -/
theorem T1_core {q n m : Nat} (hq : 0 < q) (h : 3 * n + q = 2 * m) : n < m := by
  omega

/-- **T1 (core), mod-4 form.**  If `n, q` are odd and `3n + q ≡ 2 (mod 4)`,
    then the next odd number is strictly bigger: `n < S q n`. -/
theorem T1_core_mod4 {q n : Nat} (hq : q % 2 = 1) (hn : n % 2 = 1) (hqp : 0 < q)
    (h4 : (3 * n + q) % 4 = 2) : n < S q n := by
  obtain ⟨b, hb1, hb, _⟩ := S_spec hq hn
  rcases (show b = 1 ∨ 2 ≤ b by omega) with hb2 | hb2
  · subst hb2
    rw [Nat.pow_one] at hb
    exact T1_core hqp hb
  · exfalso
    have e := two_pow_split (k := 2) hb2
    have e4 : (2:Nat) ^ 2 = 4 := by decide
    rw [e4] at e
    rw [e, Nat.mul_assoc] at hb
    omega

/-- **T1, q = 1.**  An odd `n ≡ 3 (mod 4)` is followed by a *bigger* odd number,
    so it can never be the largest element of a cycle.
    (`7 ↦ 11`, `11 ↦ 17`, `15 ↦ 23`, …) -/
theorem lt_S_of_three_mod_four {n : Nat} (h : n % 4 = 3) : n < S 1 n :=
  T1_core_mod4 (by decide) (by omega) (by decide) (by omega)

/-! ## 3. T2 — the predecessor of the maximum -/

/-- **T2 (core).**  If `y ≤ x`, `q < x`, and `3 * y + q = 2 ^ b * x` with
    `b ≥ 1`, then `b = 1`. -/
theorem T2_core {q y x b : Nat} (_hq : 0 < q) (hxq : q < x) (hb1 : 1 ≤ b)
    (hyx : y ≤ x) (h : 3 * y + q = 2 ^ b * x) : b = 1 := by
  rcases (show b = 1 ∨ 2 ≤ b by omega) with hb2 | hb2
  · exact hb2
  · exfalso
    have h4 : (4 : Nat) ≤ 2 ^ b := by
      have h' : (2:Nat) ^ 2 ≤ 2 ^ b := two_pow_le hb2
      have e : (2:Nat) ^ 2 = 4 := by decide
      omega
    have hmul : 4 * x ≤ 2 ^ b * x := Nat.mul_le_mul_right x h4
    omega

/-- **T2 (core), unpacked.**  The predecessor of the maximum satisfies
    `3 * y + q = 2 * x`, i.e. `y = (2x − q)/3`. -/
theorem T2_pred {q y x b : Nat} (hq : 0 < q) (hxq : q < x) (hb1 : 1 ≤ b)
    (hyx : y ≤ x) (h : 3 * y + q = 2 ^ b * x) : 3 * y + q = 2 * x := by
  have hb := T2_core hq hxq hb1 hyx h
  subst hb
  rw [Nat.pow_one] at h
  exact h

/-! ## 4. The predecessor lemma (Lemma U): at most one odd predecessor below -/

/-- Auxiliary for Lemma U: two odd predecessors of `p` at *different* exponents,
    both `≤ p`, are impossible.  Two cases:

* `b' = b + 1` — then `3 y' = 6 y + q`, so `3 ∣ q`, contradicting `3 ∤ q`;
* `b' ≥ b + 2` — then `y' ≥ 4y + q` while `2 y' ≤ 2 p ≤ 2^b p = 3y + q`,
  which forces `5y + q ≤ 0`.

(Geometrically: `0 < y_b ≤ p` confines `2^b` to a window of additive length 3,
and two powers of two at distance ≥ 2 differ by at least `3·2^b ≥ 6`.) -/
private theorem pred_step_absurd {q p y y' b b' : Nat}
    (hq3 : q % 3 ≠ 0) (hy : 0 < y) (hyp' : y' ≤ p) (hb : 1 ≤ b) (hbb : b < b')
    (h : 3 * y + q = 2 ^ b * p) (h' : 3 * y' + q = 2 ^ b' * p) : False := by
  rcases (show b' = b + 1 ∨ b + 2 ≤ b' by omega) with hcase | hcase
  · subst hcase
    have e : (2:Nat) ^ (b + 1) * p = 2 * (2 ^ b * p) := by
      rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
    omega
  · have h4 : 4 * (2 ^ b * p) ≤ 2 ^ b' * p := by
      have hs : (2:Nat) ^ 2 * 2 ^ b ≤ 2 ^ b' := two_pow_shift 2 hcase
      have e4 : (2:Nat) ^ 2 = 4 := by decide
      rw [e4] at hs
      have hm := Nat.mul_le_mul_right p hs
      have e : 4 * 2 ^ b * p = 4 * (2 ^ b * p) := Nat.mul_assoc 4 (2 ^ b) p
      omega
    have h2p : 2 * p ≤ 2 ^ b * p := by
      have hs : (2:Nat) ^ 1 ≤ 2 ^ b := two_pow_le hb
      have e2 : (2:Nat) ^ 1 = 2 := by decide
      rw [e2] at hs
      exact Nat.mul_le_mul_right p hs
    omega

/-- **Lemma U (core): uniqueness of the predecessor below the target.**
    For `3 ∤ q`, a number `p` has *at most one* odd predecessor `y` with
    `0 < y ≤ p`.  No hypothesis relating `p` and `q` is needed. -/
theorem pred_unique_core {q p y y' b b' : Nat}
    (hq3 : q % 3 ≠ 0)
    (hy : 0 < y) (hy' : 0 < y')
    (hyp : y ≤ p) (hyp' : y' ≤ p)
    (hb : 1 ≤ b) (hb' : 1 ≤ b')
    (h : 3 * y + q = 2 ^ b * p) (h' : 3 * y' + q = 2 ^ b' * p) :
    y = y' := by
  rcases (show b < b' ∨ b = b' ∨ b' < b by omega) with hc | hc | hc
  · exact (pred_step_absurd hq3 hy hyp' hb hc h h').elim
  · subst hc; omega
  · exact (pred_step_absurd hq3 hy' hyp hb' hc h' h).elim

/-- **Lemma U, functional form.**  For `q` odd with `3 ∤ q`: any two odd
    `S_q`-predecessors of `p` that are `≤ p` are equal. -/
theorem pred_unique {q p y y' : Nat} (hq : q % 2 = 1) (hq3 : q % 3 ≠ 0)
    (hy : 0 < y) (hy' : 0 < y') (hyo : y % 2 = 1) (hyo' : y' % 2 = 1)
    (hyp : y ≤ p) (hyp' : y' ≤ p)
    (hs : S q y = p) (hs' : S q y' = p) : y = y' := by
  obtain ⟨b, hb1, hb, _⟩ := S_spec hq hyo
  obtain ⟨b', hb1', hb', _⟩ := S_spec hq hyo'
  rw [hs] at hb
  rw [hs'] at hb'
  exact pred_unique_core hq3 hy hy' hyp hyp' hb1 hb1' hb hb'

/-- **Predecessor existence.**  If `q` is odd, `p` is odd, `q < 2p` and
    `2p ≡ q (mod 3)`, then `y = (2p − q)/3` really is an odd predecessor of `p`,
    and it lies strictly below `p`. -/
theorem pred_exists {q p : Nat} (hq : q % 2 = 1) (hp : p % 2 = 1)
    (hlt : q < 2 * p) (h3 : (2 * p) % 3 = q % 3) :
    ∃ y, 0 < y ∧ y % 2 = 1 ∧ y < p ∧ 3 * y + q = 2 * p ∧ S q y = p := by
  obtain ⟨y, hy⟩ : ∃ y, 3 * y + q = 2 * p := ⟨(2 * p - q) / 3, by omega⟩
  refine ⟨y, by omega, by omega, by omega, hy, ?_⟩
  show oddPart (3 * y + q) = p
  rw [hy, oddPart_two_mul (by omega)]
  exact oddPart_of_odd hp

/-! ### The `q = 1` packaging asked for in the task

For odd `p > 1`: the odd predecessors of `p` that do not exceed `p` are
exactly `{(2p−1)/3}` when `p ≡ 2 (mod 3)`, and none otherwise. -/

/-- `q = 1`: an odd predecessor `y ≤ p` of `p > 1` must satisfy `3y + 1 = 2p`,
    i.e. `y = (2p − 1)/3`.  (Positivity of `y` is not needed.) -/
theorem pred_le_eq_q1 {p y : Nat} (hp1 : 1 < p) (hyo : y % 2 = 1)
    (hyp : y ≤ p) (hs : S 1 y = p) : 3 * y + 1 = 2 * p := by
  obtain ⟨b, hb1, hb, _⟩ := S_spec (q := 1) (by decide) hyo
  rw [hs] at hb
  exact T2_pred (by decide) hp1 hb1 hyp hb

/-- `q = 1`: at most one odd predecessor `≤ p`. -/
theorem pred_le_unique_q1 {p y y' : Nat} (hy : 0 < y) (hy' : 0 < y')
    (hyo : y % 2 = 1) (hyo' : y' % 2 = 1) (hyp : y ≤ p) (hyp' : y' ≤ p)
    (hs : S 1 y = p) (hs' : S 1 y' = p) : y = y' :=
  pred_unique (by decide) (by decide) hy hy' hyo hyo' hyp hyp' hs hs'

/-- `q = 1`: if `p` is odd and `p ≡ 2 (mod 3)` then `(2p−1)/3` is an odd
    predecessor of `p` lying strictly below `p`. -/
theorem pred_lt_exists_q1 {p : Nat} (hp : p % 2 = 1) (h3 : p % 3 = 2) :
    ∃ y, 0 < y ∧ y % 2 = 1 ∧ y < p ∧ 3 * y + 1 = 2 * p ∧ S 1 y = p :=
  pred_exists (by decide) hp (by omega) (by omega)

/-- **Predecessor lemma, `q = 1`, final form.**
    An odd `p > 1` has an odd predecessor `≤ p` **iff** `p ≡ 2 (mod 3)`;
    it is then unique (`pred_le_unique_q1`) and equal to `(2p−1)/3`
    (`pred_le_eq_q1`). -/
theorem pred_le_iff_q1 {p : Nat} (hp : p % 2 = 1) (hp1 : 1 < p) :
    (∃ y, 0 < y ∧ y % 2 = 1 ∧ y ≤ p ∧ S 1 y = p) ↔ p % 3 = 2 := by
  constructor
  · rintro ⟨y, _hy, hyo, hyp, hs⟩
    have := pred_le_eq_q1 hp1 hyo hyp hs
    omega
  · intro h3
    obtain ⟨y, hy, hyo, hlt, _, hs⟩ := pred_lt_exists_q1 hp h3
    exact ⟨y, hy, hyo, by omega, hs⟩

/-! ## 5. T5 — the second backward hop -/

/-- **T5 (core), exact inequality, general `q`.**  Stated cleared of subtraction
    to stay inside `Nat`.  Over `ℤ` this is GROUND_TRUTH's
    `M (2^{1+b₂} − 9) ≤ (2^{b₂} + 3) q`. -/
theorem T5_ineq {q x y1 y2 b2 : Nat}
    (h1 : 3 * y1 + q = 2 * x) (h2 : 3 * y2 + q = 2 ^ b2 * y1) (hy2 : y2 ≤ x) :
    2 ^ b2 * (2 * x) ≤ 9 * x + 3 * q + 2 ^ b2 * q := by
  have e : 3 * (2 ^ b2 * y1) = 2 ^ b2 * (3 * y1) := Nat.mul_left_comm _ _ _
  have h3 : 3 * (3 * y2 + q) = 2 ^ b2 * (3 * y1) := by rw [h2, e]
  have hsplit : 2 ^ b2 * (2 * x) = 2 ^ b2 * (3 * y1) + 2 ^ b2 * q := by
    rw [← h1, Nat.mul_add]
  omega

/-- **T5 (core), sharp general-`q` form.**  If `11 q < 7 x` (i.e. `x > 11q/7`)
    then the second backward hop has `b₂ ≤ 2`.

    The threshold is sharp: `7x = 11q` allows `b₂ = 3` (e.g. `q = 7`, `x = 11`).
    Note there is **no cycle-length hypothesis**: GROUND_TRUTH.md's `L ≥ 3` is
    neither necessary nor sufficient — the right condition is this size bound. -/
theorem T5_core_sharp {q x y1 y2 b2 : Nat} (hx : 11 * q < 7 * x)
    (h1 : 3 * y1 + q = 2 * x) (h2 : 3 * y2 + q = 2 ^ b2 * y1) (hy2 : y2 ≤ x) :
    b2 ≤ 2 := by
  rcases (show b2 ≤ 2 ∨ 3 ≤ b2 by omega) with hb | hb
  · exact hb
  exfalso
  have key := T5_ineq h1 h2 hy2
  have h8 : (8:Nat) ≤ 2 ^ b2 := by
    have h' : (2:Nat) ^ 3 ≤ 2 ^ b2 := two_pow_le hb
    have e : (2:Nat) ^ 3 = 8 := by decide
    omega
  obtain ⟨d, hd⟩ : ∃ d, 2 * x = q + d := ⟨2 * x - q, by omega⟩
  have hsplit : 2 ^ b2 * (2 * x) = 2 ^ b2 * q + 2 ^ b2 * d := by
    rw [hd, Nat.mul_add]
  have h8d : 8 * d ≤ 2 ^ b2 * d := Nat.mul_le_mul_right d h8
  omega

/-- **T5 (core), `q = 1`.**  `x ≥ 2` ⇒ `b₂ ≤ 2`.
    (`11 · 1 < 7 · 2`, so the sharp threshold is met by every `x ≥ 2`.) -/
theorem T5_core_q1 {x y1 y2 b2 : Nat} (hx : 2 ≤ x)
    (h1 : 3 * y1 + 1 = 2 * x) (h2 : 3 * y2 + 1 = 2 ^ b2 * y1) (hy2 : y2 ≤ x) :
    b2 ≤ 2 :=
  T5_core_sharp (by omega) h1 h2 hy2

end Collatz
