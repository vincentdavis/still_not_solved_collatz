/-
  Collatz/Cycle.lean

  The `Cycle` structure and the cycle-level theorems T0–T8.

  DESIGN NOTE (read this before trusting anything below).
  A cycle is presented *backwards from its maximum*, matching the `y_k`
  notation of docs/GROUND_TRUTH.md: `y 0 = M`, and `y (k+1)` is the odd
  `S_q`-predecessor of `y k`.  Indices are plain `Nat` (not `Fin L`), so every
  index computation is available to `omega`; periodicity (`hper`) makes the
  infinite index range harmless.

  The structure *postulates* the backward orbit as a function rather than
  deriving it from a finite list.  That is the safe direction: every genuine
  `S_q`-cycle yields such a structure, so anything proved about `Cycle q`
  applies to every real cycle.  But a reader must check that the fields say
  what they mean.  `Collatz/Examples.lean` exhibits three concrete instances
  (including one with `L = 3` and `M > q`) as evidence that they do, and that
  the interesting regime is not vacuous.

  Mathlib-free: Lean 4 core only.
-/
import Collatz.Core

namespace Collatz

/-- An `S_q`-cycle, presented backwards from its largest odd element. -/
structure Cycle (q : Nat) where
  /-- number of *distinct* odd elements -/
  L : Nat
  /-- `y k` = the `k`-th odd element going backwards from the maximum -/
  y : Nat → Nat
  hL : 0 < L
  hq_pos : 0 < q
  hq_odd : q % 2 = 1
  hq_three : q % 3 ≠ 0
  /-- every element is odd -/
  hodd : ∀ i, y i % 2 = 1
  /-- `y (i+1)` is an odd `S_q`-predecessor of `y i` -/
  hstep : ∀ i, S q (y (i + 1)) = y i
  /-- `y 0 = M` is the maximum -/
  hmax : ∀ i, y i ≤ y 0
  /-- the cycle closes after `L` backward steps -/
  hper : ∀ i, y (i + L) = y i
  /-- `L` is the number of *distinct* elements -/
  hmin : ∀ k, 0 < k → k < L → y k ≠ y 0

namespace Cycle

variable {q : Nat} (C : Cycle q)

/-- `M` = the largest odd element of the cycle. -/
def M : Nat := C.y 0

theorem M_odd : C.M % 2 = 1 := C.hodd 0

theorem M_pos : 0 < C.M := by have := C.hodd 0; show 0 < C.y 0; omega

theorem y_pos (i : Nat) : 0 < C.y i := by have := C.hodd i; omega

/-- Each backward hop, in multiplicative form: `3 * y (i+1) + q = 2 ^ b * y i`. -/
theorem step_mul (i : Nat) :
    ∃ b, 1 ≤ b ∧ 3 * C.y (i + 1) + q = 2 ^ b * C.y i := by
  obtain ⟨b, hb1, hb, _⟩ := S_spec C.hq_odd (C.hodd (i + 1))
  exact ⟨b, hb1, by rw [hb, C.hstep i]⟩

/-- The forward image of a cycle element is again a cycle element:
    `S q (y i) = y (i + L - 1)`. -/
theorem S_eq (i : Nat) : S q (C.y i) = C.y (i + C.L - 1) := by
  have hL := C.hL
  have he : i + C.L - 1 + 1 = i + C.L := by omega
  have h := C.hstep (i + C.L - 1)
  rw [he] at h
  rw [C.hper i] at h
  exact h

/-- Forward images stay below the maximum. -/
theorem S_le_M (i : Nat) : S q (C.y i) ≤ C.M := by
  rw [C.S_eq i]; exact C.hmax _

theorem S_M_le_M : S q C.M ≤ C.M := C.S_le_M 0

/-- Two forward steps out of the maximum also stay below it. -/
theorem S_S_le_M : S q (S q C.M) ≤ C.M := by
  have h : S q C.M = C.y (0 + C.L - 1) := C.S_eq 0
  rw [h]
  exact C.S_le_M _

/-- If the cycle has at least two distinct odd elements then `M ≥ 3`.
    (Hence for `q = 1` the hypothesis `M > q` of T2/T3/T4 is implied by
    `L ≥ 2` — no separate size assumption is needed.) -/
theorem M_ge_three_of_L (hL : 2 ≤ C.L) : 3 ≤ C.M := by
  have hne : C.y 1 ≠ C.y 0 := C.hmin 1 (by omega) (by omega)
  have hle : C.y 1 ≤ C.y 0 := C.hmax 1
  have h1 := C.hodd 1
  have h0 := C.hodd 0
  show 3 ≤ C.y 0
  omega

/-! ## Faithfulness of the encoding

The worry with a *postulated* structure is that it might be satisfiable by
something degenerate — e.g. a shorter orbit padded out to length `L`, which
would make every `L`-indexed statement weaker than advertised.  It is not:
`hstep` alone propagates any coincidence downwards to index 0, where `hmin`
forbids it.  So `y 0, …, y (L-1)` are `L` *pairwise distinct* numbers. -/

/-- Any coincidence `y j = y (j + d)` pushes down to `y 0 = y d`.
    (Apply `S_q` to both sides `j` times; `hstep` is exactly that step.) -/
theorem shift_zero : ∀ j d, C.y j = C.y (j + d) → C.y 0 = C.y d := by
  intro j
  induction j with
  | zero => intro d h; rw [Nat.zero_add] at h; exact h
  | succ j ih =>
      intro d h
      apply ih d
      have e : j + 1 + d = (j + d) + 1 := by omega
      rw [e] at h
      have h' := congrArg (S q) h
      rw [C.hstep j, C.hstep (j + d)] at h'
      exact h'

/-- **The `L` listed elements are pairwise distinct.**  Hence a `Cycle q` really
    does carry `L` distinct odd numbers on one closed `S_q`-orbit: the structure
    cannot be satisfied by a shorter orbit padded out to length `L`. -/
theorem y_ne_of_lt {j k : Nat} (hj : j < k) (hk : k < C.L) : C.y j ≠ C.y k := by
  intro h
  have e : k = j + (k - j) := by omega
  rw [e] at h
  exact C.hmin (k - j) (by omega) (by omega) (C.shift_zero j (k - j) h).symm

/-! ## T0 -/

/-- **T0.**  No element of an `S_q`-cycle is divisible by 3. -/
theorem T0 (i : Nat) : C.y i % 3 ≠ 0 := by
  obtain ⟨b, _, hb⟩ := C.step_mul i
  exact T0_core C.hq_three hb

/-! ## T1 -/

/-- **T1.**  The forward step out of `M` needs at least two halvings:
    `3M + q ≡ 0 (mod 4)`.

    NOTE: no `M > q` hypothesis is needed.  docs/GROUND_TRUTH.md's edge-case
    note claiming otherwise is wrong; its two cited "counterexamples"
    (`q=17, {1,5}` and `q=23, {7,11}`) both *satisfy* this conclusion. -/
theorem T1 : (3 * C.M + q) % 4 = 0 := by
  have hM : C.M % 2 = 1 := C.M_odd
  have h2 : (3 * C.M + q) % 2 = 0 := three_mul_add_even C.hq_odd hM
  rcases (show (3 * C.M + q) % 4 = 0 ∨ (3 * C.M + q) % 4 = 2 by omega) with h4 | h4
  · exact h4
  · exfalso
    have hlt : C.M < S q C.M := T1_core_mod4 C.hq_odd hM C.hq_pos h4
    have hle := C.S_M_le_M
    omega

/-- **T1, general `q`, clean form:** `M ≡ q (mod 4)`. -/
theorem T1_mod4 : C.M % 4 = q % 4 := by
  have h := C.T1
  have hM := C.M_odd
  have hq := C.hq_odd
  omega

/-- **T1, q = 1:** `M ≡ 1 (mod 4)`.  In particular `M ≢ 3 (mod 4)`, which is
    exactly the user's "7 can't be the largest" observation (and it excludes
    11 as well — for the same reason, not because 11 needs a bigger predecessor). -/
theorem T1_q1 (C : Cycle 1) : C.M % 4 = 1 := by
  have h1 := C.T1
  have h2 := C.M_odd
  omega

/-! ## T2 -/

/-- **T2.**  If `M > q` the first backward hop has `b₁ = 1`:
    `3 * y 1 + q = 2 * M`, so the predecessor of `M` is exactly `(2M − q)/3`. -/
theorem T2 (hMq : q < C.M) : 3 * C.y 1 + q = 2 * C.M := by
  obtain ⟨b, hb1, hb⟩ := C.step_mul 0
  have hy : C.y 1 ≤ C.M := C.hmax 1
  exact T2_pred C.hq_pos hMq hb1 hy hb

/-- **T2, general `q`, congruence form:** `2M ≡ q (mod 3)`. -/
theorem T2_mod3 (hMq : q < C.M) : (2 * C.M) % 3 = q % 3 := by
  have h := C.T2 hMq
  omega

/-- **T2, uniqueness (Lemma U applied to a cycle).**  Any odd `y ≤ M` with
    `S q y = M` equals `y 1`.  This needs **no** hypothesis relating `M` and `q`. -/
theorem T2_unique {y : Nat} (hy : y % 2 = 1) (hyM : y ≤ C.M)
    (hs : S q y = C.M) : y = C.y 1 := by
  have h1 : S q (C.y 1) = C.M := C.hstep 0
  exact pred_unique C.hq_odd C.hq_three (by omega) (C.y_pos 1)
    hy (C.hodd 1) hyM (C.hmax 1) hs h1

/-- **T2, q = 1:** `M ≡ 2 (mod 3)`. -/
theorem T2_q1 (C : Cycle 1) (hMq : 1 < C.M) : C.M % 3 = 2 := by
  have h := C.T2 hMq
  unfold M at h ⊢
  omega

/-! ## T3 -/

/-- **T3, general `q`.**  `q < M` ⇒ `M ≡ 5q (mod 12)`.  (CRT on `T1_mod4` and
    `T2_mod3`.)  For `q = 1` this is `M ≡ 5 (mod 12)` = `T3`; the point of the
    general form is that it is *witnessed* — `cycle5` has `M = 49 ≡ 1` and
    `5·5 = 25 ≡ 1 (mod 12)`, `cycle7` has `M = 11` and `5·7 = 35 ≡ 11`.  No
    `Cycle 1` with `M > 1` is known to exist, so `T3` itself has no witness. -/
theorem T3_gen (hMq : q < C.M) : C.M % 12 = (5 * q) % 12 := by
  have h4 := C.T1_mod4
  have h3 := C.T2_mod3 hMq
  omega

/-- **T3.**  `q = 1` ⇒ `M ≡ 5 (mod 12)`.  (CRT on T1 and T2.) -/
theorem T3 (C : Cycle 1) (hMq : 1 < C.M) : C.M % 12 = 5 := by
  have h4 := C.T1_q1
  have h3 := C.T2_q1 hMq
  omega

/-- **T3, in the form asked for: the maximum of a `q = 1` cycle with at least
    two distinct odd elements is `≡ 5 (mod 12)`.** -/
theorem T3_of_L (C : Cycle 1) (hL : 2 ≤ C.L) : C.M % 12 = 5 :=
  C.T3 (by have := C.M_ge_three_of_L hL; omega)

/-! ## T4 (base level only) -/

/-- **T4 (base case), 3-adic form, general `q`.**  T0 applied to the predecessor
    `y 1 = (2M − q)/3` says `3 ∤ y 1`, i.e. `9 ∤ 2M − q`. -/
theorem T4_mod9 (hMq : q < C.M) : (2 * C.M) % 9 ≠ q % 9 := by
  have hy := C.T2 hMq
  have h3 := C.T0 1
  omega

/-- **T4 (base case), general `q`.**  `q < M` ⇒ `M ≢ 5q (mod 36)`.
    Together with `T3_gen` (`M ≡ 5q mod 12`) this leaves exactly the two classes
    `5q + 12` and `5q + 24` mod 36 — for `q = 1`, `17` and `29`, i.e. `T4_base`.
    Witnessed: `cycle5` has `M = 49 ≡ 13 (mod 36)` while `5·5 = 25`. -/
theorem T4_base_gen (hMq : q < C.M) : C.M % 36 ≠ (5 * q) % 36 := by
  have hy := C.T2 hMq
  have h3 := C.T0 1
  omega

/-- **T4 (base case).**  `q = 1` ⇒ `M ≡ 17 or 29 (mod 36)`.
    T3, plus T0 applied to the predecessor `y 1 = (2M − 1)/3 = 8t + 3`. -/
theorem T4_base (C : Cycle 1) (hMq : 1 < C.M) :
    C.M % 36 = 17 ∨ C.M % 36 = 29 := by
  have h12 := C.T3 hMq
  have hy := C.T2 hMq
  have h3 := C.T0 1
  unfold M at h12 hy ⊢
  omega

theorem T4_base_of_L (C : Cycle 1) (hL : 2 ≤ C.L) :
    C.M % 36 = 17 ∨ C.M % 36 = 29 :=
  C.T4_base (by have := C.M_ge_three_of_L hL; omega)

/-! ## T5 -/

/-- **T5, sharp general-`q` form.**  If `11 q < 7 M` then `b₂ ≤ 2`:
    only two even hops back need to be considered.
    No cycle-length hypothesis. -/
theorem T5_gen (hM : 11 * q < 7 * C.M) {b : Nat}
    (hb : 3 * C.y 2 + q = 2 ^ b * C.y 1) : b ≤ 2 := by
  have hMq : q < C.M := by have := C.hq_pos; omega
  exact T5_core_sharp hM (C.T2 hMq) hb (C.hmax 2)

/-- **T5, q = 1.**  `M ≥ 2` ⇒ the second backward hop has `b₂ ≤ 2`.
    This is the user's "we need only look two even hops back", made precise.
    (`L ≥ 3` is **not** needed — see the note in `Collatz/Core.lean`.) -/
theorem T5 (C : Cycle 1) (hM : 2 ≤ C.M) {b : Nat}
    (hb : 3 * C.y 2 + 1 = 2 ^ b * C.y 1) : b ≤ 2 :=
  C.T5_gen (by omega) hb

/-- The exponent of T5 exists and is in `{1, 2}`. -/
theorem T5' (C : Cycle 1) (hM : 2 ≤ C.M) :
    ∃ b, 1 ≤ b ∧ b ≤ 2 ∧ 3 * C.y 2 + 1 = 2 ^ b * C.y 1 := by
  obtain ⟨b, hb1, hb⟩ := C.step_mul 1
  exact ⟨b, hb1, C.T5 hM hb, hb⟩

theorem T5_of_L (C : Cycle 1) (hL : 2 ≤ C.L) :
    ∃ b, 1 ≤ b ∧ b ≤ 2 ∧ 3 * C.y 2 + 1 = 2 ^ b * C.y 1 :=
  C.T5' (by have := C.M_ge_three_of_L hL; omega)

/-! ## T8 — a mod-16 refinement of T1, with no size hypothesis

If `M = 16s + 9` then two forward steps give `12s + 7` and then `18s + 11`,
and `18s + 11 > 16s + 9 = M`, contradicting maximality. -/

/-- **T8.**  `q = 1` ⇒ `M ≢ 9 (mod 16)`. -/
theorem T8 (C : Cycle 1) : C.M % 16 ≠ 9 := by
  intro h9
  obtain ⟨s, hs⟩ : ∃ s, C.M = 16 * s + 9 := ⟨C.M / 16, by omega⟩
  have e1 : S 1 C.M = 12 * s + 7 := by
    rw [hs]
    show oddPart (3 * (16 * s + 9) + 1) = 12 * s + 7
    have e : 3 * (16 * s + 9) + 1 = 2 * (2 * (12 * s + 7)) := by omega
    rw [e, oddPart_two_mul (by omega), oddPart_two_mul (by omega)]
    exact oddPart_of_odd (by omega)
  have e2 : S 1 (12 * s + 7) = 18 * s + 11 := by
    show oddPart (3 * (12 * s + 7) + 1) = 18 * s + 11
    have e : 3 * (12 * s + 7) + 1 = 2 * (18 * s + 11) := by omega
    rw [e, oddPart_two_mul (by omega)]
    exact oddPart_of_odd (by omega)
  have hle := C.S_S_le_M
  rw [e1, e2] at hle
  omega

/-- **T8, refined form of T1 for `q = 1`:** `M ≡ 1, 5 or 13 (mod 16)`. -/
theorem T8_mod16 (C : Cycle 1) : C.M % 16 = 1 ∨ C.M % 16 = 5 ∨ C.M % 16 = 13 := by
  have h4 := C.T1_q1
  have h16 := C.T8
  omega

/-- **T3 ∧ T8.**  `q = 1`, `M > 1` ⇒ `M ≡ 5, 17 or 29 (mod 48)`.
    In particular `M ≡ 41 (mod 48)` is excluded. -/
theorem T3_T8 (C : Cycle 1) (hMq : 1 < C.M) :
    C.M % 48 = 5 ∨ C.M % 48 = 17 ∨ C.M % 48 = 29 := by
  have h12 := C.T3 hMq
  have h16 := C.T8
  omega

/-! ## `b_k`, `B_k`, `c_k` and the closed form (GROUND_TRUTH lines 11–13) -/

/-- `b_k` = number of halvings on the backward hop `y k → y (k−1)`. -/
def bb (k : Nat) : Nat := v2 (3 * C.y k + q)

theorem bb_spec (k : Nat) : 3 * C.y (k + 1) + q = 2 ^ C.bb (k + 1) * C.y k := by
  have hpos : 0 < 3 * C.y (k + 1) + q := by
    have := C.hodd (k + 1); have := C.hq_pos; omega
  have h := two_pow_v2_mul_oddPart hpos
  show 3 * C.y (k + 1) + q = 2 ^ (v2 (3 * C.y (k + 1) + q)) * C.y k
  rw [← C.hstep k]
  exact h.symm

theorem bb_pos (k : Nat) : 1 ≤ C.bb (k + 1) := by
  have hodd := C.hodd (k + 1)
  have hqp := C.hq_pos
  have hpos : 0 < 3 * C.y (k + 1) + q := by omega
  have he : (3 * C.y (k + 1) + q) % 2 = 0 := three_mul_add_even C.hq_odd hodd
  have h := v2_of_even hpos he
  show 1 ≤ v2 (3 * C.y (k + 1) + q)
  omega

/-- `B_k = b_1 + … + b_k`. -/
def BB (D : Cycle q) : Nat → Nat
  | 0 => 0
  | (k + 1) => BB D k + D.bb (k + 1)

/-- `c_k = 2^{b_k} c_{k−1} + 3^{k−1} q`, `c_0 = 0`. -/
def cc (D : Cycle q) : Nat → Nat
  | 0 => 0
  | (k + 1) => 2 ^ D.bb (k + 1) * cc D k + 3 ^ k * q

/-- **Closed form** (GROUND_TRUTH `y_k = (2^{B_k} M − c_k)/3^k`), written
    without subtraction: `3^k · y_k + c_k = 2^{B_k} · M`. -/
theorem closed_form (k : Nat) : 3 ^ k * C.y k + C.cc k = 2 ^ C.BB k * C.M := by
  induction k with
  | zero => simp [cc, BB, M]
  | succ k ih =>
    have hstep := C.bb_spec k
    simp only [cc, BB]
    have e1 : 3 ^ (k + 1) * C.y (k + 1) + (2 ^ C.bb (k + 1) * C.cc k + 3 ^ k * q)
            = 3 ^ k * (3 * C.y (k + 1) + q) + 2 ^ C.bb (k + 1) * C.cc k := by
      rw [Nat.pow_succ]
      simp [Nat.mul_add, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    rw [e1, hstep]
    have e2 : 3 ^ k * (2 ^ C.bb (k + 1) * C.y k) + 2 ^ C.bb (k + 1) * C.cc k
            = 2 ^ C.bb (k + 1) * (3 ^ k * C.y k + C.cc k) := by
      simp [Nat.mul_add, Nat.mul_left_comm]
    rw [e2, ih, Nat.pow_add]
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]

theorem cc_pos (k : Nat) : 0 < C.cc (k + 1) := by
  have hq := C.hq_pos
  have h3 : 0 < 3 ^ k := Nat.pow_pos (by decide)
  have : 0 < 3 ^ k * q := Nat.mul_pos h3 hq
  simp only [cc]
  omega

/-- **T6 (core).**  `y_k ≤ M` unpacks to `2^{B_k} · M ≤ 3^k · M + c_k`.
    (This is the *correct* form; the unconditional `B_k ≤ ⌊k·log₂3⌋` is FALSE —
    see the ❌ row of docs/GROUND_TRUTH.md.  The threshold version is NOT
    formalized here; see `Collatz/Unproved.lean`.) -/
theorem T6 (k : Nat) : 2 ^ C.BB k * C.M ≤ 3 ^ k * C.M + C.cc k := by
  have h := C.closed_form k
  have hy : C.y k ≤ C.M := C.hmax k
  have hle : 3 ^ k * C.y k ≤ 3 ^ k * C.M := Nat.mul_le_mul_left _ hy
  omega

/-- **T6, equivalence form** (GROUND_TRUTH states T6 as an `⟺`).  The
    inequality of `T6` is exactly the maximality constraint `y_k ≤ M`; nothing
    is lost by stating only the `→` direction, because the two are equivalent
    given the closed form. -/
theorem T6_iff (k : Nat) :
    2 ^ C.BB k * C.M ≤ 3 ^ k * C.M + C.cc k ↔ C.y k ≤ C.M := by
  have h := C.closed_form k
  have h3 : 0 < 3 ^ k := Nat.pow_pos (by decide)
  constructor
  · intro hle
    have : 3 ^ k * C.y k ≤ 3 ^ k * C.M := by omega
    exact Nat.le_of_mul_le_mul_left this h3
  · intro hy
    have : 3 ^ k * C.y k ≤ 3 ^ k * C.M := Nat.mul_le_mul_left _ hy
    omega

/-- **T2, in `b_k` notation:** `b₁ = 1`. -/
theorem T2_bb (hMq : q < C.M) : C.bb 1 = 1 := by
  have h := C.bb_spec 0
  exact T2_core C.hq_pos hMq (C.bb_pos 0) (C.hmax 1) h

/-- **T5, in `b_k` notation:** `q = 1`, `M ≥ 2` ⇒ `b₂ ≤ 2`. -/
theorem T5_bb (C : Cycle 1) (hM : 2 ≤ C.M) : C.bb 2 ≤ 2 :=
  C.T5 hM (C.bb_spec 1)

/-- **T5, in `b_k` notation, general `q`:** `11q < 7M` ⇒ `b₂ ≤ 2`. -/
theorem T5_bb_gen (hM : 11 * q < 7 * C.M) : C.bb 2 ≤ 2 :=
  C.T5_gen hM (C.bb_spec 1)

/-! ## T7 (the cycle equation) -/

/-- The cycle equation `M (2^{B_L} − 3^L) = c_L`, cleared of subtraction. -/
theorem T7_eq : 3 ^ C.L * C.M + C.cc C.L = 2 ^ C.BB C.L * C.M := by
  have h := C.closed_form C.L
  have hyL : C.y C.L = C.M := by
    have hp := C.hper 0
    show C.y C.L = C.y 0
    simpa using hp
  rw [hyL] at h
  exact h

/-- **T7.**  `c_L > 0` forces `2^{B_L} > 3^L`, i.e. `B/L > log₂ 3`.
    (No reals and no logarithms are needed to state this.) -/
theorem T7 : 3 ^ C.L < 2 ^ C.BB C.L := by
  have h := C.T7_eq
  have hL := C.hL
  have hpos : 0 < C.cc C.L := by
    obtain ⟨k, hk⟩ : ∃ k, C.L = k + 1 := ⟨C.L - 1, by omega⟩
    rw [hk]; exact C.cc_pos k
  have hM := C.M_pos
  -- avoid `Nat.lt_of_mul_lt_mul_right` (which drags in `Classical.choice`):
  -- argue by contraposition with `Nat.mul_le_mul_right` instead.
  rcases Nat.lt_or_ge (3 ^ C.L) (2 ^ C.BB C.L) with hcase | hcase
  · exact hcase
  · exfalso
    have hle : 2 ^ C.BB C.L * C.M ≤ 3 ^ C.L * C.M := Nat.mul_le_mul_right C.M hcase
    omega

end Cycle

end Collatz
