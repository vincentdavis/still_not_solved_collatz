/-
  Collatz/Examples.lean

  Concrete instances of `Cycle`, so that the structure is demonstrably
  NON-VACUOUS in the regimes the theorems care about, plus worked examples of
  the cycle-free lemmas.

  Why this file matters: `Cycle q` is a *postulated* backward orbit.  If its
  fields were subtly inconsistent, every theorem about it would be vacuously
  true.  The three instances below rule that out:

    * `trivialCycle : Cycle 1`  — the fixed point {1}, `L = 1`, `M = 1 = q`
    * `cycle7 : Cycle 7`        — the 2-cycle {11, 5}, `L = 2`, `M = 11 > q`
    * `cycle5 : Cycle 5`        — the 3-cycle {49, 31, 19}, `L = 3`, `M = 49 > q`

  `cycle5` in particular inhabits the `L ≥ 3`, `M > q` regime that T2/T3/T5 are
  about, so those theorems are not vacuously true.
-/
import Collatz.Cycle

namespace Collatz

/-! ## 1. The `q = 1` fixed point {1} -/

def trivialCycle : Cycle 1 where
  L := 1
  y := fun _ => 1
  hL := by decide
  hq_pos := by decide
  hq_odd := by decide
  hq_three := by decide
  hodd := fun _ => by decide
  hstep := fun _ => by simp [S, oddPart]
  hmax := fun _ => by decide
  hper := fun _ => rfl
  hmin := fun _ h1 h2 => by omega

example : trivialCycle.M = 1 := rfl
example : trivialCycle.L = 1 := rfl
example : (3 * trivialCycle.M + 1) % 4 = 0 := trivialCycle.T1
example : trivialCycle.M % 4 = 1 := trivialCycle.T1_q1
example : trivialCycle.M % 16 ≠ 9 := trivialCycle.T8

/-! ## 2. The `q = 7` cycle {11, 5}:  11 → 5 → 11 -/

def cycle7 : Cycle 7 where
  L := 2
  y := fun i => if i % 2 = 0 then 11 else 5
  hL := by decide
  hq_pos := by decide
  hq_odd := by decide
  hq_three := by decide
  hodd := fun i => by
    rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]
  hstep := fun i => by
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · have h2 : (i + 1) % 2 = 1 := by omega
      simp [h, h2, S, oddPart]
    · have h2 : (i + 1) % 2 = 0 := by omega
      simp [h, h2, S, oddPart]
  hmax := fun i => by
    rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]
  hper := fun i => by
    have h : (i + 2) % 2 = i % 2 := by omega
    simp [h]
  hmin := fun k h1 h2 => by
    have hk : k = 1 := by omega
    subst hk; decide

example : cycle7.M = 11 := rfl
example : cycle7.L = 2 := rfl
example : cycle7.y 1 = 5 := rfl
/-- `M = 11 > q = 7`, so T2 applies: `b₁ = 1`. -/
example : cycle7.bb 1 = 1 := cycle7.T2_bb (by decide)
example : (3 * cycle7.M + 7) % 4 = 0 := cycle7.T1
example : cycle7.M % 4 = 7 % 4 := cycle7.T1_mod4
example : (2 * cycle7.M) % 3 = 7 % 3 := cycle7.T2_mod3 (by decide)

/-! ## 3. The `q = 5` cycle {49, 31, 19}:  49 → 19 → 31 → 49

    Backwards from the maximum: `y 0 = 49`, `y 1 = 31`, `y 2 = 19`.
    This is the cycle named in the ❌ row of docs/GROUND_TRUTH.md
    (`q = 5`, `M = 49`, `B_3 = 5 > 4 = ⌊3 log₂ 3⌋`). -/

def cycle5 : Cycle 5 where
  L := 3
  y := fun i => if i % 3 = 0 then 49 else if i % 3 = 1 then 31 else 19
  hL := by decide
  hq_pos := by decide
  hq_odd := by decide
  hq_three := by decide
  hodd := fun i => by
    rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with h | h | h <;>
      simp [h]
  hstep := fun i => by
    rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with h | h | h
    · have h2 : (i + 1) % 3 = 1 := by omega
      simp [h, h2, S, oddPart]
    · have h2 : (i + 1) % 3 = 2 := by omega
      simp [h, h2, S, oddPart]
    · have h2 : (i + 1) % 3 = 0 := by omega
      simp [h, h2, S, oddPart]
  hmax := fun i => by
    rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with h | h | h <;>
      simp [h]
  hper := fun i => by
    have h : (i + 3) % 3 = i % 3 := by omega
    simp [h]
  hmin := fun k h1 h2 => by
    rcases (show k = 1 ∨ k = 2 by omega) with h | h <;> subst h <;> decide

example : cycle5.M = 49 := rfl
example : cycle5.L = 3 := rfl
example : cycle5.y 1 = 31 := rfl
example : cycle5.y 2 = 19 := rfl
/-- `L = 3`, `M = 49 > q = 5`: the regime T2/T5 are about is inhabited. -/
example : cycle5.bb 1 = 1 := cycle5.T2_bb (by decide)
/-- T5 (sharp general-`q` form): `11·5 = 55 < 343 = 7·49`, so `b₂ ≤ 2`. -/
example : cycle5.bb 2 ≤ 2 := cycle5.T5_bb_gen (by decide)
example : (3 * cycle5.M + 5) % 4 = 0 := cycle5.T1
example : cycle5.M % 4 = 5 % 4 := cycle5.T1_mod4
example : 3 ≤ cycle5.M := cycle5.M_ge_three_of_L (by decide)
example : cycle5.y 2 % 3 ≠ 0 := cycle5.T0 2

/-! ### `cycle5` witnesses the ❌ row of docs/GROUND_TRUTH.md

`b₁ = b₂ = 1`, `b₃ = 3`, so `B₃ = 5` and `2^{B₃} = 32 > 27 = 3³`.  The claim
`B_k ≤ ⌊k · log₂ 3⌋` (here `⌊3 log₂ 3⌋ = 4`) is therefore FALSE without a
largeness hypothesis on `M`.  The *correct* statement, `Cycle.T6`, still holds
— here with equality, because `y₃ = M`. -/

example : cycle5.bb 1 = 1 := by simp [Cycle.bb, cycle5, v2]
example : cycle5.bb 2 = 1 := by simp [Cycle.bb, cycle5, v2]
example : cycle5.bb 3 = 3 := by simp [Cycle.bb, cycle5, v2]
example : cycle5.BB 3 = 5 := by simp [Cycle.BB, Cycle.bb, cycle5, v2]
example : cycle5.cc 3 = 245 := by simp [Cycle.cc, Cycle.bb, cycle5, v2]

/-- `2^{B₃} = 32 > 27 = 3³`: the unconditional floor rule fails on a real cycle. -/
example : ¬ (2 ^ cycle5.BB 3 ≤ 3 ^ 3) := by
  have h : cycle5.BB 3 = 5 := by simp [Cycle.BB, Cycle.bb, cycle5, v2]
  rw [h]; decide

/-- …but `Cycle.T6` (the correct inequality) holds, with equality here. -/
example : 2 ^ cycle5.BB 3 * cycle5.M ≤ 3 ^ 3 * cycle5.M + cycle5.cc 3 :=
  cycle5.T6 3

/-! ## 4. Worked examples of the cycle-free lemmas -/

/-- The user's seed observation: `7 ↦ 11 > 7`, so 7 is never a cycle maximum. -/
example : (7:Nat) < S 1 7 := lt_S_of_three_mod_four (by decide)

/-- 11 is excluded too — but by the *same* mod-4 reason (`11 ≡ 3 mod 4`,
    `11 ↦ 17`), **not** because reaching 11 needs a bigger odd number.
    Indeed `S 1 7 = 11` with `7 < 11`, so 11 *is* reached from below. -/
example : (11:Nat) < S 1 11 := lt_S_of_three_mod_four (by decide)
example : S 1 7 = 11 := by simp [S, oddPart]

/-- T0: 9 is an odd multiple of 3, so no odd number maps to it under `S_1`. -/
example {y : Nat} (hy : y % 2 = 1) : S 1 y ≠ 9 :=
  no_odd_pred_of_three_dvd (by decide) (by decide) (by decide) hy

/-- Lemma U, existence half: `17 ≡ 2 (mod 3)`, so 17 has the odd predecessor
    `(2·17 − 1)/3 = 11`. -/
example : S 1 11 = 17 := by simp [S, oddPart]

/-- Lemma U, non-existence half: `13 ≡ 1 (mod 3)`, so 13 has *no* odd
    predecessor at or below itself. -/
example : ¬ ∃ y, 0 < y ∧ y % 2 = 1 ∧ y ≤ 13 ∧ S 1 y = 13 := by
  intro h
  have := (pred_le_iff_q1 (p := 13) (by decide) (by decide)).mp h
  omega

/-- Lemma U, uniqueness half, instantiated at `p = 17`. -/
example {y : Nat} (hy : 0 < y) (hyo : y % 2 = 1) (hle : y ≤ 17)
    (hs : S 1 y = 17) : y = 11 :=
  pred_le_unique_q1 hy (by decide) hyo (by decide) hle (by decide) hs
    (by simp [S, oddPart])

end Collatz
