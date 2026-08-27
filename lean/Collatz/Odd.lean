/-
  Collatz/Odd.lean

  The odd step of the `3n+q` Syracuse map, defined by well-founded recursion,
  plus the "bridge lemma" that converts the *functional* form `S q n = m`
  into the *multiplicative* form `3n + q = 2^b * m` used by every later proof.

  Mathlib-free: Lean 4 core only.  Notation follows docs/GROUND_TRUTH.md.
-/

namespace Collatz

/-! ## 1. Definitions -/

/-- `v2 m` = the 2-adic valuation of `m` (convention: `v2 0 = 0`). -/
def v2 : Nat → Nat
  | 0 => 0
  | (n+1) => if (n+1) % 2 = 0 then v2 ((n+1) / 2) + 1 else 0
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

/-- `oddPart m` = `m / 2 ^ v2 m` (convention: `oddPart 0 = 0`). -/
def oddPart : Nat → Nat
  | 0 => 0
  | (n+1) => if (n+1) % 2 = 0 then oddPart ((n+1) / 2) else (n+1)
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

/-- The **Syracuse map** `S_q` of GROUND_TRUTH.md:
    `S_q n = (3n + q) / 2 ^ v2 (3n + q)`, defined for all `n` (total). -/
def S (q n : Nat) : Nat := oddPart (3 * n + q)

/-! ### Sanity checks.

Well-founded definitions are *sealed*, so `decide` gets stuck on them;
`simp [S, oddPart]` uses the generated equation lemmas and evaluates fine. -/

example : S 1 1 = 1 := by simp [S, oddPart]
example : S 1 7 = 11 := by simp [S, oddPart]
example : S 1 11 = 17 := by simp [S, oddPart]
example : S 1 5 = 1 := by simp [S, oddPart]
example : S 7 11 = 5 := by simp [S, oddPart]
example : S 7 5 = 11 := by simp [S, oddPart]
example : S 5 19 = 31 := by simp [S, oddPart]
example : S 5 31 = 49 := by simp [S, oddPart]
example : S 5 49 = 19 := by simp [S, oddPart]
example : v2 40 = 3 := by simp [v2]
example : v2 152 = 3 := by simp [v2]

/-! ## 2. Equation lemmas

`oddPart 0 = 0 := rfl` does *not* hold definitionally (WF definitions are not
transparent), so every unfolding must go through these four lemmas. -/

theorem oddPart_of_odd {m : Nat} (h : m % 2 = 1) : oddPart m = m := by
  cases m with
  | zero => omega
  | succ n => rw [oddPart]; simp [h]

theorem oddPart_of_even {m : Nat} (hpos : 0 < m) (h : m % 2 = 0) :
    oddPart m = oddPart (m / 2) := by
  cases m with
  | zero => omega
  | succ n => rw [oddPart]; simp [h]

theorem v2_of_odd {m : Nat} (h : m % 2 = 1) : v2 m = 0 := by
  cases m with
  | zero => omega
  | succ n => rw [v2]; simp [h]

theorem v2_of_even {m : Nat} (hpos : 0 < m) (h : m % 2 = 0) :
    v2 m = v2 (m / 2) + 1 := by
  cases m with
  | zero => omega
  | succ n => rw [v2]; simp [h]

/-- Halving commutes with `oddPart`. -/
theorem oddPart_two_mul {m : Nat} (hm : 0 < m) : oddPart (2 * m) = oddPart m := by
  have hpos : 0 < 2 * m := by omega
  have he : (2 * m) % 2 = 0 := by omega
  have h := oddPart_of_even hpos he
  have e : 2 * m / 2 = m := by omega
  rw [e] at h
  exact h

/-! ## 3. Structural facts -/

/-- The odd part of a positive number is odd. -/
theorem oddPart_mod_two {m : Nat} (hpos : 0 < m) : oddPart m % 2 = 1 := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    rcases Nat.mod_two_eq_zero_or_one m with h2 | h2
    · have hlt : m / 2 < m := Nat.div_lt_self hpos (by decide)
      have hp2 : 0 < m / 2 := by omega
      rw [oddPart_of_even hpos h2]
      exact ih (m / 2) hlt hp2
    · rw [oddPart_of_odd h2]; exact h2

theorem oddPart_pos {m : Nat} (hpos : 0 < m) : 0 < oddPart m := by
  have := oddPart_mod_two hpos; omega

/-- **The bridge lemma**: `2 ^ v2 m * oddPart m = m`.

This is what turns the *functional* statement `S q n = m` into the
*multiplicative* statement `3n + q = 2^b * m` that all cycle arguments use. -/
theorem two_pow_v2_mul_oddPart {m : Nat} (hpos : 0 < m) :
    2 ^ v2 m * oddPart m = m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    rcases Nat.mod_two_eq_zero_or_one m with h2 | h2
    · have hlt : m / 2 < m := Nat.div_lt_self hpos (by decide)
      have hp2 : 0 < m / 2 := by omega
      have hrec := ih (m / 2) hlt hp2
      rw [oddPart_of_even hpos h2, v2_of_even hpos h2, Nat.pow_succ]
      calc 2 ^ v2 (m / 2) * 2 * oddPart (m / 2)
          = 2 ^ v2 (m / 2) * oddPart (m / 2) * 2 := Nat.mul_right_comm _ _ _
        _ = (m / 2) * 2 := by rw [hrec]
        _ = m := by omega
    · rw [oddPart_of_odd h2, v2_of_odd h2, Nat.pow_zero, Nat.one_mul]

/-- For odd `n` and odd `q`, `3n + q` is even: the step really does halve. -/
theorem three_mul_add_even {q n : Nat} (hq : q % 2 = 1) (hn : n % 2 = 1) :
    (3 * n + q) % 2 = 0 := by omega

/-- **Step relation, multiplicative form.**  For odd `q` and odd `n`,
    `3n + q = 2 ^ b * S q n` with `b = v2 (3n+q) ≥ 1`, and `S q n` is odd. -/
theorem S_spec {q n : Nat} (hq : q % 2 = 1) (hn : n % 2 = 1) :
    ∃ b, 1 ≤ b ∧ 3 * n + q = 2 ^ b * S q n ∧ (S q n) % 2 = 1 := by
  have hpos : 0 < 3 * n + q := by omega
  refine ⟨v2 (3 * n + q), ?_, ?_, ?_⟩
  · have he : (3 * n + q) % 2 = 0 := three_mul_add_even hq hn
    have := v2_of_even hpos he
    omega
  · exact (two_pow_v2_mul_oddPart hpos).symm
  · exact oddPart_mod_two hpos

/-- `S q n` is odd whenever `q` and `n` are. -/
theorem S_odd {q n : Nat} (hq : q % 2 = 1) (hn : n % 2 = 1) : (S q n) % 2 = 1 := by
  have hpos : 0 < 3 * n + q := by omega
  exact oddPart_mod_two hpos

theorem S_pos {q n : Nat} (hq : q % 2 = 1) (hn : n % 2 = 1) : 0 < S q n := by
  have := S_odd hq hn; omega

end Collatz
