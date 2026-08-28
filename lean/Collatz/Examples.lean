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
import Collatz.Minimum
import Collatz.Reach
import Collatz.Periodic
import Collatz.Census

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

/-! ## 4. The `q = 17` cycle {5, 1}:  5 → 1 → 5

This one exists to be a *counterexample*.  Its minimum is `m = 1 ≤ 17 = q`, so
it sits outside the hypothesis of `Cycle.min_bb_out` — and the conclusion fails
for it: the step out of its minimum is `3·1 + 17 = 20 = 2² · 5`, **two**
halvings, not one.  So `q < m` is not a convenience, and the machine says so. -/

def cycle17 : Cycle 17 where
  L := 2
  y := fun i => if i % 2 = 0 then 5 else 1
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
    subst hk
    decide

example : cycle17.M = 5 := rfl
example : cycle17.L = 2 := rfl

/-! ### The derived minimum agrees with the arithmetic one -/

theorem cycle5_minIdx : cycle5.minIdx = 2 := rfl
theorem cycle5_m : cycle5.m = 19 := rfl
theorem cycle7_m : cycle7.m = 5 := rfl
theorem cycle17_m : cycle17.m = 1 := rfl
theorem trivial_m : trivialCycle.m = 1 := rfl

/-- `Cycle.m_le` on a real cycle: nothing in `cycle5` is below 19. -/
theorem cycle5_m_le (i : Nat) : 19 ≤ cycle5.y i := cycle5.m_le i

/-! ### `cycle5` inhabits the hypothesis, and the mirror holds there -/

theorem cycle5_q_lt_m : 5 < cycle5.m := by decide

/-- The step out of the minimum is a single halving. -/
theorem cycle5_min_out : cycle5.bb cycle5.minIdx = 1 :=
  cycle5.min_bb_out cycle5_q_lt_m

/-- The mirror of T1: `3m + q ≡ 2 (mod 4)`, against `3M + q ≡ 0` at the top. -/
theorem cycle5_min_mod4 : (3 * cycle5.m + 5) % 4 = 2 :=
  cycle5.min_mod4 cycle5_q_lt_m

theorem cycle5_max_mod4 : (3 * cycle5.M + 5) % 4 = 0 := cycle5.T1

/-- `m ≡ q + 2 (mod 4)` while `M ≡ q (mod 4)` — the two ends, two apart. -/
theorem cycle5_ends_mod4 : cycle5.m % 4 = (5 + 2) % 4 ∧ cycle5.M % 4 = 5 % 4 :=
  ⟨cycle5.min_mod4' cycle5_q_lt_m, cycle5.T1_mod4⟩

/-- The backward hop *into* the minimum takes at least two halvings. -/
theorem cycle5_min_in : 2 ≤ cycle5.bb (cycle5.minIdx + 1) := cycle5.min_bb_in

/-! ### `cycle17` falls outside it, and the conclusion falls too -/

theorem cycle17_minIdx : cycle17.minIdx = 1 := rfl

theorem cycle17_bb_out : cycle17.bb cycle17.minIdx = 2 := by
  show Collatz.v2 (3 * cycle17.y 1 + 17) = 2
  have h : cycle17.y 1 = 1 := rfl
  rw [h]
  simp [v2]

/-- **The hypothesis `q < m` of `Cycle.min_bb_out` cannot be dropped.**
    `cycle17` is a genuine `S_17`-cycle that fails it, and fails the conclusion
    too.

    It does not, on its own, show that `q < m` is the *right* hypothesis:
    `cycle17` also fails `q < M`, so it cannot tell the two apart.  `cycle37`
    below can. -/
theorem min_bb_out_needs_hypothesis :
    ¬ (17 < cycle17.m) ∧ cycle17.bb cycle17.minIdx ≠ 1 := by
  refine ⟨by decide, ?_⟩
  rw [cycle17_bb_out]
  decide

/-! ## 5. The `q = 37` cycle {65, 31, 29}:  29 → 31 → 65 → 29

The witness that separates the two hypotheses.  Here `m = 29 ≤ 37 = q < 65 = M`,
so `q < M` — the hypothesis of T2/T3/T4 at the *top* end — holds, while `q < m`
fails.  And the mirror's conclusion fails with it: `3·29 + 37 = 124 = 2² · 31`.
So the minimum's mirror really does need its own hypothesis; it does not inherit
the maximum's. -/

def cycle37 : Cycle 37 where
  L := 3
  y := fun i => if i % 3 = 0 then 65 else if i % 3 = 1 then 31 else 29
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

theorem cycle37_M : cycle37.M = 65 := rfl
theorem cycle37_minIdx : cycle37.minIdx = 2 := rfl
theorem cycle37_m : cycle37.m = 29 := rfl

theorem cycle37_bb_out : cycle37.bb cycle37.minIdx = 2 := by
  show Collatz.v2 (3 * cycle37.y 2 + 37) = 2
  have h : cycle37.y 2 = 29 := rfl
  rw [h]
  simp [v2]

/-- **The minimum's mirror needs `q < m` specifically, not the maximum's
    `q < M`.**  `cycle37` satisfies `q < M`, fails `q < m`, and fails the
    conclusion — so the hypothesis at the top end does not carry to the bottom.
    This is the Lean-side counterpart of the census cycles recorded in
    docs/CERTIFY.md, of which 167 have `m ≤ q < M` exactly like this one. -/
theorem min_bb_out_needs_its_own_hypothesis :
    37 < cycle37.M ∧ ¬ (37 < cycle37.m) ∧ cycle37.bb cycle37.minIdx ≠ 1 := by
  refine ⟨by decide, by decide, ?_⟩
  rw [cycle37_bb_out]
  decide

/-- The hypothesis is **sufficient, not necessary**: `cycle7` fails `q < m`
    (`m = 5 ≤ 7`) and yet its minimum does leave by a single halving.  So the
    census cycles that break the mirror are evidence that the hypothesis cannot
    be dropped — not that every cycle without it breaks. -/
theorem min_bb_out_hypothesis_not_necessary :
    ¬ (7 < cycle7.m) ∧ cycle7.bb cycle7.minIdx = 1 := by
  refine ⟨by decide, ?_⟩
  show Collatz.v2 (3 * cycle7.y 1 + 7) = 1
  have h : cycle7.y 1 = 5 := rfl
  rw [h]
  simp [v2]

/-! ## 6. `L ≤ |R(O)|` on real cycles

The bound of `Collatz/Reach.lean`, applied where cycles exist.  `#eval` puts the
counts at 10 and 19 (matching `collatz_maxodd.structure.reachable_set`), against
lengths 3 and 8 — but the kernel cannot reduce `oddPart`, so what is *proved*
here is the inequality, not the value of its right-hand side. -/

theorem cycle5_length_le_reach :
    cycle5.L ≤ countLE (Cycle.inR 5 cycle5.M cycle5.M) cycle5.M :=
  cycle5.length_le_reach_M

theorem cycle7_length_le_reach :
    cycle7.L ≤ countLE (Cycle.inR 7 cycle7.M cycle7.M) cycle7.M :=
  cycle7.length_le_reach_M

theorem cycle37_length_le_reach :
    cycle37.L ≤ countLE (Cycle.inR 37 cycle37.M cycle37.M) cycle37.M :=
  cycle37.length_le_reach_M

/-- `L ≤ M`, on a real cycle: `3 ≤ 49`. -/
theorem cycle5_length_le_M : cycle5.L ≤ cycle5.M := cycle5.length_le_M

/-! ## 7. Periodic points and the `−1` witness

`Collatz/Periodic.lean` proves that *any* periodic point of a halving pattern
satisfies the cycle equation, with no cycle in the hypotheses.  (Existence of a
periodic point is a separate matter: over `ℤ` most patterns have none — the
solution is only rational.  See that file's header.)  Here are the ones the page
quotes. -/

/-- `c_L = 3^L − 2^L` for the all-ones pattern: 1, 5, 19, 65, … -/
theorem Pc_ones_1 : Pc 1 ones 1 = 1 := by decide
theorem Pc_ones_2 : Pc 1 ones 2 = 5 := by decide
theorem Pc_ones_3 : Pc 1 ones 3 = 19 := by decide
theorem Pc_ones_4 : Pc 1 ones 4 = 65 := by decide

theorem PB_ones_3 : PB ones 3 = 3 := by decide

/-- **The witness, concretely.**  `(−1)·(2³ − 3³) = 19 = c₃`. -/
theorem ones_three_equation : (-1 : Int) * (2 ^ (3 : Nat) - 3 ^ (3 : Nat)) = 19 := by decide

/-- **The witness, at every length.**  The all-ones pattern's periodic point is
    `−1` for every `L ≥ 1`, and `−1` is not a natural number.  It passes every
    congruence test at every depth (`Collatz.all_digits_two`) and is not a cycle.
    That gap is invisible to a sieve. -/
theorem ones_witness {L : Nat} (hL : 0 < L) {y : Int} (P : IsPeriodic 1 ones L y) :
    y = -1 ∧ ¬ ∃ n : Nat, 0 < n ∧ (n : Int) = y := by
  have hy := minus_one_of_ones hL P
  refine ⟨hy, ?_⟩
  rintro ⟨n, hn, he⟩
  rw [hy] at he
  omega

/-- The trivial cycle is the constant pattern `b = 2`, and `const_positive_integer`
    says it is the *only* constant pattern reaching a positive integer. -/
theorem trivial_is_const_two : (1 : Int) * (2 ^ (2 : Nat) - 3) = 1 := by decide

theorem only_b_two {b : Nat} {y : Int} (h : y * (2 ^ b - 3) = 1) (hy : 0 < y) :
    b = 2 ∧ y = 1 := const_positive_integer h hy

/-- …and `b = 2` is inhabited, so that is a characterisation, not a vacuity. -/
theorem const_two_exists : Nonempty (IsPeriodic 1 (const 2) 1 1) := ⟨constTwoPeriodic⟩

/-- A real cycle really is a positive-integer periodic point of its own pattern. -/
theorem cycle5_is_periodic :
    (cycle5.M : Int) * (2 ^ cycle5.BB cycle5.L - 3 ^ cycle5.L) = (cycle5.cc cycle5.L : Int) :=
  cycle5.T7_from_periodic

theorem cycle7_is_periodic :
    (cycle7.M : Int) * (2 ^ cycle7.BB cycle7.L - 3 ^ cycle7.L) = (cycle7.cc cycle7.L : Int) :=
  cycle7.T7_from_periodic

/-! ## 8. The census theorems, on real cycles

`cycle5` is the `q = 5` cycle `{49, 31, 19}` with `L = 3, B = 5`, so
`2^B − 3^L = 32 − 27 = 5 = q` — an *exact hit*, the burst case.  It is the first
cycle on the page and it is there because of this. -/

theorem cycle5_coprime : Nat.gcd cycle5.M 5 = 1 := by decide

/-- `q ∣ 2^B − 3^L`, on a cycle that exists. -/
theorem cycle5_q_dvd : (5 : Nat) ∣ 2 ^ cycle5.BB cycle5.L - 3 ^ cycle5.L :=
  cycle5.q_dvd_sub cycle5_coprime

/-- And `q = 5` is an exact hit: `2^5 − 3^3 = 5`. -/
theorem cycle5_exact_hit : 2 ^ cycle5.BB cycle5.L - 3 ^ cycle5.L = 5 := by
  have hBB : cycle5.BB 3 = 5 := by
    have h1 : cycle5.y 1 = 31 := rfl
    have h2 : cycle5.y 2 = 19 := rfl
    have h3 : cycle5.y 3 = 49 := rfl
    simp [Cycle.BB, Cycle.bb, h1, h2, h3, v2]
  show 2 ^ cycle5.BB 3 - 3 ^ 3 = 5
  rw [hBB]

/-- So the burst identity holds for it: `M · q = c_L`, i.e. `49 · 5 = 245`. -/
theorem cycle5_burst : cycle5.M * 5 = cycle5.cc cycle5.L :=
  cycle5.burst cycle5_exact_hit

/-- `q = 7`'s cycle `{11, 5}` is another exact hit: `2^4 − 3^2 = 7 = q`. -/
theorem cycle7_coprime : Nat.gcd cycle7.M 7 = 1 := by decide

theorem cycle7_q_dvd : (7 : Nat) ∣ 2 ^ cycle7.BB cycle7.L - 3 ^ cycle7.L :=
  cycle7.q_dvd_sub cycle7_coprime

theorem cycle7_exact_hit : 2 ^ cycle7.BB cycle7.L - 3 ^ cycle7.L = 7 := by
  have hBB : cycle7.BB 2 = 4 := by
    have h1 : cycle7.y 1 = 5 := rfl
    have h2 : cycle7.y 2 = 11 := rfl
    simp [Cycle.BB, Cycle.bb, h1, h2, v2]
  show 2 ^ cycle7.BB 2 - 3 ^ 2 = 7
  rw [hBB]

/-- **A non-degenerate witness.**  `cycle5` and `cycle7` are both *exact* hits,
    where `q ∣ 2^B − 3^L` collapses to `q ∣ q`.  `cycle17` is not:
    `2^7 − 3^2 = 119 = 7 · 17`, so the divisibility has quotient 7 and the
    general theorem is doing real work. -/
theorem cycle17_coprime : Nat.gcd cycle17.M 17 = 1 := by decide

theorem cycle17_q_dvd : (17 : Nat) ∣ 2 ^ cycle17.BB cycle17.L - 3 ^ cycle17.L :=
  cycle17.q_dvd_sub cycle17_coprime

theorem cycle17_not_an_exact_hit : 2 ^ cycle17.BB cycle17.L - 3 ^ cycle17.L = 119 := by
  have hBB : cycle17.BB 2 = 7 := by
    have h1 : cycle17.y 1 = 1 := rfl
    have h2 : cycle17.y 2 = 5 := rfl
    simp [Cycle.BB, Cycle.bb, h1, h2, v2]
  show 2 ^ cycle17.BB 2 - 3 ^ 2 = 119
  rw [hBB]

/-- `trivialCycle` really does have `(L, B) = (1, 2)`. -/
theorem trivial_L_BB : trivialCycle.L = 1 ∧ trivialCycle.BB 1 = 2 := by
  refine ⟨rfl, ?_⟩
  have h1 : trivialCycle.y 1 = 1 := rfl
  simp [Cycle.BB, Cycle.bb, h1, v2]

/-- **`q = 1` gets exactly one burst, and it is the trivial cycle.**  Any
    `(L, B)` with `L ≥ 1` solving `2^B = 3^L + 1` is `(1, 2)`; and `(1, 2)` is
    exactly `trivialCycle`'s `(L, B)`, so the characterisation is not vacuous
    and the unique solution really is the cycle everybody knows. -/
theorem q1_burst_is_exactly_the_trivial_cycle :
    (∀ L B : Nat, 1 ≤ L → 2 ^ B = 3 ^ L + 1 → L = 1 ∧ B = 2)
    ∧ trivialCycle.L = 1 ∧ trivialCycle.BB 1 = 2 :=
  ⟨fun _ _ hL h => q1_burst hL h, trivial_L_BB.1, trivial_L_BB.2⟩

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
