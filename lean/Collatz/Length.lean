/-
  Collatz/Length.lean

  A LOWER BOUND ON THE LENGTH OF A NONTRIVIAL CYCLE.

  The published cycle-length bounds (Steiner 1977, Simons–de Weger 2005,
  Hercher 2023) all run through Baker's theorem on linear forms in logarithms,
  which bounds how close `2^B / 3^L` can get to 1.  Lean 4 core has no real
  numbers, let alone Baker.  So the Baker input is taken as an explicit
  HYPOTHESIS, stated in ℕ, and everything downstream of it is proved:

      hbaker :  3^L * L^κ + c * 3^L  ≤  2^B * L^κ
                (i.e.  2^B / 3^L  ≥  1 + c / L^κ)

      ⟹  3 * m * c  ≤  2 * L^(κ+1)          (`length_bound`)

  where `m` is the cycle minimum.  So a cycle of a system verified up to `m`
  must have `L^(κ+1) ≥ 3mc/2`.

  THE POINT: no analysis is needed.  The usual derivation takes logarithms of
  `2^B = ∏ (3 + 1/x_j)`; here the same content is carried by the exact integer
  identity

      2^B * ∏ x_j  =  ∏ (3 * x_j + q)                    (`prodG_eq`)

  and by an elementary Bernoulli-style inequality on naturals
  (`pow_succ_le`).  Both are plain inductions.

  NOVELTY: none.  This is the classical Crandall-style squeeze, rearranged to
  avoid ℝ.  The bound it yields is weaker than the published ones; the value
  here is that it is machine-checked and choice-free.
-/
import Collatz.Odd
import Collatz.Core
import Collatz.Cycle
import Collatz.Examples

namespace Collatz
namespace Cycle

variable {q : Nat} (C : Cycle q)

/-! ## 1. Finite products and sums along the cycle -/

/-- `∏_{k < n} y (o + k)`. -/
def prodFrom (C : Cycle q) (o : Nat) : Nat → Nat
  | 0     => 1
  | n + 1 => C.y (o + n) * C.prodFrom o n

/-- `∏_{k < n} (3 * y (k+1) + q)` — the numerators of the backward hops. -/
def prodG (C : Cycle q) : Nat → Nat
  | 0     => 1
  | n + 1 => (3 * C.y (n + 1) + q) * C.prodG n

theorem prodFrom_pos (C : Cycle q) (o : Nat) : ∀ n, 0 < C.prodFrom o n
  | 0     => Nat.one_pos
  | n + 1 => Nat.mul_pos (C.y_pos _) (C.prodFrom_pos o n)

/-- **The exact identity.**  `∏ (3 y_{k+1} + q) = 2 ^ B * ∏ y_k`.

    This is what replaces "take logarithms of `2^B = ∏ (3 + 1/x_j)`". -/
theorem prodG_eq : ∀ n, C.prodG n = 2 ^ C.BB n * C.prodFrom 0 n := by
  intro n
  induction n with
  | zero => simp [prodG, Cycle.BB, prodFrom]
  | succ n ih =>
      show (3 * C.y (n + 1) + q) * C.prodG n
         = 2 ^ (C.BB n + C.bb (n + 1)) * (C.y (0 + n) * C.prodFrom 0 n)
      rw [ih, C.bb_spec n, Nat.pow_add, Nat.zero_add]
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Shifting the product window by one costs a factor `y n / y 0`. -/
theorem prodFrom_shift : ∀ n, C.prodFrom 1 n * C.y 0 = C.prodFrom 0 n * C.y n := by
  intro n
  induction n with
  | zero => simp [prodFrom]
  | succ n ih =>
      show C.y (1 + n) * C.prodFrom 1 n * C.y 0
         = C.y (0 + n) * C.prodFrom 0 n * C.y (n + 1)
      have e1 : 1 + n = n + 1 := by omega
      have e2 : 0 + n = n := by omega
      rw [e1, e2]
      calc C.y (n + 1) * C.prodFrom 1 n * C.y 0
          = C.y (n + 1) * (C.prodFrom 1 n * C.y 0) := by simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ = C.y (n + 1) * (C.prodFrom 0 n * C.y n) := by rw [ih]
        _ = C.y n * C.prodFrom 0 n * C.y (n + 1) := by simp [Nat.mul_comm, Nat.mul_assoc]

/-- Around a full turn the two windows agree, because `y L = y 0`. -/
theorem prodFrom_one_eq_zero : C.prodFrom 1 C.L = C.prodFrom 0 C.L := by
  have h := C.prodFrom_shift C.L
  have hy : C.y C.L = C.y 0 := by have := C.hper 0; simpa using this
  rw [hy] at h
  exact Nat.eq_of_mul_eq_mul_right (C.y_pos 0) h

/-! ## 2. The squeeze -/

/-- Every factor obeys `m (3y + q) ≤ (3m + q) y` when `m ≤ y`; multiply up. -/
theorem prod_squeeze {m : Nat} (hm : ∀ i, m ≤ C.y i) :
    ∀ n, m ^ n * C.prodG n ≤ (3 * m + q) ^ n * C.prodFrom 1 n := by
  intro n
  induction n with
  | zero => simp [prodG, prodFrom]
  | succ n ih =>
      show m ^ (n + 1) * ((3 * C.y (n + 1) + q) * C.prodG n)
         ≤ (3 * m + q) ^ (n + 1) * (C.y (1 + n) * C.prodFrom 1 n)
      have e : 1 + n = n + 1 := by omega
      rw [e, Nat.pow_succ, Nat.pow_succ]
      have step : m * (3 * C.y (n + 1) + q) ≤ (3 * m + q) * C.y (n + 1) := by
        have hmy := hm (n + 1)
        have h1 : m * (3 * C.y (n + 1) + q) = 3 * (m * C.y (n + 1)) + m * q := by
          simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
        have h2 : (3 * m + q) * C.y (n + 1) = 3 * (m * C.y (n + 1)) + q * C.y (n + 1) := by
          simp [Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        have h3 : m * q ≤ q * C.y (n + 1) := by
          calc m * q = q * m := Nat.mul_comm _ _
            _ ≤ q * C.y (n + 1) := Nat.mul_le_mul_left q hmy
        omega
      calc m ^ n * m * ((3 * C.y (n + 1) + q) * C.prodG n)
          = (m * (3 * C.y (n + 1) + q)) * (m ^ n * C.prodG n) := by simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ ≤ ((3 * m + q) * C.y (n + 1)) * ((3 * m + q) ^ n * C.prodFrom 1 n) :=
            Nat.mul_le_mul step ih
        _ = (3 * m + q) ^ n * (3 * m + q) * (C.y (n + 1) * C.prodFrom 1 n) := by simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- **The key inequality**, with every product cancelled away:
    `m ^ L * 2 ^ B ≤ (3m + q) ^ L`. -/
theorem pow_le_of_min {m : Nat} (hm : ∀ i, m ≤ C.y i) :
    m ^ C.L * 2 ^ C.BB C.L ≤ (3 * m + q) ^ C.L := by
  have h := C.prod_squeeze hm C.L
  rw [C.prodG_eq C.L, C.prodFrom_one_eq_zero] at h
  have hp := C.prodFrom_pos 0 C.L
  have h' : (m ^ C.L * 2 ^ C.BB C.L) * C.prodFrom 0 C.L
          ≤ ((3 * m + q) ^ C.L) * C.prodFrom 0 C.L := by
    calc (m ^ C.L * 2 ^ C.BB C.L) * C.prodFrom 0 C.L
        = m ^ C.L * (2 ^ C.BB C.L * C.prodFrom 0 C.L) := Nat.mul_assoc _ _ _
      _ ≤ (3 * m + q) ^ C.L * C.prodFrom 0 C.L := h
  exact Nat.le_of_mul_le_mul_right h' hp

/-! ## 2b. The other half of the sandwich, and the single-halving count -/

/-- Mirror of `prod_squeeze` at the top end: `(3M+q)·y ≤ M·(3y+q)` when `y ≤ M`. -/
theorem prod_squeeze_max :
    ∀ n, (3 * C.M + q) ^ n * C.prodFrom 1 n ≤ C.M ^ n * C.prodG n := by
  intro n
  induction n with
  | zero => simp [prodG, prodFrom]
  | succ n ih =>
      show (3 * C.M + q) ^ (n + 1) * (C.y (1 + n) * C.prodFrom 1 n)
         ≤ C.M ^ (n + 1) * ((3 * C.y (n + 1) + q) * C.prodG n)
      have e : 1 + n = n + 1 := by omega
      rw [e, Nat.pow_succ, Nat.pow_succ]
      have step : (3 * C.M + q) * C.y (n + 1) ≤ C.M * (3 * C.y (n + 1) + q) := by
        have hyM := C.hmax (n + 1)
        have h1 : (3 * C.M + q) * C.y (n + 1)
                = 3 * (C.M * C.y (n + 1)) + q * C.y (n + 1) := by
          simp [Nat.add_mul, Nat.mul_assoc]
        have h2 : C.M * (3 * C.y (n + 1) + q)
                = 3 * (C.M * C.y (n + 1)) + C.M * q := by
          simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
        have h3 : q * C.y (n + 1) ≤ C.M * q := by
          calc q * C.y (n + 1) ≤ q * C.M := Nat.mul_le_mul_left q hyM
            _ = C.M * q := Nat.mul_comm _ _
        omega
      calc (3 * C.M + q) ^ n * (3 * C.M + q) * (C.y (n + 1) * C.prodFrom 1 n)
          = ((3 * C.M + q) * C.y (n + 1)) * ((3 * C.M + q) ^ n * C.prodFrom 1 n) := by
            simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ ≤ (C.M * (3 * C.y (n + 1) + q)) * (C.M ^ n * C.prodG n) := Nat.mul_le_mul step ih
        _ = C.M ^ n * C.M * ((3 * C.y (n + 1) + q) * C.prodG n) := by
            simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- **The upper half of the min–max sandwich**: `(3M+q)^L ≤ M^L · 2^B`.

    Together with `pow_le_of_min` (`m^L · 2^B ≤ (3m+q)^L`) this is the
    two-sided squeeze `(3 + q/M)^L ≤ 2^B ≤ (3 + q/m)^L`, written without
    division. -/
theorem pow_ge_of_max : (3 * C.M + q) ^ C.L ≤ C.M ^ C.L * 2 ^ C.BB C.L := by
  have h := C.prod_squeeze_max C.L
  rw [C.prodG_eq C.L, C.prodFrom_one_eq_zero] at h
  have hp := C.prodFrom_pos 0 C.L
  have h' : ((3 * C.M + q) ^ C.L) * C.prodFrom 0 C.L
          ≤ (C.M ^ C.L * 2 ^ C.BB C.L) * C.prodFrom 0 C.L := by
    calc ((3 * C.M + q) ^ C.L) * C.prodFrom 0 C.L
        ≤ C.M ^ C.L * (2 ^ C.BB C.L * C.prodFrom 0 C.L) := h
      _ = (C.M ^ C.L * 2 ^ C.BB C.L) * C.prodFrom 0 C.L := (Nat.mul_assoc _ _ _).symm
  exact Nat.le_of_mul_le_mul_right h' hp

/-- `u_n` = how many of the first `n` backward hops take exactly one halving. -/
def countOnes (C : Cycle q) : Nat → Nat
  | 0     => 0
  | n + 1 => (if C.bb (n + 1) = 1 then 1 else 0) + C.countOnes n

/-- Every hop contributes at least `2` to `b + [b = 1]`: either `b = 1` and the
    indicator supplies the second, or `b ≥ 2` already does. -/
theorem two_mul_le_BB_add_countOnes :
    ∀ n, 2 * n ≤ C.BB n + C.countOnes n := by
  intro n
  induction n with
  | zero => simp [Cycle.BB, countOnes]
  | succ n ih =>
      have hb := C.bb_pos n
      show 2 * (n + 1)
         ≤ (C.BB n + C.bb (n + 1)) + ((if C.bb (n + 1) = 1 then 1 else 0) + C.countOnes n)
      by_cases h : C.bb (n + 1) = 1
      · rw [if_pos h, h]; omega
      · rw [if_neg h]
        have h2 : 2 ≤ C.bb (n + 1) := by omega
        omega

/-- **At least `2L − B` of a cycle's steps take a single halving.**

    For `q = 1` the min–max sandwich pins `B/L` to `log₂3`, which turns this into
    "at least `2 − log₂3 ≈ 41.5 %` of the steps" — see `docs/STRUCTURE.md`.
    That last step needs real arithmetic and is **not** formalized; what is
    proved here is the exact integer inequality it rests on. -/
theorem single_halving_count : 2 * C.L ≤ C.BB C.L + C.countOnes C.L :=
  C.two_mul_le_BB_add_countOnes C.L

end Cycle

/-! ## 3. A Bernoulli-style inequality on naturals -/

/-- `(N+q)^L * N ≤ N^L * (N + 2Lq)` whenever `2Lq ≤ N`.

    This is the integer stand-in for `(1 + q/N)^L ≤ 1 + 2Lq/N`, which is where
    the usual argument would reach for `exp` and `log`. -/
theorem pow_succ_le (N q : Nat) :
    ∀ L, 2 * L * q ≤ N → (N + q) ^ L * N ≤ N ^ L * (N + 2 * L * q) := by
  intro L
  induction L with
  | zero => intro _; simp
  | succ L ih =>
      intro h
      have hL : 2 * L * q ≤ N := by
        -- omega parses `2 * L * q` as `(2*L) * q`, so relate the atoms directly
        have h2 : 2 * L * q ≤ 2 * (L + 1) * q := Nat.mul_le_mul_right q (by omega)
        omega
      have hq2 : q * (2 * L * q) ≤ q * N := Nat.mul_le_mul_left q hL
      have step : (N + q) * (N + 2 * L * q) ≤ N * (N + 2 * (L + 1) * q) := by
        have e1 : (N + q) * (N + 2 * L * q) = N * N + 2 * (L * (q * N)) + q * N + q * (2 * L * q) := by
          simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          omega
        have e2 : N * (N + 2 * (L + 1) * q) = N * N + 2 * (L * (q * N)) + 2 * (q * N) := by
          simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          omega
        omega
      calc (N + q) ^ (L + 1) * N
          = (N + q) * ((N + q) ^ L * N) := by
            rw [Nat.pow_succ]; simp [Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ (N + q) * (N ^ L * (N + 2 * L * q)) := Nat.mul_le_mul_left _ (ih hL)
        _ = N ^ L * ((N + q) * (N + 2 * L * q)) := by
            simp [Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ N ^ L * (N * (N + 2 * (L + 1) * q)) := Nat.mul_le_mul_left _ step
        _ = N ^ (L + 1) * (N + 2 * (L + 1) * q) := by
            rw [Nat.pow_succ]; simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

namespace Cycle
variable {q : Nat} (C : Cycle q)

/-- `3m * 2^B ≤ 3^L * (3m + 2Lq)` — the squeeze with the Bernoulli bound applied. -/
theorem squeeze {m : Nat} (hm : ∀ i, m ≤ C.y i) (hmpos : 0 < m)
    (hsmall : 2 * C.L * q ≤ 3 * m) :
    3 * m * 2 ^ C.BB C.L ≤ 3 ^ C.L * (3 * m + 2 * C.L * q) := by
  have key := C.pow_le_of_min hm
  have bern := pow_succ_le (3 * m) q C.L hsmall
  have hmL : 0 < m ^ C.L := Nat.pow_pos hmpos
  have h1 : (m ^ C.L * 2 ^ C.BB C.L) * (3 * m) ≤ (3 * m + q) ^ C.L * (3 * m) :=
    Nat.mul_le_mul_right _ key
  have h3 : (m ^ C.L * 2 ^ C.BB C.L) * (3 * m)
          ≤ (3 * m) ^ C.L * (3 * m + 2 * C.L * q) := Nat.le_trans h1 bern
  have hexp : (3 * m) ^ C.L = 3 ^ C.L * m ^ C.L := by rw [Nat.mul_pow]
  rw [hexp] at h3
  have h4 : m ^ C.L * (3 * m * 2 ^ C.BB C.L)
          ≤ m ^ C.L * (3 ^ C.L * (3 * m + 2 * C.L * q)) := by
    calc m ^ C.L * (3 * m * 2 ^ C.BB C.L)
        = (m ^ C.L * 2 ^ C.BB C.L) * (3 * m) := by
          simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ ≤ 3 ^ C.L * m ^ C.L * (3 * m + 2 * C.L * q) := h3
      _ = m ^ C.L * (3 ^ C.L * (3 * m + 2 * C.L * q)) := by
          simp [Nat.mul_comm, Nat.mul_left_comm]
  exact Nat.le_of_mul_le_mul_left h4 hmL

/-- **THE CYCLE-LENGTH BOUND.**

    `hbaker` is the Baker-type input, stated in ℕ: `2^B / 3^L ≥ 1 + c / L^κ`.
    Everything below it is proved.  Conclusion: `3 m c ≤ 2 q L^(κ+1)`.

    Used contrapositively: if every `n < m` is known to reach the fixed point,
    then any cycle satisfies `L^(κ+1) ≥ 3 m c / (2q)`. -/
theorem length_bound {m κ c : Nat}
    (hm : ∀ i, m ≤ C.y i) (hmpos : 0 < m)
    (hsmall : 2 * C.L * q ≤ 3 * m)
    (hbaker : 3 ^ C.L * C.L ^ κ + c * 3 ^ C.L ≤ 2 ^ C.BB C.L * C.L ^ κ) :
    3 * m * c ≤ 2 * q * C.L ^ (κ + 1) := by
  have sq := C.squeeze hm hmpos hsmall
  have h1 : 3 * m * (3 ^ C.L * C.L ^ κ + c * 3 ^ C.L)
          ≤ 3 * m * (2 ^ C.BB C.L * C.L ^ κ) := Nat.mul_le_mul_left _ hbaker
  have h2 : 3 * m * (2 ^ C.BB C.L * C.L ^ κ)
          ≤ 3 ^ C.L * (3 * m + 2 * C.L * q) * C.L ^ κ := by
    calc 3 * m * (2 ^ C.BB C.L * C.L ^ κ)
        = (3 * m * 2 ^ C.BB C.L) * C.L ^ κ := by
          simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ ≤ (3 ^ C.L * (3 * m + 2 * C.L * q)) * C.L ^ κ := Nat.mul_le_mul_right _ sq
  have h3 : 3 * m * (3 ^ C.L * C.L ^ κ) + 3 ^ C.L * (3 * m * c)
          ≤ 3 * m * (3 ^ C.L * C.L ^ κ) + 3 ^ C.L * (2 * q * C.L ^ (κ + 1)) := by
    calc 3 * m * (3 ^ C.L * C.L ^ κ) + 3 ^ C.L * (3 * m * c)
        = 3 * m * (3 ^ C.L * C.L ^ κ + c * 3 ^ C.L) := by
          simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ ≤ 3 ^ C.L * (3 * m + 2 * C.L * q) * C.L ^ κ := Nat.le_trans h1 h2
      _ = 3 * m * (3 ^ C.L * C.L ^ κ) + 3 ^ C.L * (2 * q * (C.L ^ κ * C.L)) := by
          simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ = 3 * m * (3 ^ C.L * C.L ^ κ) + 3 ^ C.L * (2 * q * C.L ^ (κ + 1)) := by
          rw [Nat.pow_succ]
  have h4 : 3 ^ C.L * (3 * m * c) ≤ 3 ^ C.L * (2 * q * C.L ^ (κ + 1)) := by omega
  exact Nat.le_of_mul_le_mul_left h4 (Nat.pow_pos (by omega))

/-- Specialisation to `q = 1`, the Collatz case: `3 m c ≤ 2 L^(κ+1)`. -/
theorem length_bound_q1 (C : Cycle 1) {m κ c : Nat}
    (hm : ∀ i, m ≤ C.y i) (hmpos : 0 < m)
    (hsmall : 2 * C.L ≤ 3 * m)
    (hbaker : 3 ^ C.L * C.L ^ κ + c * 3 ^ C.L ≤ 2 ^ C.BB C.L * C.L ^ κ) :
    3 * m * c ≤ 2 * C.L ^ (κ + 1) := by
  have h := C.length_bound hm hmpos (by omega) hbaker
  omega

end Cycle

/-! ## 4. Non-vacuity — the bound applied to a REAL cycle

`length_bound`'s hypotheses are not vacuous.  `cycle5 : Cycle 5` is the genuine
cycle `{49, 31, 19}` from `Collatz/Examples.lean`, with `L = 3`, `B = 5`,
minimum `19`.  Its Baker-type input holds with `κ = 3, c = 5`:

    3^3 * 3^3 + 5 * 3^3  =  729 + 135  =  864  =  32 * 27  =  2^B * L^κ

(equality, so `c = 5` is exactly sharp here) and the conclusion
`3 * 19 * 5 ≤ 2 * 5 * 3^4`, i.e. `285 ≤ 810`, is a true statement about an
actual cycle rather than about a hypothetical one. -/

theorem cycle5_BB : cycle5.BB 3 = 5 := by
  have h1 : cycle5.y 1 = 31 := rfl
  have h2 : cycle5.y 2 = 19 := rfl
  have h3 : cycle5.y 3 = 49 := rfl
  simp [Cycle.BB, Cycle.bb, h1, h2, h3, v2]

theorem cycle5_min (i : Nat) : 19 ≤ cycle5.y i := by
  show 19 ≤ (if i % 3 = 0 then 49 else if i % 3 = 1 then 31 else 19)
  rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with h | h | h <;> simp [h]

/-- The length bound, instantiated on a cycle that actually exists. -/
theorem cycle5_length_bound : 3 * 19 * 5 ≤ 2 * 5 * cycle5.L ^ (3 + 1) := by
  refine cycle5.length_bound (m := 19) (κ := 3) (c := 5) cycle5_min (by decide) ?_ ?_
  · show 2 * 3 * 5 ≤ 3 * 19
    decide
  · show 3 ^ 3 * 3 ^ 3 + 5 * 3 ^ 3 ≤ 2 ^ cycle5.BB 3 * 3 ^ 3
    rw [cycle5_BB]
    decide

end Collatz
