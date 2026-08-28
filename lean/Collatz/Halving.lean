/-
  Collatz/Halving.lean

  "At least 41.5 % of the steps are single halvings", with no real numbers and
  nothing assumed.

  WHY THIS FILE EXISTS.  It was the last theorem in the project's accounting
  table marked "needs real arithmetic on `log₂ 3`, and core Lean has no `ℝ`".
  That reason was wrong, and the mistake is instructive: the *derivation*
  mentions `log₂ 3`, the *statement* does not.  "At least 41.5 %" is

      1000 · u  ≥  415 · L ,

  an inequality between whole numbers.  What it needs is not `ℝ` but a rational
  strictly between `log₂ 3` and the cutoff `1.585`, and one integer inequality
  certifying that it is one.

  THE CERTIFICATE.  Take `317/200`:

      log₂ 3  <  317/200  ≤  1.585        ⟺        3 ^ 200  <  2 ^ 317 ,

  a fact about two 96-digit integers that `decide` settles outright.  `cert`
  below depends on **no axioms at all**.  That single line is where the real
  number `log₂ 3` used to be.

  `317/200` is not merely convenient, it is forced: it is the *unique* fraction
  with denominator at most 200 lying in `(log₂ 3, 1.585]`.  The bound must be
  above `log₂ 3`, or `Cycle.T7` contradicts it, and at most `1.585`, or it does
  not reach 41.5 %.  The nearest convergent of `log₂ 3`, `65/41 = 1.58537…`,
  overshoots the cutoff and yields only 41.46 %.

  NOTHING IS QUARANTINED.  The only input is `12825 ≤ m`: the cycle's smallest
  element exceeds 12825.  That is not an analytic hypothesis of the Baker kind —
  it is discharged here by `decide` at `m = 12825` plus monotonicity
  (`cert_m`, `cert_m_mono`), and for `q = 1` it is supplied outright by the
  verified search, which puts any nontrivial cycle's minimum above
  `2.39 × 10²¹`.

  (An earlier version of this file routed through `Cycle.squeeze`, whose
  Bernoulli linearization forced a hypothesis coupling `L` to `m`.  Going through
  the exact `Cycle.pow_le_of_min` instead removes `L` from the hypothesis
  entirely — which is what the informal derivation in docs/STRUCTURE.md always
  did.  Recorded because the weaker route looked perfectly convincing.)

  A NOTE ON `2 ^ 317`.  It is written `2 ^ 256 * 2 ^ 61` throughout.  Lean will
  prove `3 ^ 200 < 2 ^ 317` by `decide` quite happily, but warns that it did not
  evaluate an exponent above 256; `lean/check.sh` fails on any warning, and the
  `set_option` that would raise the threshold is banned as an escape hatch.  So
  the split is a house-rule accommodation, not a limitation of Lean.

  Mathlib-free: Lean 4 core only.
-/
import Collatz.Length

namespace Collatz

/-! ## 1. The certificate: `317/200 > log₂ 3`, without logarithms -/

/-- `2 ^ 317`, split so that no literal exponent exceeds 256 (see the header). -/
def twoPow317 : Nat := 2 ^ 256 * 2 ^ 61

/-- **`3 ^ 200 < 2 ^ 317`** — i.e. `log₂ 3 < 317/200 = 1.585`.
    Decided outright: this declaration depends on no axioms whatsoever. -/
theorem cert : (3 : Nat) ^ 200 < twoPow317 := by decide

theorem twoPow317_pos : 0 < twoPow317 := by decide

/-- `(2 ^ 317) ^ L = 2 ^ (317 L)`, with the exponents kept symbolic. -/
theorem twoPow317_pow (L : Nat) : twoPow317 ^ L = 2 ^ (317 * L) := by
  show ((2 : Nat) ^ 256 * 2 ^ 61) ^ L = 2 ^ (317 * L)
  have e : 317 * L = 256 * L + 61 * L := by omega
  rw [e, Nat.pow_add, Nat.pow_mul, Nat.pow_mul, Nat.mul_pow]

/-! ### The size hypothesis, discharged rather than assumed

`(3m + 1) ^ 200 ≤ 2 ^ 317 · m ^ 200` is `(3 + 1/m) ^ 200 ≤ 2 ^ 317` cleared of
division.  It holds for every `m ≥ 12825`, and — crucially — it says nothing
about `L`. -/

/-- The bound is monotone in `m`, because `3 + 1/m` decreases. -/
theorem cert_m_mono {m₀ m K : Nat} (h0 : 0 < m₀) (hle : m₀ ≤ m)
    (h : (3 * m₀ + 1) ^ 200 ≤ K * m₀ ^ 200) :
    (3 * m + 1) ^ 200 ≤ K * m ^ 200 := by
  have step : (3 * m + 1) * m₀ ≤ (3 * m₀ + 1) * m := by
    have e1 : (3 * m + 1) * m₀ = 3 * (m * m₀) + m₀ := by
      simp [Nat.add_mul, Nat.mul_assoc]
    have e2 : (3 * m₀ + 1) * m = 3 * (m₀ * m) + m := by
      simp [Nat.add_mul, Nat.mul_assoc]
    have e3 : m * m₀ = m₀ * m := Nat.mul_comm m m₀
    omega
  have p := Nat.pow_le_pow_left step 200
  rw [Nat.mul_pow, Nat.mul_pow] at p
  have h2 : (3 * m₀ + 1) ^ 200 * m ^ 200 ≤ K * m₀ ^ 200 * m ^ 200 :=
    Nat.mul_le_mul_right _ h
  have hp : 0 < m₀ ^ 200 := Nat.pow_pos h0
  have goal : m₀ ^ 200 * ((3 * m + 1) ^ 200) ≤ m₀ ^ 200 * (K * m ^ 200) := by
    have a : m₀ ^ 200 * ((3 * m + 1) ^ 200) = (3 * m + 1) ^ 200 * m₀ ^ 200 :=
      Nat.mul_comm _ _
    have b : m₀ ^ 200 * (K * m ^ 200) = K * m₀ ^ 200 * m ^ 200 := by
      simp [Nat.mul_left_comm, Nat.mul_assoc]
    omega
  exact Nat.le_of_mul_le_mul_left goal hp

/-- The base case, by `decide` on two 918-digit integers.  No axioms. -/
theorem cert_m_base : (3 * 12825 + 1) ^ 200 ≤ twoPow317 * 12825 ^ 200 := by decide

/-- **`(3m + 1) ^ 200 ≤ 2 ^ 317 · m ^ 200` for every `m ≥ 12825`.**
    No `L` anywhere: this is a statement about the minimum alone. -/
theorem cert_m {m : Nat} (hm : 12825 ≤ m) :
    (3 * m + 1) ^ 200 ≤ twoPow317 * m ^ 200 :=
  cert_m_mono (by decide) hm cert_m_base

namespace Cycle

variable (C : Collatz.Cycle 1)

/-! ## 2. `B / L ≤ 1.585`

`Cycle.T7` already gives `B / L > log₂ 3` from below.  This is the bound from
above, and it is the half that needs the minimum.

The route matters: `Cycle.pow_le_of_min` is the *exact* squeeze
`m ^ L · 2 ^ B ≤ (3m + q) ^ L`, with no linearization, so raising it to the
200th power leaves a hypothesis about `m` alone. -/

/-- **`200 · B ≤ 317 · L`.**  The exact min-squeeze, raised to the 200th power
    and compared against the certificate.  The only hypothesis is on the
    minimum; `L` is unconstrained. -/
theorem BB_le_of_min {m : Nat} (hm : ∀ i, m ≤ C.y i) (hm0 : 12825 ≤ m) :
    200 * C.BB C.L ≤ 317 * C.L := by
  rcases Nat.lt_or_ge (317 * C.L) (200 * C.BB C.L) with h | h
  · exfalso
    have hmpos : 0 < m := by omega
    -- the exact squeeze at the minimum, for q = 1
    have sq : m ^ C.L * 2 ^ C.BB C.L ≤ (3 * m + 1) ^ C.L := C.pow_le_of_min hm
    -- raise it to the 200th power
    have p := Nat.pow_le_pow_left sq 200
    have lhs : (m ^ C.L * 2 ^ C.BB C.L) ^ 200
             = m ^ (C.L * 200) * 2 ^ (C.BB C.L * 200) := by
      rw [Nat.mul_pow, Nat.pow_mul, Nat.pow_mul]
    have rhs : ((3 * m + 1) ^ C.L) ^ 200 = ((3 * m + 1) ^ 200) ^ C.L := by
      rw [← Nat.pow_mul, ← Nat.pow_mul]
      have e : C.L * 200 = 200 * C.L := Nat.mul_comm _ _
      rw [e]
    rw [lhs, rhs] at p
    -- 2 ^ (200 B) is at least 2 · 2 ^ (317 L)
    have hexp : 317 * C.L + 1 ≤ C.BB C.L * 200 := by omega
    have hbig : 2 ^ (317 * C.L) * 2 ≤ 2 ^ (C.BB C.L * 200) := by
      have := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) hexp
      rw [Nat.pow_succ] at this
      exact this
    -- and (3m+1) ^ (200 L) is at most 2 ^ (317 L) · m ^ (200 L)
    have hc : ((3 * m + 1) ^ 200) ^ C.L ≤ (twoPow317 * m ^ 200) ^ C.L :=
      Nat.pow_le_pow_left (cert_m hm0) C.L
    have hexpand : (twoPow317 * m ^ 200) ^ C.L = 2 ^ (317 * C.L) * m ^ (C.L * 200) := by
      rw [Nat.mul_pow, twoPow317_pow, ← Nat.pow_mul, Nat.mul_comm 200 C.L]
    rw [hexpand] at hc
    -- chain everything
    have step1 : m ^ (C.L * 200) * (2 ^ (317 * C.L) * 2)
               ≤ m ^ (C.L * 200) * 2 ^ (C.BB C.L * 200) :=
      Nat.mul_le_mul_left _ hbig
    have chain : m ^ (C.L * 200) * (2 ^ (317 * C.L) * 2)
               ≤ 2 ^ (317 * C.L) * m ^ (C.L * 200) := by omega
    -- cancel the common positive factor
    have hpos : 0 < 2 ^ (317 * C.L) * m ^ (C.L * 200) :=
      Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos hmpos)
    have e : m ^ (C.L * 200) * (2 ^ (317 * C.L) * 2)
           = (2 ^ (317 * C.L) * m ^ (C.L * 200)) * 2 := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    omega
  · exact h

/-! ## 3. The figure itself -/

/-- **At least 41.5 % of a cycle's steps are single halvings.**

    `1000 · u ≥ 415 · L`, where `u = countOnes` counts the steps taking exactly
    one halving.  Equivalently, at least that share of the cycle's odd elements
    are `≡ 3 (mod 4)`.

    No real numbers appear anywhere, and nothing is assumed beyond the size of
    the minimum: `Cycle.single_halving_count` gives `u ≥ 2L − B`, `BB_le_of_min`
    gives `B ≤ 1.585 L`, and `415 = 2000 − 1585`. -/
theorem single_halving_percent {m : Nat} (hm : ∀ i, m ≤ C.y i) (hm0 : 12825 ≤ m) :
    415 * C.L ≤ 1000 * C.countOnes C.L := by
  have hB := C.BB_le_of_min hm hm0
  have hu := C.single_halving_count
  omega

/-- The same, with the minimum supplied by the development itself
    (`Collatz/Minimum.lean`) rather than passed in. -/
theorem single_halving_percent_m (hm0 : 12825 ≤ C.m) :
    415 * C.L ≤ 1000 * C.countOnes C.L :=
  C.single_halving_percent C.m_le hm0

/-- The arithmetic step on its own, so the constant is visible rather than
    buried: `2000 − 1585 = 415`. -/
theorem percent_arithmetic (B L u : Nat)
    (hB : 200 * B ≤ 317 * L) (hu : 2 * L ≤ B + u) : 415 * L ≤ 1000 * u := by
  omega

/-- **The size hypothesis is load-bearing.**  `trivialCycle` has `L = 1`,
    `B = 2`, `u = 0` and minimum `1`, so the conclusion is false for it — as it
    must be, since `2/1 = 2 > 1.585`.  Dropping `12825 ≤ m` would make the
    theorem false, not merely unprovable. -/
theorem needs_the_size_hypothesis :
    ¬ (415 * trivialCycle.L ≤ 1000 * trivialCycle.countOnes trivialCycle.L) := by
  have hb : trivialCycle.bb 1 = 2 := by simp [Collatz.Cycle.bb, trivialCycle, v2]
  have hc : trivialCycle.countOnes trivialCycle.L = 0 := by
    show (if trivialCycle.bb 1 = 1 then 1 else 0) + trivialCycle.countOnes 0 = 0
    rw [hb]
    rfl
  rw [hc]
  show ¬ (415 * 1 ≤ 1000 * 0)
  decide

end Cycle

end Collatz
