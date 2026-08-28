/-
  Collatz/Periodic.lean

  The periodic points of the backward map, and the `−1` witness.

  WHY THIS FILE EXISTS.  Every other route in this project ends by measuring some
  density that stubbornly fails to reach zero.  docs/WHY_NOT.md gives the reason
  with no densities at all, and it is the last unformalized line of the project's
  own accounting table.

  THE POINT.  Fix a halving pattern `b` and ask for a point the backward map
  returns to itself.  Any such point satisfies the *cycle equation*

      y · (2 ^ B − 3 ^ L)  =  c_L ,

  and — this is what matters — **no cycle appears anywhere in the hypotheses**.
  `Cycle.T7_eq` looked like a fact about cycles; it is a fact about patterns.
  What makes a pattern a cycle is that its solution is a *positive integer*.

  WHAT IS PROVED, AND WHAT IS NOT.  `cycle_equation` is a uniqueness statement:
  *if* `y` is a periodic point then it satisfies the equation.  The matching
  EXISTENCE statement — that every pattern has a periodic point, namely the
  rational `c_L / (2 ^ B − 3 ^ L)` — is **not** formalized here, and over `ℤ` it
  is simply false: `b = (3)`, `q = 1` gives `1 / 5`.  Most patterns have no
  integer periodic point at all (12 of the 340 patterns of length `≤ 4` with
  entries `≤ 4`, at `q = 1`).  The general existence claim
  lives in `ℚ` (or `ℤ₃`), which this development does not build;
  `collatz_maxodd.padic.periodic_point` computes it as a `Fraction`, and
  `test_padic.py` checks the two agree wherever both apply.

  THE WITNESS.  For the all-ones pattern an integer point does exist, and it is
  `−1`, at every length (`minus_one_of_ones`).  Its residue mod `3 ^ k` is
  `3 ^ k − 1` (`neg_one_emod`), every base-3 digit of which is a 2
  (`all_digits_two`) — the residue an odd halving count demands at every depth.
  A congruence sieve therefore cannot rule the class out, and `−1` is not a
  natural number.  Sign and integrality are invisible to congruences.

  (That last sentence is the *interpretation*.  The sieve itself — `a_k`, class
  survival, the count of live residues — is not formalized in this file; see
  docs/WHY_NOT.md for what is measured rather than proved.)

  This is the first file in the development to leave ℕ.  It has to: the witness
  is negative.  Core `Int` only — still no Mathlib, still no `ℝ`.

  Mathlib-free: Lean 4 core only.
-/
import Collatz.Cycle

namespace Collatz

/-! ## 1. Patterns

A *pattern* is just a sequence of halving counts.  `PB` and `Pc` are `Cycle.BB`
and `Cycle.cc` with the cycle removed — they depend on the pattern alone, which
is the entire point of this file. -/

/-- `B_k = b 1 + … + b k`. -/
def PB (b : Nat → Nat) : Nat → Nat
  | 0 => 0
  | (k + 1) => PB b k + b (k + 1)

/-- `c_k = 2 ^ b_k · c_{k−1} + 3 ^ (k−1) · q`, `c_0 = 0`. -/
def Pc (q : Int) (b : Nat → Nat) : Nat → Int
  | 0 => 0
  | (k + 1) => 2 ^ b (k + 1) * Pc q b k + 3 ^ k * q

/-! ### Small `Int` power facts (core Lean has no `ring`, no `positivity`) -/

theorem two_pow_pos (k : Nat) : (0 : Int) < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih => rw [Int.pow_succ]; omega

theorem three_pow_pos (k : Nat) : (0 : Int) < 3 ^ k := by
  induction k with
  | zero => decide
  | succ k ih => rw [Int.pow_succ]; omega

theorem two_pow_le_three_pow (k : Nat) : (2 : Int) ^ k ≤ 3 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
      have h := two_pow_pos k
      rw [Int.pow_succ, Int.pow_succ]; omega

/-- NOTE.  This is deliberately stated in the `a + d` form and *then* specialised
    below.  Running `induction d` with a hypothesis `a ≤ a + d` in scope makes
    Lean generalise that hypothesis, which drags `Classical.choice` into the
    axiom certificate — `lean/check.sh` rejects it, and it took a bisection to
    find.  Keeping the induction hypothesis-free avoids the whole problem. -/
theorem two_pow_int_le_add (a d : Nat) : (2 : Int) ^ a ≤ 2 ^ (a + d) := by
  induction d with
  | zero =>
      have e : a + 0 = a := by omega
      rw [e]
      exact Int.le_refl _
  | succ d ih =>
      have hp := two_pow_pos (a + d)
      have e : (2 : Int) ^ (a + (d + 1)) = 2 ^ (a + d) * 2 := by
        have ha : a + (d + 1) = (a + d) + 1 := by omega
        rw [ha, Int.pow_succ]
      omega

theorem two_pow_int_le {a b : Nat} (h : a ≤ b) : (2 : Int) ^ a ≤ 2 ^ b := by
  obtain ⟨d, hd⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  subst hd
  exact two_pow_int_le_add a d

/-- Over `ℤ` a product is 1 only if both factors are; positivity rules out the
    `(−1, −1)` branch.  Core Lean has no `nlinarith`, so this is by hand. -/
theorem eq_one_of_pos_mul_eq_one {a b : Int} (ha : 0 < a) (h : a * b = 1) :
    a = 1 ∧ b = 1 := by
  have hb : 0 < b := by
    rcases Int.lt_trichotomy b 0 with hlt | heq | hgt
    · exact absurd h (by have := Int.mul_neg_of_pos_of_neg ha hlt; omega)
    · exact absurd h (by rw [heq]; simp)
    · exact hgt
  rcases (show a = 1 ∨ 2 ≤ a by omega) with h1 | h2
  · exact ⟨h1, by rw [h1] at h; omega⟩
  · exfalso
    have : 2 * b ≤ a * b := Int.mul_le_mul_of_nonneg_right h2 (by omega)
    omega

theorem two_pow_lt_three_pow {k : Nat} (hk : 0 < k) : (2 : Int) ^ k < 3 ^ k := by
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  subst hj
  have h := two_pow_le_three_pow j
  have h2 := two_pow_pos j
  rw [Int.pow_succ, Int.pow_succ]; omega

/-! ## 2. Periodic points of the backward map

`z (k+1)` is the backward image of `z k` under halving count `b (k+1)`, written
without division: `3 · z (k+1) + q = 2 ^ b (k+1) · z k`.  A periodic point is a
chain that closes. -/

/-- A point the pattern `b` returns to itself after `L` backward hops.

    DESIGN NOTE.  `hstep` quantifies over *all* `k`, not just `k < L`, so this
    demands an infinite **integral** backward chain — strictly stronger than
    "the length-`L` window closes".  That is the safe direction (every theorem
    below is correspondingly weaker, every witness correspondingly stronger),
    but it is worth knowing: with `q = 1` and `b = (1, 2, 1, 1, …)` the backward
    map genuinely fixes `−7` over `ℚ`, yet `IsPeriodic 1 b 2 (-7)` is
    uninhabited, because the chain leaves `ℤ` at the fourth step.  It also makes
    `periodic_unique`'s hypothesis redundant — see the note there. -/
structure IsPeriodic (q : Int) (b : Nat → Nat) (L : Nat) (y : Int) where
  z : Nat → Int
  hz0 : z 0 = y
  hzL : z L = y
  hstep : ∀ k, 3 * z (k + 1) + q = 2 ^ b (k + 1) * z k

namespace IsPeriodic

variable {q : Int} {b : Nat → Nat} {L : Nat} {y : Int} (P : IsPeriodic q b L y)

/-- The closed form, exactly as `Cycle.closed_form` but over `ℤ` and with no
    cycle in sight: `3 ^ k · z k + c_k = 2 ^ B_k · y`. -/
theorem closed : ∀ k, 3 ^ k * P.z k + Pc q b k = 2 ^ PB b k * y := by
  intro k
  induction k with
  | zero => simp [Pc, PB, P.hz0]
  | succ k ih =>
      have hstep := P.hstep k
      show 3 ^ (k + 1) * P.z (k + 1) + (2 ^ b (k + 1) * Pc q b k + 3 ^ k * q)
           = 2 ^ (PB b k + b (k + 1)) * y
      have e1 : 3 ^ (k + 1) * P.z (k + 1) + (2 ^ b (k + 1) * Pc q b k + 3 ^ k * q)
              = 3 ^ k * (3 * P.z (k + 1) + q) + 2 ^ b (k + 1) * Pc q b k := by
        rw [Int.pow_succ]
        simp [Int.mul_add, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc,
              Int.add_comm, Int.add_left_comm, Int.add_assoc]
      rw [e1, hstep]
      have e2 : 3 ^ k * (2 ^ b (k + 1) * P.z k) + 2 ^ b (k + 1) * Pc q b k
              = 2 ^ b (k + 1) * (3 ^ k * P.z k + Pc q b k) := by
        simp [Int.mul_add, Int.mul_comm, Int.mul_left_comm]
      rw [e2, ih, Int.pow_add]
      simp [Int.mul_comm, Int.mul_assoc]

/-- **The cycle equation, for an arbitrary pattern.**  `y (2^B − 3^L) = c_L`.

    This is the file's headline.  `Cycle.T7_eq` is the same identity, but only
    for a cycle that exists; here it holds for *every* pattern, because every
    pattern has a periodic point.  Cycles are not what makes the equation true —
    they are the solutions that happen to be positive integers. -/
theorem cycle_equation (P : IsPeriodic q b L y) :
    y * (2 ^ PB b L - 3 ^ L) = Pc q b L := by
  have h := P.closed L
  rw [P.hzL] at h
  have : 3 ^ L * y + Pc q b L = 2 ^ PB b L * y := h
  have e : y * (2 ^ PB b L - 3 ^ L) = 2 ^ PB b L * y - 3 ^ L * y := by
    simp [Int.mul_sub, Int.mul_comm]
  omega

end IsPeriodic

/-- **Uniqueness.**  Off the diagonal `2 ^ B = 3 ^ L` a pattern has at most one
    periodic point, so "the periodic point of `b`" is well defined.

    NOTE.  Given `IsPeriodic` as defined (see its design note) `hne` is actually
    redundant: subtracting two chains gives `3 ^ k ∣ (y − y')` for every `k`.
    It is kept because it is what a finite-window definition would need, and
    because it is the hypothesis the statement is *about*. -/
theorem periodic_unique {q : Int} {b : Nat → Nat} {L : Nat} {y y' : Int}
    (P : IsPeriodic q b L y) (P' : IsPeriodic q b L y')
    (hne : (2 : Int) ^ PB b L - 3 ^ L ≠ 0) : y = y' := by
  have h := P.cycle_equation
  have h' := P'.cycle_equation
  have : y * (2 ^ PB b L - 3 ^ L) = y' * (2 ^ PB b L - 3 ^ L) := by rw [h, h']
  exact Int.eq_of_mul_eq_mul_right (by omega) this

/-! ## 3. The all-ones pattern, and the witness -/

/-- Every hop a single halving. -/
def ones : Nat → Nat := fun _ => 1

theorem PB_ones (L : Nat) : PB ones L = L := by
  induction L with
  | zero => rfl
  | succ L ih => show PB ones L + 1 = L + 1; rw [ih]

/-- `c_L = 3 ^ L − 2 ^ L` for the all-ones pattern, written without
    subtraction. -/
theorem Pc_ones (L : Nat) : Pc 1 ones L + 2 ^ L = 3 ^ L := by
  induction L with
  | zero => decide
  | succ L ih =>
      show (2 ^ (1 : Nat) * Pc 1 ones L + 3 ^ L * 1) + 2 ^ (L + 1) = 3 ^ (L + 1)
      have e2 : (2 : Int) ^ (L + 1) = 2 * 2 ^ L := by rw [Int.pow_succ]; omega
      have e3 : (3 : Int) ^ (L + 1) = 3 * 3 ^ L := by rw [Int.pow_succ]; omega
      have e1 : (2 : Int) ^ (1 : Nat) = 2 := by decide
      rw [e1, e2, e3]
      omega

/-- **The witness.**  The all-ones pattern's periodic point is `−1`, at every
    length: `3 · (−1) + 1 = −2 = 2 · (−1)`, so `−1` is fixed by every hop. -/
def onesPeriodic (L : Nat) : IsPeriodic 1 ones L (-1) where
  z := fun _ => -1
  hz0 := rfl
  hzL := rfl
  hstep := fun _ => by show 3 * (-1 : Int) + 1 = 2 ^ (1 : Nat) * (-1); decide

/-- And it is the *only* one, for every `L ≥ 1`: `2 ^ L ≠ 3 ^ L`. -/
theorem minus_one_of_ones {L : Nat} (hL : 0 < L) {y : Int}
    (P : IsPeriodic 1 ones L y) : y = -1 := by
  refine periodic_unique P (onesPeriodic L) ?_
  rw [PB_ones]
  have h := two_pow_lt_three_pow hL
  omega

/-- **`−1` is not a natural number.**  So the all-ones pattern, which passes every
    congruence test at every depth, is not a cycle — and no congruence can say so. -/
theorem ones_not_a_cycle : ¬ ∃ n : Nat, 0 < n ∧ (n : Int) = -1 := by
  rintro ⟨n, hn, he⟩
  omega

/-! ### The constant patterns, in full

Length 1, halving count `b`: `PB = b` and `c_1 = q`, so the periodic point solves
`y (2 ^ b − 3) = q`.  For `q = 1` that is `y = 1/(2^b − 3)`, and asking which `b`
give a positive integer is a two-line argument — no deep theorem, no sieve. -/

/-- The constant pattern of halving count `b`. -/
def const (b : Nat) : Nat → Nat := fun _ => b

theorem PB_const (b : Nat) : PB (const b) 1 = b := by
  show 0 + b = b; omega

theorem Pc_const (q : Int) (b : Nat) : Pc q (const b) 1 = q := by
  show 2 ^ b * 0 + 3 ^ (0 : Nat) * q = q
  simp

/-- A length-1 periodic point solves `y (2 ^ b − 3) = q`. -/
theorem const_equation {q : Int} {b : Nat} {y : Int} (P : IsPeriodic q (const b) 1 y) :
    y * (2 ^ b - 3) = q := by
  have h := P.cycle_equation
  rw [PB_const, Pc_const] at h
  have e : (3 : Int) ^ (1 : Nat) = 3 := by decide
  rw [e] at h
  exact h

/-- `b = 2` really does have the periodic point `1`: the existence half, so
    that `const_positive_integer` below is a genuine characterisation and not
    just a uniqueness statement about a possibly-empty set. -/
def constTwoPeriodic : IsPeriodic 1 (const 2) 1 1 where
  z := fun _ => 1
  hz0 := rfl
  hzL := rfl
  hstep := fun _ => by show 3 * (1 : Int) + 1 = 2 ^ (2 : Nat) * 1; decide

/-- **For `q = 1` the only constant pattern landing on a positive integer is
    `b = 2`, and it gives `y = 1` — the trivial cycle.**

    So `1 → 4 → 2 → 1` is not merely *an* example of the cycle equation; among
    the constant patterns it is the unique positive-integer solution. -/
theorem const_positive_integer {b : Nat} {y : Int}
    (h : y * (2 ^ b - 3) = 1) (hy : 0 < y) : b = 2 ∧ y = 1 := by
  obtain ⟨hy1, hd⟩ := eq_one_of_pos_mul_eq_one hy h
  refine ⟨?_, hy1⟩
  -- 2 ^ b − 3 = 1, so 2 ^ b = 4, so b = 2
  have hb4 : (2 : Int) ^ b = 4 := by omega
  rcases (show b ≤ 2 ∨ 3 ≤ b by omega) with hle | hge
  · rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with h0 | h1 | h2
    · exfalso; rw [h0] at hb4; simp at hb4
    · exfalso; rw [h1] at hb4; simp at hb4
    · exact h2
  · exfalso
    have h8 : (8 : Int) ≤ 2 ^ b := by
      have := two_pow_int_le (a := 3) (b := b) hge
      have e : (2 : Int) ^ (3 : Nat) = 8 := by decide
      omega
    omega

/-! ## 4. Why the sieve cannot see it

In `ℤ₃` the number `−1` is `…2222`.  Concretely: its residue mod `3 ^ k` is
`3 ^ k − 1`, and *every* base-3 digit of that is a 2 — which is exactly the
residue an odd halving count requires at each step, and the all-ones pattern
uses an odd halving count at every step.  So the class survives at every depth. -/

/-- `−1 mod 3 ^ k` really is `3 ^ k − 1`.  Without this the digit lemmas below
    would be facts about a natural number that merely *looks* like `−1`. -/
theorem neg_one_emod {m : Int} (h : 0 < m) : (-1 : Int) % m = m - 1 := by
  have e : (-1 : Int) = (m - 1) + m * (-1) := by omega
  rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]

/-- The residue of `−1` at depth `k`, as an integer. -/
theorem neg_one_residue (k : Nat) : (-1 : Int) % (3 ^ k) = 3 ^ k - 1 :=
  neg_one_emod (three_pow_pos k)

/-- `3 ^ m − 1 ≡ 2 (mod 3)` for `m ≥ 1`: the last base-3 digit is a 2. -/
theorem digit_pow_sub_one {m : Nat} (hm : 0 < m) : (3 ^ m - 1) % 3 = 2 := by
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  subst hk
  have h : 3 ^ (k + 1) = 3 * 3 ^ k := by rw [Nat.pow_succ]; omega
  have hp : 0 < 3 ^ k := Nat.pow_pos (by decide)
  omega

/-- Shifting off `j` digits of `3 ^ k − 1` leaves `3 ^ (k−j) − 1`. -/
theorem shift_pow_sub_one {k j : Nat} (h : j ≤ k) :
    (3 ^ k - 1) / 3 ^ j = 3 ^ (k - j) - 1 := by
  obtain ⟨d, hd⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
  subst hd
  have hsplit : 3 ^ (j + d) = 3 ^ j * 3 ^ d := Nat.pow_add 3 j d
  have hpj : 0 < 3 ^ j := Nat.pow_pos (by decide)
  have hpd : 0 < 3 ^ d := Nat.pow_pos (by decide)
  -- write 3^d = A + 1 so that every step below is linear in the atoms
  obtain ⟨A, hA⟩ : ∃ A, 3 ^ d = A + 1 := ⟨3 ^ d - 1, by omega⟩
  have hmul : 3 ^ (j + d) = 3 ^ j * A + 3 ^ j := by
    rw [hsplit, hA, Nat.mul_add, Nat.mul_one]
  have e : 3 ^ (j + d) - 1 = (3 ^ j - 1) + 3 ^ j * A := by omega
  rw [e, Nat.add_mul_div_left _ _ hpj, Nat.div_eq_of_lt (by omega)]
  have hjd : j + d - j = d := by omega
  rw [hjd, hA]
  omega

/-- **Every base-3 digit of `3 ^ k − 1` is a 2.**  Depth `k`, digit `j < k`. -/
theorem all_digits_two {k j : Nat} (hj : j < k) : ((3 ^ k - 1) / 3 ^ j) % 3 = 2 := by
  rw [shift_pow_sub_one (by omega)]
  exact digit_pow_sub_one (by omega)

/-- **…and `3 ^ k − 1` is exactly the residue of `−1`.**  Put together with
    `neg_one_residue`, that is the statement the prose wants: at every depth the
    class of `−1` is `…2222`, so an odd halving count is legal at every step and
    the pattern of all ones never contradicts a congruence. -/
theorem neg_one_all_digits_two {k j : Nat} (hj : j < k) :
    ((-1 : Int) % (3 ^ k)) = ((3 ^ k - 1 : Nat) : Int) ∧ ((3 ^ k - 1) / 3 ^ j) % 3 = 2 := by
  refine ⟨?_, all_digits_two hj⟩
  rw [neg_one_residue k]
  have hp : 1 ≤ (3 : Nat) ^ k := Nat.one_le_pow _ _ (by decide)
  have hcast : (((3 : Nat) ^ k : Nat) : Int) = (3 : Int) ^ k := by
    push_cast
    rfl
  omega

/-! ## 5. Cycles are periodic points

The converse direction of the headline: a genuine cycle *is* a periodic point,
and a positive-integer one.  So `Cycle.T7_eq` is the special case of
`cycle_equation` where the solution lands in ℕ. -/

namespace Cycle

variable {q : Nat} (C : Collatz.Cycle q)

/-- A cycle, read as a periodic point of its own halving pattern. -/
def toPeriodic : IsPeriodic (q : Int) C.bb C.L (C.M : Int) where
  z := fun k => (C.y k : Int)
  hz0 := rfl
  hzL := by
    have hp := C.hper 0
    show ((C.y C.L : Int)) = (C.M : Int)
    have : C.y C.L = C.y 0 := by simpa using hp
    rw [this]; rfl
  hstep := fun k => by
    have h := C.bb_spec k
    show 3 * (C.y (k + 1) : Int) + (q : Int) = 2 ^ C.bb (k + 1) * (C.y k : Int)
    exact_mod_cast h

/-- **So a cycle is exactly a periodic point that lands on a positive integer.**
    The equation is the same one every pattern satisfies; what distinguishes a
    cycle is `0 < M` and `M : ℕ`, neither of which a congruence can test. -/
theorem cycle_is_positive_periodic :
    (C.M : Int) * (2 ^ PB C.bb C.L - 3 ^ C.L) = Pc (q : Int) C.bb C.L ∧ 0 < (C.M : Int) :=
  ⟨C.toPeriodic.cycle_equation, by have := C.M_pos; omega⟩

/-! ### The pattern machinery agrees with the cycle machinery

`PB` and `Pc` were `Cycle.BB` and `Cycle.cc` with the cycle removed; on a cycle
they give back exactly what they came from.  So `Cycle.T7_eq` is the special case
of `cycle_equation` where the periodic point happens to be a positive integer —
which is the sentence this whole file exists to make precise. -/

theorem PB_eq_BB (k : Nat) : PB C.bb k = C.BB k := by
  induction k with
  | zero => rfl
  | succ k ih => show PB C.bb k + C.bb (k + 1) = C.BB k + C.bb (k + 1); rw [ih]

theorem Pc_eq_cc (k : Nat) : Pc (q : Int) C.bb k = (C.cc k : Int) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show 2 ^ C.bb (k + 1) * Pc (q : Int) C.bb k + 3 ^ k * (q : Int)
           = ((2 ^ C.bb (k + 1) * C.cc k + 3 ^ k * q : Nat) : Int)
      rw [ih]
      push_cast
      rfl

/-- **`Cycle.T7_eq`, recovered from the general equation.**  Same identity, now
    with the cycle a special case rather than the hypothesis. -/
theorem T7_from_periodic :
    (C.M : Int) * (2 ^ C.BB C.L - 3 ^ C.L) = (C.cc C.L : Int) := by
  have h := C.toPeriodic.cycle_equation
  rw [C.PB_eq_BB, C.Pc_eq_cc] at h
  exact h

end Cycle

end Collatz
