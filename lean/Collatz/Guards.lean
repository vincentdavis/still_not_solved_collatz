/-
  Collatz/Guards.lean

  VALUE PINS — "do the definitions compute the intended functions?"

  A formalization can be flawless and still be about the wrong functions.  This
  file pins `v2`, `oddPart`, `S`, `iter`, `bb`, `BB`, `cc` and the `Cycle`
  instances to concrete numbers, along TWO INDEPENDENT EVALUATION PATHS:

  * `#guard …`  runs the **compiled / interpreted** definition.  A `#guard`
    whose proposition evaluates to `false` is a build ERROR.  (Verified
    negative control: `#guard S 1 7 = 12` fails with
    "Expression `decide (S 1 7 = 12)` did not evaluate to `true`".)

  * `example … := by simp [S, oddPart]`  builds a **kernel-checked proof term**
    from the equation lemmas.  `decide` and `rfl` cannot be used for these:
    `v2` and `oddPart` are defined by well-founded recursion and are therefore
    sealed, so the kernel reaches them only through those lemmas.  (Verified
    negative control: `example : S 1 7 = 12 := by simp [S, oddPart]` leaves
    the goal `⊢ False` and fails.)

  The two paths share no machinery, so agreement between them rules out a
  divergence between the compiled function and the logical one.  (There is no
  `@[implemented_by]`, `unsafe`, `native_decide` or `axiom` anywhere in this
  project — see `lean/check.sh`.)

  All expected values below were produced by an INDEPENDENT Python
  implementation of `S_q`, not by Lean.

  Mathlib-free: Lean 4 core only.
-/
import Collatz.Bridge
import Collatz.Examples

namespace Collatz

/-! ## 1. `v2` and `oddPart` — interpreter path -/

-- `v2 m` for `m = 1 … 24`.
#guard (List.range 24).map (fun i => v2 (i + 1))
     = [0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3]

-- `oddPart m` for `m = 1 … 24`.
#guard (List.range 24).map (fun i => oddPart (i + 1))
     = [1, 1, 3, 1, 5, 3, 7, 1, 9, 5, 11, 3, 13, 7, 15, 1, 17, 9, 19, 5, 21, 11, 23, 3]

-- The defining property `2 ^ v2 m * oddPart m = m` on `m = 1 … 500`.
-- (The *theorem* is `two_pow_v2_mul_oddPart`; this pins that it is not vacuous.)
#guard (List.range 500).all (fun i => 2 ^ v2 (i + 1) * oddPart (i + 1) == i + 1)

-- Edge convention at 0 (documented in `Collatz/Odd.lean`).
#guard v2 0 = 0
#guard oddPart 0 = 0

/-! ## 2. `S q` — interpreter path, three values of `q`, first 24 odd inputs -/

#guard (List.range 24).map (fun i => S 1 (2 * i + 1))
     = [1, 5, 1, 11, 7, 17, 5, 23, 13, 29, 1, 35, 19, 41, 11, 47, 25, 53, 7, 59, 31, 65, 17, 71]

#guard (List.range 24).map (fun i => S 5 (2 * i + 1))
     = [1, 7, 5, 13, 1, 19, 11, 25, 7, 31, 17, 37, 5, 43, 23, 49, 13, 55, 29, 61, 1, 67, 35, 73]

#guard (List.range 24).map (fun i => S 7 (2 * i + 1))
     = [5, 1, 11, 7, 17, 5, 23, 13, 29, 1, 35, 19, 41, 11, 47, 25, 53, 7, 59, 31, 65, 17, 71, 37]

-- `S q n` is odd, and `3n + q = 2 ^ v2(3n+q) * S q n`, on 300 odd inputs.
#guard (List.range 300).all (fun i =>
  let n := 2 * i + 1
  S 1 n % 2 == 1 && 3 * n + 1 == 2 ^ v2 (3 * n + 1) * S 1 n)

/-! ## 3. `S q` — kernel path (equation lemmas), the same numbers

If these disagreed with the `#guard`s above, the compiled function and the
logical function would differ.  They do not. -/

example : S 1 1  = 1  := by simp [S, oddPart]
example : S 1 3  = 5  := by simp [S, oddPart]
example : S 1 5  = 1  := by simp [S, oddPart]
example : S 1 7  = 11 := by simp [S, oddPart]   -- the user's seed example
example : S 1 9  = 7  := by simp [S, oddPart]
example : S 1 11 = 17 := by simp [S, oddPart]
example : S 1 13 = 5  := by simp [S, oddPart]
example : S 1 27 = 41 := by simp [S, oddPart]
example : S 5 49 = 19 := by simp [S, oddPart]
example : S 5 19 = 31 := by simp [S, oddPart]
example : S 5 31 = 49 := by simp [S, oddPart]
example : S 7 11 = 5  := by simp [S, oddPart]
example : S 7 5  = 11 := by simp [S, oddPart]
example : v2 40  = 3  := by simp [v2]
example : v2 152 = 3  := by simp [v2]
example : oddPart 152 = 19 := by simp [oddPart]

/-! ## 4. `iter` (forward orbits) -/

#guard (List.range 13).map (fun k => iter 1 k 27)
     = [27, 41, 31, 47, 71, 107, 161, 121, 91, 137, 103, 155, 233]
#guard (List.range 7).map (fun k => iter 5 k 49) = [49, 19, 31, 49, 19, 31, 49]
#guard (List.range 5).map (fun k => iter 7 k 11) = [11, 5, 11, 5, 11]
#guard (List.range 4).map (fun k => iter 1 k 1)  = [1, 1, 1, 1]

/-! ## 5. NON-VACUITY of the `Cycle` predicate, via the soundness bridge

Each instance below is produced by `Cycle.ofOrbit`, whose hypotheses mention
only the forward map `S_q`.  They are therefore not hand-asserted structures:
they are *derived* from "`iter q L n = n`, `n` is the orbit maximum, `L` is the
least period" — the textbook definition of a cycle with maximum `n`. -/

/-- The `q = 1` fixed point **{1}**.  This is the answer to "can the cycle
    predicate be satisfied at all?": yes, and by the one cycle everybody knows.
    So no theorem about `Cycle 1` is vacuous for lack of *any* instance. -/
def one : Cycle 1 :=
  Cycle.ofOrbit 1 1 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [iter, S, oddPart])
    (fun k hk => by
      have hk0 : k = 0 := by omega
      subst hk0; simp [iter])
    (fun _ h1 h2 => by omega)

example : one.M = 1 := rfl
example : one.L = 1 := rfl
#guard one.M = 1
#guard one.L = 1

/-- The `q = 7` cycle **{11, 5}**, `L = 2`, `M = 11 > q`. -/
def two7 : Cycle 7 :=
  Cycle.ofOrbit 7 11 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [iter, S, oddPart])
    (fun k hk => by
      rcases (show k = 0 ∨ k = 1 by omega) with h | h <;>
        subst h <;> simp [iter, S, oddPart])
    (fun k h1 h2 => by
      have hk1 : k = 1 := by omega
      subst hk1; simp [iter, S, oddPart])

example : two7.M = 11 := rfl
example : two7.L = 2  := rfl

/-- The `q = 5` cycle **{49, 31, 19}**, `L = 3`, `M = 49 > q`.  This inhabits
    the `L ≥ 3`, `M > q` regime that T2 / T3_gen / T4_base_gen / T5_gen are
    about, so those theorems have a witness and are **not** vacuously true. -/
def three5 : Cycle 5 :=
  Cycle.ofOrbit 5 49 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [iter, S, oddPart])
    (fun k hk => by
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with h | h | h <;>
        subst h <;> simp [iter, S, oddPart])
    (fun k h1 h2 => by
      rcases (show k = 1 ∨ k = 2 by omega) with h | h <;>
        subst h <;> simp [iter, S, oddPart])

example : three5.M = 49 := rfl
example : three5.L = 3  := rfl
example : three5.y 1 = 31 := by simp [Cycle.ofOrbit, three5, iter, S, oddPart]
example : three5.y 2 = 19 := by simp [Cycle.ofOrbit, three5, iter, S, oddPart]

/-! ### The theorems, applied to the bridge-built cycle -/

example : (3 * three5.M + 5) % 4 = 0            := three5.T1
example : three5.M % 4 = 5 % 4                  := three5.T1_mod4
example : three5.M % 12 = (5 * 5) % 12          := three5.T3_gen (by decide)
example : three5.M % 36 ≠ (5 * 5) % 36          := three5.T4_base_gen (by decide)
example : (2 * three5.M) % 9 ≠ 5 % 9            := three5.T4_mod9 (by decide)
example : three5.bb 1 = 1                       := three5.T2_bb (by decide)
example : three5.bb 2 ≤ 2                       := three5.T5_bb_gen (by decide)
example : three5.y 2 % 3 ≠ 0                    := three5.T0 2
example : 3 ^ three5.L < 2 ^ three5.BB three5.L := three5.T7
example : 2 ^ three5.BB 2 * three5.M ≤ 3 ^ 2 * three5.M + three5.cc 2 := three5.T6 2

-- Faithfulness (`y_ne_of_lt`): the three listed elements really are distinct,
-- so the structure cannot be a shorter orbit padded out to length 3.
example : three5.y 0 ≠ three5.y 1 := three5.y_ne_of_lt (by decide) (by decide)
example : three5.y 0 ≠ three5.y 2 := three5.y_ne_of_lt (by decide) (by decide)
example : three5.y 1 ≠ three5.y 2 := three5.y_ne_of_lt (by decide) (by decide)

/-! ## 6. `bb`, `BB`, `cc` pinned on `cycle5`

`b₁ = b₂ = 1`, `b₃ = 3` ⇒ `B₃ = 5`, `c₃ = 245`, and the closed form
`3³·y₃ + c₃ = 2^{B₃}·M` reads `27·49 + 245 = 1568 = 32·49`. -/

#guard cycle5.bb 1 = 1
#guard cycle5.bb 2 = 1
#guard cycle5.bb 3 = 3
#guard cycle5.BB 3 = 5
#guard cycle5.cc 1 = 5
#guard cycle5.cc 2 = 25
#guard cycle5.cc 3 = 245
#guard 3 ^ 3 * cycle5.y 3 + cycle5.cc 3 = 2 ^ cycle5.BB 3 * cycle5.M
#guard 3 ^ 3 * 49 + 245 = 1568
#guard 2 ^ 5 * 49 = 1568

-- `2^{B₃} = 32 > 27 = 3³`: the ❌ row of `docs/GROUND_TRUTH.md`, on a real
-- cycle, in the interpreter as well as in the kernel (`Examples.lean`).
#guard ¬ (2 ^ cycle5.BB 3 ≤ 3 ^ 3)

/-! ## 7. The seed observations, pinned

`7 ↦ 11` is a genuine *increase*, so 7 is not a cycle maximum — and 11 IS
reachable from below (`S 1 7 = 11`, `7 < 11`), so the user's stated reason for
excluding 11 ("to reach 11 you need a bigger odd") is wrong even though the
conclusion is right: 11 is excluded by T1, because `11 ≡ 3 (mod 4)`. -/

#guard S 1 7 = 11
#guard 7 < S 1 7
#guard S 1 11 = 17
#guard 11 < S 1 11
#guard 7 % 4 = 3 && 11 % 4 = 3      -- both excluded by T1, for the same reason
#guard S 1 7 = 11 && 7 < 11         -- 11 IS reached from a SMALLER odd number

-- T5 ("only two even hops back") and the sharpness of its threshold:
-- `cycle7` has `b₂ = 3`, which is allowed precisely because `7M = 11q` there,
-- so the strict bound `11q < 7M` is not met.
#guard cycle7.bb 2 = 3
#guard 7 * 11 = 11 * 7
#guard ¬ (11 * 7 < 7 * 11)

end Collatz
