/-
  Collatz/Equivalence.lean

  THE BACKWARD SIEVE IS NOT AN APPROXIMATION TO THE CYCLE PROBLEM — IT IS THE
  CYCLE PROBLEM.

  A *backward chain* bounded by `M` is an infinite sequence `M = y 0, y 1, …`
  of odd numbers, each the `S_q`-predecessor of the one before, with every
  element `≤ M`.  "M survives the backward sieve at depth k" means such a chain
  exists out to length `k`.

  Two directions:

    * `Cycle.toBackChain` — a cycle is a backward chain bounded by its own
      maximum (walk around it forever).  Trivial.

    * `BackChain.exists_periodic` — conversely ANY backward chain bounded by `M`
      forces a periodic point of `S_q` at or below `M`.  Pigeonhole on the
      finitely many values `≤ M`.

    * `BackChain.exists_nontrivial_periodic` — for `q = 1` and `M > 1` that
      periodic point is moreover `≠ 1`, i.e. a genuinely nontrivial cycle,
      because `S₁ 1 = 1` means a `1` anywhere in the chain drags `M` down to `1`.

  So a bounded infinite backward chain exists **iff** a cycle does.  Proving the
  sieve kills every `M` at some finite depth is not an approach to the
  conjecture — it is logically the same problem.

  NON-VACUITY.  For `q = 1` the hypothesis `BackChain 1 M` with `M > 1` is
  exactly what the conjecture denies, so that corollary is conditional and
  would be vacuous if Collatz is true.  The general-`q` theorem is NOT: § 4
  instantiates it on the real `q = 7` cycle `11 → 5 → 11`, where the hypothesis
  is satisfied and the conclusion is a true statement about an actual cycle.

  Mathlib-free.  See `Collatz/Unproved.lean` for the one step (König's lemma)
  that is deliberately NOT formalized here.
-/
import Collatz.Odd
import Collatz.Cycle
import Collatz.Pigeonhole
import Collatz.Examples

namespace Collatz

/-! ## 1. Iteration

Lean 4 core has no `Nat.iterate` and this project takes no dependencies, so
iteration is defined here.  `Siter q (n+1) x = Siter q n (S q x)` holds by
`rfl`, which is what makes the chain lemma a two-line induction. -/

/-- `Siter q n x` applies `S q` to `x` exactly `n` times. -/
def Siter (q : Nat) : Nat → Nat → Nat
  | 0,     x => x
  | n + 1, x => Siter q n (S q x)

/-! ## 2. Backward chains -/

/-- An infinite backward chain of odd numbers, bounded by `M`. -/
structure BackChain (q M : Nat) where
  /-- `y k` is the `k`-th odd number going backwards from `M`. -/
  y : Nat → Nat
  /-- the chain starts at `M` -/
  hy0 : y 0 = M
  /-- every element is odd -/
  hodd : ∀ k, y k % 2 = 1
  /-- `y (k+1)` is an odd `S_q`-predecessor of `y k` -/
  hstep : ∀ k, S q (y (k + 1)) = y k
  /-- the chain never rises above its start -/
  hle : ∀ k, y k ≤ M

namespace BackChain

variable {q M : Nat}

/-- Walking `m` steps forward along the chain undoes `m` backward steps. -/
theorem iter (C : BackChain q M) : ∀ m k, Siter q m (C.y (k + m)) = C.y k := by
  intro m
  induction m with
  | zero => intro k; simp [Siter]
  | succ m ih =>
      intro k
      show Siter q m (S q (C.y (k + (m + 1)))) = C.y k
      have e : k + (m + 1) = (k + m) + 1 := by omega
      rw [e, C.hstep]
      exact ih k

/-- **The substantive direction, in full generality.**  A backward chain bounded
    by `M` forces a periodic point of `S_q` at or below `M`.

    The chain takes infinitely many indices into the finitely many values `≤ M`,
    so two indices `i < j` agree; then `S_q` iterated `j - i` times fixes
    `y j`. -/
theorem exists_periodic (C : BackChain q M) :
    ∃ z n, 0 < n ∧ Siter q n z = z ∧ z ≤ M := by
  obtain ⟨i, j, hij, _hjM, hy⟩ :=
    exists_repeat (M + 1) C.y (fun i _ => by have := C.hle i; omega)
  refine ⟨C.y j, j - i, by omega, ?_, C.hle j⟩
  have e : i + (j - i) = j := by omega
  calc Siter q (j - i) (C.y j)
      = Siter q (j - i) (C.y (i + (j - i))) := by rw [e]
    _ = C.y i := C.iter (j - i) i
    _ = C.y j := hy

end BackChain

/-! ## 3. The `q = 1` refinement: the periodic point is not the trivial cycle -/

/-- `S₁` fixes `1`: this is the trivial cycle `1 → 4 → 2 → 1`. -/
theorem S_one_eq_one : S 1 1 = 1 := by
  simp [S, oddPart]

namespace BackChain

/-- If `1` ever appears in a `q = 1` chain then the chain started at `1`.
    (`S₁ 1 = 1`, so a `1` propagates all the way back to `y 0`.) -/
theorem eq_one_of_mem {M : Nat} (C : BackChain 1 M) : ∀ k, C.y k = 1 → M = 1 := by
  intro k
  induction k with
  | zero => intro h; rw [← C.hy0]; exact h
  | succ k ih =>
      intro h
      refine ih ?_
      have hs := C.hstep k
      rw [h, S_one_eq_one] at hs
      exact hs.symm

/-- Hence for `M > 1` no element of the chain is `1`. -/
theorem ne_one {M : Nat} (C : BackChain 1 M) (hM : 1 < M) : ∀ k, C.y k ≠ 1 := by
  intro k hk
  have := C.eq_one_of_mem k hk
  omega

/-- **A bounded backward chain above 1 forces a NONTRIVIAL cycle.**

    CONDITIONAL: the hypothesis is exactly what the Collatz conjecture denies,
    so this statement is vacuous if the conjecture is true.  Its content is the
    implication, not the existence of an instance.  See `q7_has_periodic_point`
    for the same argument where the hypothesis really is satisfied. -/
theorem exists_nontrivial_periodic {M : Nat} (C : BackChain 1 M) (hM : 1 < M) :
    ∃ z n, 0 < n ∧ Siter 1 n z = z ∧ z ≠ 1 ∧ z ≤ M := by
  obtain ⟨i, j, hij, _hjM, hy⟩ :=
    exists_repeat (M + 1) C.y (fun i _ => by have := C.hle i; omega)
  refine ⟨C.y j, j - i, by omega, ?_, C.ne_one hM j, C.hle j⟩
  have e : i + (j - i) = j := by omega
  calc Siter 1 (j - i) (C.y j)
      = Siter 1 (j - i) (C.y (i + (j - i))) := by rw [e]
    _ = C.y i := C.iter (j - i) i
    _ = C.y j := hy

end BackChain

/-- **The easy direction.**  A cycle is a backward chain bounded by its own
    maximum. -/
def Cycle.toBackChain {q : Nat} (C : Cycle q) : BackChain q (C.y 0) where
  y     := C.y
  hy0   := rfl
  hodd  := C.hodd
  hstep := C.hstep
  hle   := C.hmax

/-! ## 4. Non-vacuity

`cycle7 : Cycle 7` is the real cycle `11 → 5 → 11` from `Collatz/Examples.lean`.
Feeding it through both directions gives a TRUE, non-vacuous instance: the
hypothesis is satisfied by an actual cycle, and the conclusion asserts an actual
periodic point. -/

/-- The `q = 7` cycle really does give a backward chain bounded by its maximum. -/
example : BackChain 7 (cycle7.y 0) := cycle7.toBackChain

/-- …and the pigeonhole argument really does produce a periodic point from it. -/
theorem q7_has_periodic_point :
    ∃ z n, 0 < n ∧ Siter 7 n z = z ∧ z ≤ cycle7.y 0 :=
  cycle7.toBackChain.exists_periodic

/-- Round trip for `q = 1`: a cycle with maximum `> 1` yields a nontrivial
    periodic point at or below that maximum. -/
theorem Cycle.periodic_of_max_gt_one (C : Cycle 1) (hM : 1 < C.y 0) :
    ∃ z n, 0 < n ∧ Siter 1 n z = z ∧ z ≠ 1 ∧ z ≤ C.y 0 :=
  C.toBackChain.exists_nontrivial_periodic hM

end Collatz
