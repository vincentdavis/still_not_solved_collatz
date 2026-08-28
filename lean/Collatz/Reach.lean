/-
  Collatz/Reach.lean

  `L ≤ |R(O)|` — a cycle is no longer than the set its maximum can reach.

  WHY THIS FILE EXISTS.  docs/STRUCTURE.md's first result says a cycle with
  maximum `O` lies entirely inside `R(O)`, everything reachable *backwards* from
  `O` without ever exceeding it, so `L ≤ |R(O)|`.  The recorded Lean blocker was
  "needs finite-set machinery, expensive in a Mathlib-free development".

  It does not need any.  `R(O)` is a set of naturals bounded by `O`, so it can be
  counted by a plain recursion over the initial segment `[0, O]` — `countLT`
  below — and the bound then follows from the pigeonhole principle the project
  already has, choice-free, in `Collatz/Pigeonhole.lean`.  No `Finset`, no
  cardinals, no `Classical.choice`.

  THE ARGUMENT.  Give each element `x` of a decidable set `p` its *rank*,
  `countLT p x` = how many members of `p` lie strictly below it.  Rank is
  strictly increasing along `p`, hence injective on `p`.  A cycle's `L` elements
  are pairwise distinct (`Cycle.y_ne_of_lt`), all `≤ M`, and all in `p`; so rank
  maps them injectively into `[0, countLE p M)`.  If that range were smaller than
  `L`, pigeonhole would collide two of them — contradicting distinctness.

  This is stated once, for an ARBITRARY decidable `p` that the cycle satisfies
  (`length_le_count`).  `R(O)` is then just one choice of `p`, and two cruder
  ones fall out for free.

  WHAT IS *NOT* MACHINE-CHECKED HERE.  The theorem is proved for the real map
  `S`, and it is applied to real cycles in `Collatz/Examples.lean`.  But the
  numeric value of `countLE (inR q M M) M` is NOT reduced by the kernel: `S` goes
  through `oddPart`, which is well-founded recursion and therefore sealed, and
  `native_decide` is banned by `lean/check.sh`.  `#eval` gives 10 for
  `q = 5, O = 49`, 19 for `q = 11, O = 79`, 1 for `q = 1, O = 10^6+3` and 408 for
  `q = 1, O = 3077` — matching `collatz_maxodd.structure.reachable_set` exactly —
  and `test_structure.py` checks that agreement over many inputs.  So "the count
  is 10" rests on evaluation and cross-checking, while "L is at most the count"
  is the part that is proved.

  Mathlib-free: Lean 4 core only.
-/
import Collatz.Cycle
import Collatz.Pigeonhole

namespace Collatz

/-! ## 1. Counting a decidable predicate on an initial segment -/

/-- `countLT p n` = how many `i < n` satisfy `p`. -/
def countLT (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | (n + 1) => countLT p n + (if p n then 1 else 0)

/-- `countLE p n` = how many `i ≤ n` satisfy `p`. -/
def countLE (p : Nat → Bool) (n : Nat) : Nat := countLT p (n + 1)

theorem countLT_succ (p : Nat → Bool) (n : Nat) :
    countLT p (n + 1) = countLT p n + (if p n then 1 else 0) := rfl

theorem countLT_mono (p : Nat → Bool) {a b : Nat} (h : a ≤ b) :
    countLT p a ≤ countLT p b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ b ih =>
      rcases (show a ≤ b ∨ a = b + 1 by omega) with hle | heq
      · have h1 := ih hle
        have h2 : countLT p b ≤ countLT p (b + 1) := by
          rw [countLT_succ]; omega
        omega
      · subst heq; exact Nat.le_refl _

/-- Rank strictly increases across a member of `p`. -/
theorem countLT_lt (p : Nat → Bool) {x y : Nat} (hx : p x = true) (hxy : x < y) :
    countLT p x < countLT p y := by
  have h1 : countLT p (x + 1) = countLT p x + 1 := by
    rw [countLT_succ, hx]; simp
  have h2 : countLT p (x + 1) ≤ countLT p y := countLT_mono p (by omega)
  omega

/-- **Rank is injective on `p`.**  This is what replaces a cardinality argument. -/
theorem countLT_inj (p : Nat → Bool) {a b : Nat}
    (ha : p a = true) (hb : p b = true) (h : countLT p a = countLT p b) : a = b := by
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · have := countLT_lt p ha hlt; omega
  · exact heq
  · have := countLT_lt p hb hgt; omega

/-- Every member of `p` below the bound has rank below the count. -/
theorem countLT_lt_countLE (p : Nat → Bool) {x n : Nat}
    (hx : p x = true) (hxn : x ≤ n) : countLT p x < countLE p n :=
  countLT_lt p hx (by omega)

/-- `[0, n]` contains exactly `n` positive numbers.  Used only to get `L ≤ M`. -/
theorem countLE_pos_eq (n : Nat) : countLE (fun x => decide (0 < x)) n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show countLT _ (n + 1 + 1) = n + 1
      rw [countLT_succ]
      have : countLT (fun x => decide (0 < x)) (n + 1) = n := ih
      simp [this]

namespace Cycle

variable {q : Nat} (C : Cycle q)

/-! ## 2. The counting bound

Everything the cycle satisfies bounds its length. -/

/-- **The counting bound.**  If every one of the cycle's `L` listed elements
    satisfies a decidable predicate `p`, then `L` is at most the number of
    `x ≤ M` satisfying `p`.

    Proof: rank is injective on `p` (`countLT_inj`) and lands in
    `[0, countLE p M)`; if that were too small, `Pigeonhole.exists_repeat` would
    collide two cycle elements, which `y_ne_of_lt` forbids. -/
theorem length_le_count (p : Nat → Bool) (hp : ∀ i, i < C.L → p (C.y i) = true) :
    C.L ≤ countLE p C.M := by
  rcases Nat.lt_or_ge (countLE p C.M) C.L with hlt | hge
  · exfalso
    have hg : ∀ i, i ≤ countLE p C.M → countLT p (C.y i) < countLE p C.M := by
      intro i hi
      exact countLT_lt_countLE p (hp i (by omega)) (C.hmax i)
    obtain ⟨i, j, hij, hjn, heq⟩ :=
      exists_repeat (countLE p C.M) (fun i => countLT p (C.y i)) hg
    have hyi := hp i (by omega)
    have hyj := hp j (by omega)
    exact C.y_ne_of_lt hij (by omega) (countLT_inj p hyi hyj heq)
  · exact hge

/-- A cycle is no longer than its maximum. -/
theorem length_le_M : C.L ≤ C.M := by
  have h := C.length_le_count (fun x => decide (0 < x))
    (fun i _ => by simp [C.y_pos i])
  rw [countLE_pos_eq] at h
  exact h

/-! ## 3. `R(O)`

`reachIn q O d x` asks whether `x` reaches `O` within `d` forward `S_q`-steps
without ever exceeding `O`.  That is exactly membership of `R(O)` as
docs/STRUCTURE.md defines it — "reachable backwards from `O`, staying `≤ O`" —
read in the forward direction, which is the direction that is a function and so
the direction a `Bool` can decide. -/

/-- Does `x` reach `O` within `d` forward steps, never exceeding `O`? -/
def reachIn (q O : Nat) : Nat → Nat → Bool
  | 0, x => decide (x = O)
  | (d + 1), x => decide (x = O) || (decide (x ≤ O) && reachIn q O d (S q x))

/-- `x ∈ R(O)`, at search depth `d`.  `R(O)` is a set of *odd* numbers — the
    Syracuse map runs on odds — so the parity test is part of the membership,
    not an afterthought.  Without it the count picks up even numbers that happen
    to feed into `O` and overshoots (12 rather than 10 for `q = 5, O = 49`). -/
def inR (q O d x : Nat) : Bool := decide (x % 2 = 1) && reachIn q O d x

/-- Every cycle element reaches the maximum, in as many steps as its index. -/
theorem reach_y : ∀ (d i : Nat), i ≤ d → reachIn q C.M d (C.y i) = true := by
  intro d
  induction d with
  | zero =>
      intro i hi
      have h0 : i = 0 := by omega
      subst h0
      show decide (C.y 0 = C.M) = true
      exact decide_eq_true rfl
  | succ d ih =>
      intro i hi
      cases i with
      | zero =>
          have e0 : decide (C.y 0 = C.M) = true := decide_eq_true rfl
          show (decide (C.y 0 = C.M) || _) = true
          rw [e0]
          rfl
      | succ k =>
          have hk : k ≤ d := by omega
          have hstep : S q (C.y (k + 1)) = C.y k := C.hstep k
          have e1 : decide (C.y (k + 1) ≤ C.M) = true := decide_eq_true (C.hmax (k + 1))
          show (decide (C.y (k + 1) = C.M) || (decide (C.y (k + 1) ≤ C.M) &&
                 reachIn q C.M d (S q (C.y (k + 1))))) = true
          rw [hstep, e1, ih k hk]
          simp

/-- Cycle elements are in `R(M)`: odd, and reaching `M`. -/
theorem inR_y (d i : Nat) (hi : i ≤ d) : inR q C.M d (C.y i) = true := by
  simp only [inR, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨C.hodd i, C.reach_y d i hi⟩

/-- **`L ≤ |R(O)|`** — docs/STRUCTURE.md's first structural result.
    Any search depth at least `L` will do, and a deeper search only counts more,
    so this is the *strongest* form: it bounds `L` by the depth-`d` truncation of
    `R(M)`, which is a subset of `R(M)` itself. -/
theorem length_le_reach (d : Nat) (hd : C.L ≤ d) :
    C.L ≤ countLE (inR q C.M d) C.M :=
  C.length_le_count _ (fun i hi => C.inR_y d i (by omega))

/-- **`L ≤ |R(O)|`, with no free parameter.**  Depth `M` always suffices,
    because `L ≤ M`. -/
theorem length_le_reach_M : C.L ≤ countLE (inR q C.M C.M) C.M :=
  C.length_le_reach C.M C.length_le_M

/-! ## 4. Two cruder corollaries, for free

The same theorem with weaker predicates.  These are the bounds you get from the
residue constraints alone, without computing any reachable set. -/

/-- Every element is odd, so `L` is at most the number of odd `x ≤ M`. -/
theorem length_le_odd_count : C.L ≤ countLE (fun x => decide (x % 2 = 1)) C.M :=
  C.length_le_count _ (fun i _ => by simp [C.hodd i])

/-- **T0 sharpens it:** no element is divisible by 3 either. -/
theorem length_le_odd_not_three_count :
    C.L ≤ countLE (fun x => decide (x % 2 = 1 ∧ x % 3 ≠ 0)) C.M :=
  C.length_le_count _ (fun i _ => by simp [C.hodd i, C.T0 i])

end Cycle

end Collatz
