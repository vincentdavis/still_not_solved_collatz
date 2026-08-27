/-
  Collatz/Bridge.lean

  SOUNDNESS BRIDGE.

  `Collatz/Cycle.lean` *postulates* the backward orbit of a cycle as a function
  `y : Nat → Nat` together with eleven field hypotheses.  The obvious audit
  question is: are those fields actually satisfied by every genuine `S_q`-cycle,
  or is `Cycle q` an artefact that happens to be provable things about?

  This file answers it inside Lean.  `Cycle.ofOrbit` builds a `Cycle q` from
  data that mentions **only** the forward map `S_q`:

      n odd,  iter q L n = n,  n maximal on the orbit,  L minimal.

  Those are exactly the defining conditions of "n is the largest element of an
  `S_q`-cycle of length L", with no reference to `Cycle` at all.  So

      genuine S_q-cycle  ⟹  Cycle q  ⟹  (T0 … T8 apply)

  is now machine-checked end to end, and every theorem in `Collatz/Cycle.lean`
  is a theorem about real cycles.

  The trick that keeps this short: going *backwards* one step is the same as
  going *forwards* `L - 1` steps, so the backward orbit can be defined as
  `y k = iter q ((L-1) * k) n` with no modular arithmetic anywhere.

  Mathlib-free: Lean 4 core only.
-/
import Collatz.Cycle

namespace Collatz

/-! ## 1. Forward iteration of `S_q` -/

/-- `iter q k n` = the `k`-th forward `S_q`-iterate of `n`. -/
def iter (q : Nat) : Nat → Nat → Nat
  | 0,     n => n
  | (k+1), n => iter q k (S q n)

theorem iter_zero (q n : Nat) : iter q 0 n = n := rfl

theorem iter_succ (q k n : Nat) : iter q (k + 1) n = iter q k (S q n) := rfl

/-- `iter` composes: `iter q (a+b) = iter q b ∘ iter q a`. -/
theorem iter_add (q : Nat) : ∀ a b n, iter q (a + b) n = iter q b (iter q a n) := by
  intro a
  induction a with
  | zero => intro b n; rw [Nat.zero_add, iter_zero]
  | succ a ih =>
      intro b n
      have e : a + 1 + b = (a + b) + 1 := by omega
      rw [e, iter_succ, iter_succ, ih]

/-- One more forward step, from the front. -/
theorem iter_forward (q k n : Nat) : iter q (k + 1) n = S q (iter q k n) := by
  rw [iter_add]; rfl

/-- Oddness is preserved along the forward orbit. -/
theorem iter_odd {q : Nat} (hq : q % 2 = 1) (k : Nat) :
    ∀ n, n % 2 = 1 → (iter q k n) % 2 = 1 := by
  induction k with
  | zero => intro n hn; rw [iter_zero]; exact hn
  | succ k ih => intro n hn; rw [iter_succ]; exact ih (S q n) (S_odd hq hn)

/-! ## 2. Consequences of `iter q L n = n` -/

variable {q L n : Nat}

/-- Periodicity, one period. -/
theorem iter_period (h : iter q L n = n) (a : Nat) :
    iter q (a + L) n = iter q a n := by
  rw [Nat.add_comm a L, iter_add, h]

/-- Periodicity, `m` periods. -/
theorem iter_period_mul (h : iter q L n = n) (a : Nat) :
    ∀ m, iter q (a + L * m) n = iter q a n := by
  intro m
  induction m with
  | zero => rw [Nat.mul_zero, Nat.add_zero]
  | succ m ih =>
      have e : a + L * (m + 1) = (a + L * m) + L := by rw [Nat.mul_succ]; omega
      rw [e, iter_period h, ih]

/-- A bound checked on one period holds on the whole forward orbit. -/
theorem iter_le_of_lt (hL : 0 < L) (h : iter q L n = n)
    (hb : ∀ k, k < L → iter q k n ≤ n) : ∀ k, iter q k n ≤ n := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    rcases Nat.lt_or_ge k L with hk | hk
    · exact hb k hk
    · have e : (k - L) + L = k := by omega
      have hp := iter_period h (k - L)
      rw [e] at hp
      rw [hp]
      exact ih (k - L) (by omega)

/-! ## 3. The bridge -/

namespace Cycle

/-- **Every genuine `S_q`-cycle yields a `Cycle q`.**

Hypotheses, all stated purely in terms of the forward map `S_q`:

* `hn`   — `n` is odd;
* `hcyc` — `n` returns to itself after `L` forward steps;
* `hle`  — `n` is the **largest** element of its orbit;
* `hne`  — `L` is the **least** such period, so the orbit has `L` distinct
           elements.

The resulting cycle has `M = n` and length `L` (see `ofOrbit_M`, `ofOrbit_L`). -/
def ofOrbit (q n L : Nat)
    (hL : 0 < L) (hqp : 0 < q) (hqo : q % 2 = 1) (hq3 : q % 3 ≠ 0)
    (hn : n % 2 = 1)
    (hcyc : iter q L n = n)
    (hle : ∀ k, k < L → iter q k n ≤ n)
    (hne : ∀ k, 0 < k → k < L → iter q k n ≠ n) : Cycle q where
  L := L
  y := fun k => iter q ((L - 1) * k) n
  hL := hL
  hq_pos := hqp
  hq_odd := hqo
  hq_three := hq3
  hodd := fun i => iter_odd hqo _ n hn
  hstep := fun i => by
    have e : (L - 1) * (i + 1) + 1 = (L - 1) * i + L := by
      rw [Nat.mul_succ]; omega
    show S q (iter q ((L - 1) * (i + 1)) n) = iter q ((L - 1) * i) n
    rw [← iter_forward, e, iter_period hcyc]
  hmax := fun i => by
    show iter q ((L - 1) * i) n ≤ iter q ((L - 1) * 0) n
    rw [Nat.mul_zero, iter_zero]
    exact iter_le_of_lt hL hcyc hle _
  hper := fun i => by
    show iter q ((L - 1) * (i + L)) n = iter q ((L - 1) * i) n
    rw [Nat.mul_add, Nat.mul_comm (L - 1) L, iter_period_mul hcyc]
  hmin := fun k h1 h2 => by
    show iter q ((L - 1) * k) n ≠ iter q ((L - 1) * 0) n
    rw [Nat.mul_zero, iter_zero]
    intro hEq
    apply hne k h1 h2
    -- going backwards `k` steps and then forwards `k` steps is `L*k` steps
    have hLk : (L - 1) * k + k = L * k := by
      have e : L = (L - 1) + 1 := by omega
      calc (L - 1) * k + k = ((L - 1) + 1) * k := by rw [Nat.add_mul, Nat.one_mul]
        _ = L * k := by rw [← e]
    have h1' : iter q ((L - 1) * k + k) n = iter q k n := by
      rw [iter_add, hEq]
    rw [hLk] at h1'
    have h2' : iter q (L * k) n = n := by
      have hz := iter_period_mul hcyc 0 k
      rw [Nat.zero_add, iter_zero] at hz
      exact hz
    rw [h2'] at h1'
    exact h1'.symm

/-- The bridge-built cycle has maximum `n`, as intended. -/
theorem ofOrbit_M (q n L : Nat) (hL hqp hqo hq3 hn hcyc hle hne) :
    (ofOrbit q n L hL hqp hqo hq3 hn hcyc hle hne).M = n := by
  show iter q ((L - 1) * 0) n = n
  rw [Nat.mul_zero, iter_zero]

/-- The bridge-built cycle has length `L`, as intended. -/
theorem ofOrbit_L (q n L : Nat) (hL hqp hqo hq3 hn hcyc hle hne) :
    (ofOrbit q n L hL hqp hqo hq3 hn hcyc hle hne).L = L := rfl

/-- …and its `k`-th backward element is the `(L-1)k`-th forward iterate. -/
theorem ofOrbit_y (q n L : Nat) (hL hqp hqo hq3 hn hcyc hle hne) (k : Nat) :
    (ofOrbit q n L hL hqp hqo hq3 hn hcyc hle hne).y k = iter q ((L - 1) * k) n :=
  rfl

end Cycle

end Collatz
