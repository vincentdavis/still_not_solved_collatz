/-
  Collatz/Census.lean

  The theorems inside the census row — and a note on what is not one.

  WHY THIS FILE EXISTS.  The project's accounting table carried a single line,
  "census, death-depth tail, dimension", marked "measurements, not theorems".
  That label was doing too much work.  The row bundles three genuine theorems in
  with three genuine measurements, and the theorems are the load-bearing part of
  the census section: they are *why* the `3n+q` cycle counts look the way they
  do.

  FORMALIZED HERE.

    `q_dvd_sub`    a cycle whose maximum is coprime to `q` forces
                   `q ∣ 2 ^ B − 3 ^ L`.  (Coprimality is a HYPOTHESIS here.
                   Primitivity implies it — a prime dividing `q` divides every
                   element or none, and primitivity rules out "every" — but
                   `primitive` has no Lean definition in this development, so
                   that step is checked in Python, not proved.)  This is the
                   arithmetic condition the census section calls the engine of
                   the whole effect — cycles are not scattered at random across
                   `q`, they concentrate on the `q` that divide some `2^B − 3^L`.

    `burst`        when `2 ^ B − 3 ^ L` equals `q` exactly, the cycle equation
                   collapses to `M · q = c_L`, and every admissible halving
                   vector of that `(L, B)` yields a candidate at once.  One hit
                   can produce many cycles.

    `q1_burst`     and `q = 1` gets exactly one: `2 ^ B − 3 ^ L = 1` with
                   `L ≥ 1` forces `(L, B) = (1, 2)`, the cycle `1 → 4 → 2 → 1`.
                   The proof is a mod-8 count, no deep theorem.  This is the
                   precise sense in which `q = 1` is not like the others, and it
                   is the reason the census experiment answers its own question
                   in the negative.

  NOT FORMALIZED.  What remains in that row is two measurements and one open
  question.  Each is declined for its own reason, and the reasons are not the
  same:

    * variance/mean = 4.614, and the rejection of the Poisson model.  The
      statistic itself IS a proposition about integers — `N·Σc² − (Σc)² >
      4·N·Σc` needs no `ℝ` — so the honest reason is infeasibility, not
      category: kernel-reducing a 333-system census is out of reach with
      `native_decide` banned.  "Poisson is rejected" is separately a modelling
      judgement, and that part is not a proposition at all.

    * the death-depth tail RATE, bracketed to `[0.896, 0.947]`.  Open, not
      merely unformalized: separating the two candidate models needs `k ≈ 36`,
      about `2 × 10¹³` tree nodes (docs/DEATH_DEPTH.md).  The `a_k` values
      underneath it are a different matter and ARE formalized — see §4.

    * the box dimension of the surviving set in `ℤ₃`, estimated `0.90–0.95`.
      It rests on an unresolved limit, so it would not be a theorem even with
      `ℝ` in hand.

  So this file does not flip that row; it splits it.  See the accounting table.

  Mathlib-free: Lean 4 core only.
-/
import Collatz.Cycle
import Collatz.Reach

namespace Collatz

namespace Cycle

variable {q : Nat} (C : Cycle q)

/-! ## 1. `q ∣ 2 ^ B − 3 ^ L`

Every term of the `c_k` recursion carries a factor of `q`, so `q ∣ c_L`; the
cycle equation then hands the divisibility to `2 ^ B − 3 ^ L`, provided the
maximum is coprime to `q`.  Primitivity gives that, but the implication is not
formalized here — see the header. -/

/-- Every `c_k` is a multiple of `q`.  Immediate from the recursion. -/
theorem q_dvd_cc : ∀ k, q ∣ C.cc k := by
  intro k
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨2 ^ C.bb (k + 1) * t + 3 ^ k, ?_⟩
      show 2 ^ C.bb (k + 1) * C.cc k + 3 ^ k * q
           = q * (2 ^ C.bb (k + 1) * t + 3 ^ k)
      rw [ht]
      simp [Nat.mul_add, Nat.mul_comm, Nat.mul_assoc]

/-- The cycle equation with the subtraction performed — legitimate because
    `Cycle.T7` puts `3 ^ L` strictly below `2 ^ B`. -/
theorem M_mul_sub : C.M * (2 ^ C.BB C.L - 3 ^ C.L) = C.cc C.L := by
  have h := C.T7_eq
  have h7 := C.T7
  have e : 2 ^ C.BB C.L - 3 ^ C.L + 3 ^ C.L = 2 ^ C.BB C.L := by omega
  have hm : C.M * (2 ^ C.BB C.L - 3 ^ C.L) + C.M * 3 ^ C.L
          = C.M * (2 ^ C.BB C.L) := by
    rw [← Nat.mul_add, e]
  have e2 : C.M * 3 ^ C.L = 3 ^ C.L * C.M := Nat.mul_comm _ _
  have e3 : C.M * 2 ^ C.BB C.L = 2 ^ C.BB C.L * C.M := Nat.mul_comm _ _
  omega

/-- **The census's arithmetic engine.**  A cycle whose maximum is coprime to `q`
    — in particular any primitive cycle — forces `q ∣ 2 ^ B − 3 ^ L`.

    This is why cycles concentrate on particular `q` instead of scattering: `q`
    has to divide one of the numbers `2 ^ B − 3 ^ L`, and those are sparse. -/
theorem q_dvd_sub (hcop : Nat.gcd C.M q = 1) : q ∣ 2 ^ C.BB C.L - 3 ^ C.L := by
  have hdvd : q ∣ C.M * (2 ^ C.BB C.L - 3 ^ C.L) := by
    rw [C.M_mul_sub]; exact C.q_dvd_cc C.L
  have hcop' : Nat.Coprime q C.M := Nat.Coprime.symm hcop
  exact (Nat.Coprime.dvd_of_dvd_mul_left hcop' hdvd)

/-! ## 2. The burst -/

/-- **The burst.**  When `2 ^ B − 3 ^ L` is exactly `q`, the cycle equation
    collapses to `M · q = c_L`.  Every admissible halving vector of that
    `(L, B)` then yields a candidate maximum at once, which is how one
    arithmetic coincidence produces a cluster of cycles rather than one.

    NOTE: that counting consequence is docs/CENSUS.md's Result 3 and remains a
    *measurement*.  What is proved here is only the collapse `M · q = c_L`, for
    a cycle that already exists. -/
theorem burst (h : 2 ^ C.BB C.L - 3 ^ C.L = q) : C.M * q = C.cc C.L := by
  have := C.M_mul_sub
  rw [h] at this
  exact this

end Cycle

/-! ## 3. `q = 1` gets exactly one burst

`2 ^ B = 3 ^ L + 1`.  The right-hand side is always `2` or `4` mod `8`, never
`0`, so `2 ^ B ≤ 4`; but for `L ≥ 2` it is also at least `10`.  So `L = 1`, and the
only burst `q = 1` ever gets is the cycle everybody already knows. -/

/-- `3 ^ L + 1` is `2` or `4` mod `8` — never `0`, so never divisible by `8`.
    (It is in fact `4` for odd `L` and `2` for even `L`, but only the
    disjunction is stated, and only the disjunction is used.) -/
theorem three_pow_succ_mod_eight (L : Nat) :
    (3 ^ L + 1) % 8 = 2 ∨ (3 ^ L + 1) % 8 = 4 := by
  induction L with
  | zero => left; decide
  | succ L ih =>
      have e : (3 : Nat) ^ (L + 1) = 3 * 3 ^ L := by rw [Nat.pow_succ]; omega
      rw [e]
      -- 3^L is 1 or 3 mod 8, and multiplying by 3 swaps them
      have h8 : 3 ^ L % 8 = 1 ∨ 3 ^ L % 8 = 3 := by omega
      omega

/-- `2 ^ B` is divisible by `8` as soon as `B ≥ 3`. -/
theorem eight_dvd_two_pow {B : Nat} (h : 3 ≤ B) : 8 ∣ 2 ^ B := by
  obtain ⟨d, hd⟩ : ∃ d, B = 3 + d := ⟨B - 3, by omega⟩
  subst hd
  exact ⟨2 ^ d, by rw [Nat.pow_add]⟩

/-- `3 ^ L ≥ 9` for `L ≥ 2`. -/
theorem nine_le_three_pow {L : Nat} (h : 2 ≤ L) : 9 ≤ 3 ^ L := by
  obtain ⟨d, hd⟩ : ∃ d, L = 2 + d := ⟨L - 2, by omega⟩
  subst hd
  have : (3 : Nat) ^ (2 + d) = 9 * 3 ^ d := by rw [Nat.pow_add]
  have hp : 0 < 3 ^ d := Nat.pow_pos (by decide)
  omega

/-- **`q = 1` gets exactly one burst.**  The only solution of
    `2 ^ B − 3 ^ L = 1` with `L ≥ 1` is `(L, B) = (1, 2)` — the trivial cycle
    `1 → 4 → 2 → 1`.

    No deep theorem is needed, which is the point: for `q > 1` the condition
    `q ∣ 2 ^ B − 3 ^ L` is satisfiable with a modest `2 ^ B − 3 ^ L` and cycles
    are manufactured wholesale, while for `q = 1` it is vacuous and the real
    constraint is of a completely different character. -/
theorem q1_burst {L B : Nat} (hL : 1 ≤ L) (h : 2 ^ B = 3 ^ L + 1) :
    L = 1 ∧ B = 2 := by
  have hmod := three_pow_succ_mod_eight L
  -- B ≤ 2, because 8 never divides 3^L + 1
  have hB : B ≤ 2 := by
    rcases Nat.lt_or_ge B 3 with hb | hb
    · omega
    · exfalso
      obtain ⟨t, ht⟩ := eight_dvd_two_pow hb
      omega
  -- and 3^L + 1 = 2^B ≤ 4 forces L = 1
  have h4 : (2 : Nat) ^ B ≤ 4 := by
    rcases (show B = 0 ∨ B = 1 ∨ B = 2 by omega) with e | e | e <;> subst e <;> decide
  have hL1 : L = 1 := by
    rcases Nat.lt_or_ge L 2 with hl | hl
    · omega
    · exfalso
      have := nine_le_three_pow hl
      omega
  subst hL1
  have e3 : (3 : Nat) ^ 1 = 3 := by decide
  rw [e3] at h
  -- 2^B = 4
  rcases (show B = 0 ∨ B = 1 ∨ B = 2 by omega) with e | e | e <;> subst e
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact ⟨rfl, rfl⟩

/-! ## 4. The death-depth tail: `a_k`, exactly

docs/DEATH_DEPTH.md's headline is `P(d ≥ k) = a_k / 3^k` with
`a_k = 1, 2, 3, 6, 10, 22, 50, 104, …`, and it calls those values **exact, not
sampled**.  They are, and they are decidable: the magnitude-free sieve keeps only
the test `2 ^ (B_k) ≤ 3 ^ k`, which is `ℝ`-free, and survival to depth `k`
depends only on the residue mod `3 ^ k`.  So `a_k` is the size of a finite,
computable set and the kernel can check it outright.

What is genuinely open is the *rate* — `docs/DEATH_DEPTH.md` brackets it to
`[0.896, 0.947]` and records that separating the two candidate models needs
`k ≈ 36`.  Declining the rate is right; declining `a_k` with it was the same
bundling error this file is about, one row down. -/

/-- Scan halving counts `b, b + 2, b + 4, …` under the magnitude-free size cap
    `2 ^ (B + b) ≤ 3 ^ (j + 1)`, calling `cont` on each admissible predecessor.
    `fuel` bounds the scan; `2 (j + 1)` always suffices, because
    `3 ^ (j+1) < 2 ^ (2 (j+1))` caps `b`. -/
def scanB (cont : Nat → Nat → Bool) (y B j : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | (fuel + 1), b =>
      if 2 ^ (B + b) ≤ 3 ^ (j + 1) then
        (((2 ^ b * y - 1) % 3 == 0) && cont ((2 ^ b * y - 1) / 3) (B + b))
          || scanB cont y B j fuel (b + 2)
      else false

/-- `alive d y B j`: does the residue `y` admit `d` further backward hops under
    the magnitude-free sieve, having taken `j` hops for `B` halvings so far?

    The parity of `b` is forced by `y mod 3` — even when `y ≡ 1`, odd when
    `y ≡ 2`, impossible when `3 ∣ y` — which is the same rule the reverse-path
    buttons on the page enforce. -/
def alive : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => true
  | (d + 1), y, B, j =>
      if y % 3 == 0 then false
      else scanB (fun z B' => alive d z B' (j + 1)) y B j (2 * (j + 1))
             (if y % 3 == 1 then 2 else 1)

/-- **`a_k`** — the number of residues mod `3 ^ k` surviving the magnitude-free
    sieve to depth `k`.  `P(d ≥ k) = a_k / 3 ^ k`. -/
def aa (k : Nat) : Nat := countLE (fun r => alive k r 0 0) (3 ^ k - 1)

/-! The values docs/DEATH_DEPTH.md reports, now checked by the kernel rather
    than by a Python program.

    The ceiling is `k = 4`, and it is mechanical rather than mathematical:
    `countLE` recurses once per residue, so `k = 5` (243 residues) exceeds Lean's
    default `maxRecDepth`, and raising it needs `set_option`, which
    `lean/check.sh` bans.  A balanced or tail-recursive count would go further.
    The sequence continues 10, 22, 50, 104, 254, 538, … and
    `collatz_maxodd.deathdepth.surviving_residue_count` reaches `k = 24`; the
    Python side checks the two agree. -/

theorem aa_1 : aa 1 = 1 := by decide
theorem aa_2 : aa 2 = 2 := by decide
theorem aa_3 : aa 3 = 3 := by decide
theorem aa_4 : aa 4 = 6 := by decide
/-- **`a_k ≥ 1` at every checked depth** — the sieve never empties.
    `Collatz.all_digits_two` is the reason it never will: the class of `−1` has
    every base-3 digit equal to 2, which is exactly the residue an odd halving
    count needs, so the all-ones chain is legal at every depth. -/
theorem aa_pos : 1 ≤ aa 1 ∧ 1 ≤ aa 2 ∧ 1 ≤ aa 3 ∧ 1 ≤ aa 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end Collatz
