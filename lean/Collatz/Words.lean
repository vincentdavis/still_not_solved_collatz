/-
  Collatz/Words.lean

  Kernel-checked witnesses for docs/WORDS.md — the word → residue
  classification: caps, the first collision, realization uniqueness, the
  Sturmian sign law, and the deficit bracket, each at a finite instance.

  The objects.  An admissible word `(b_1..b_k)` has `b_t ≥ 1` and partial sums
  under the subtraction-free caps `2 ^ B_t ≤ 3 ^ t`; `NN k` counts them
  (`N_k = 1, 2, 3, 7, 12, 30, 85, …` — OEIS A100982 shifted).  The chain
  constant is `c_t = 2 ^ b_t · c_{t−1} + 3 ^ {t−1}`, and W1 (realization,
  proved in docs/WORDS.md) says each word is live at exactly one residue
  `Phi_k = c_k · 2^{−B_k} mod 3^k` — stated here multiplied through, so
  everything stays in `Nat` with no inverses.

  What is checked:
    · `wcap` (= `Nat.log2 (3^t)`) equals `floor(t·log2 3)` at pinned values,
      and the jump word takes only values 1, 2 with no `11` factor;
    · the first collision: `(1,1,1,1)` and `(1,1,1,3)` are both admissible
      and share their residue mod 81 (the bump law's minimal instance), and
      that residue is 80 ≡ −1 — the ONLY live residue of either word
      (realization uniqueness, all 81 residues scanned);
    · the all-ones word pins `−1`: `c(1^5) + 2^5 = 3^5`, live at `242`;
    · the extension count `#{B_k = wcap k} = N_{k−1}` at `k = 5, 6, 7`;
    · the Sturmian sign law `N_k² − N_{k−1}N_{k+1} > 0  ↔  jump(k) = 1`
      for `2 ≤ k ≤ 8` (Theorem A proves the `+` direction for ALL `k`;
      the `−` direction at these depths is the kernel's own census);
    · the `k = 5` deficit witness `(S0, S1, S2) = (12, 6, 8)`, `W_5 = 48`,
      inside Conjecture B's bracket `0 < W < 2·S0²`.

  Mathlib-free: Lean 4 core only.
-/
import Collatz.Census

namespace Collatz

/-- `floor (t · log2 3)`, computed exactly: `Nat.log2 (3 ^ t)` is the unique
    `f` with `2 ^ f ≤ 3 ^ t < 2 ^ (f + 1)`. -/
def wcap (t : Nat) : Nat := Nat.log2 (3 ^ t)

/-- The Sturmian jump word of `log2 3`: `wcap (k+1) - wcap k ∈ {1, 2}`. -/
def wjump (k : Nat) : Nat := wcap (k + 1) - wcap k

/-- Chain constant `c_k` of a word: `c_t = 2 ^ b_t · c_{t−1} + 3 ^ {t−1}`. -/
def chainCAux : Nat → Nat → List Nat → Nat
  | _, c, [] => c
  | j, c, b :: bs => chainCAux (j + 1) (2 ^ b * c + 3 ^ j) bs

/-- `c_k` from `c_0 = 0`. -/
def chainC (bs : List Nat) : Nat := chainCAux 0 0 bs

/-- Admissibility: every letter `≥ 1`, every prefix under the cap
    `2 ^ B_t ≤ 3 ^ t` (subtraction-free form of `B_t ≤ floor (t·log2 3)`). -/
def wadmAux : Nat → Nat → List Nat → Bool
  | _, _, [] => true
  | j, B, b :: bs =>
      (1 ≤ b) && (2 ^ (B + b) ≤ 3 ^ (j + 1)) && wadmAux (j + 1) (B + b) bs

/-- Admissible word test. -/
def wadm (bs : List Nat) : Bool := wadmAux 0 0 bs

/-- Stepwise liveness of residue `r` along a word: prefix `t` must satisfy
    `2 ^ B_t · r ≡ c_t (mod 3 ^ t)` (each congruence at its own modulus,
    subtraction-free, matching `deathdepth.live_chains`). -/
def wliveAux : Nat → Nat → Nat → Nat → List Nat → Bool
  | _, _, _, _, [] => true
  | r, j, B, c, b :: bs =>
      ((2 ^ (B + b) * r) % 3 ^ (j + 1) == (2 ^ b * c + 3 ^ j) % 3 ^ (j + 1))
        && wliveAux r (j + 1) (B + b) (2 ^ b * c + 3 ^ j) bs

/-- Liveness from the start state. -/
def wlive (r : Nat) (bs : List Nat) : Bool := wliveAux r 0 0 0 bs

/-- Scan admissible letters `b = 1, 2, …` at level `j + 1` (cap-bounded, so
    fuel `2 (j + 1)` suffices as in `scanQ`), summing `cont` over them. -/
def scanW (cont : Nat → Nat) (B j : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | (fuel + 1), b =>
      if 2 ^ (B + b) ≤ 3 ^ (j + 1) then
        cont (B + b) + scanW cont B j fuel (b + 1)
      else 0

/-- Fold `g` of the final partial sum over all admissible words of length `d`
    extending state `(B, j)`.  `foldW g k 0 0` sums `g B_k` over all
    admissible length-`k` words. -/
def foldW (g : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, B, _ => g B
  | (d + 1), B, j => scanW (fun B' => foldW g d B' (j + 1)) B j (2 * (j + 1)) 1

/-- `N_k` — the number of admissible words of length `k`. -/
def NN (k : Nat) : Nat := foldW (fun _ => 1) k 0 0

/-- Cap values are the pinned `floor (t·log2 3)` figures. -/
theorem wcap_vals :
    wcap 1 = 1 ∧ wcap 2 = 3 ∧ wcap 3 = 4 ∧ wcap 4 = 6 ∧ wcap 5 = 7 ∧
      wcap 12 = 19 := by decide

/-- The jump word takes only the values 1 and 2 (Beatty gaps of an
    `alpha ∈ (1, 2)`), checked for `k < 16`. -/
theorem wjump_one_or_two : ∀ k, k < 16 → wjump k = 1 ∨ wjump k = 2 := by decide

/-- No `11` factor: consecutive jumps sum to at least 3, `k < 15`.  (This is
    the elementary fact that routes Conjecture B's tight test to smoothed
    levels — docs/WORDS.md §7.) -/
theorem wjump_no_11 : ∀ k, k < 15 → 3 ≤ wjump k + wjump (k + 1) := by decide

/-- Word counts: `N_1..N_7 = 1, 2, 3, 7, 12, 30, 85`. -/
theorem NN_vals :
    NN 1 = 1 ∧ NN 2 = 2 ∧ NN 3 = 3 ∧ NN 4 = 7 ∧ NN 5 = 12 ∧ NN 6 = 30 ∧
      NN 7 = 85 := by decide

/-- THE FIRST COLLISION (bump law, minimal instance): both words admissible,
    and `c · 2^{B'} ≡ c' · 2^{B} (mod 81)` — the multiplied-through form of
    `Phi_4(1,1,1,1) = Phi_4(1,1,1,3)`. -/
theorem first_collision :
    wadm [1, 1, 1, 1] = true ∧ wadm [1, 1, 1, 3] = true ∧
      chainC [1, 1, 1, 1] * 2 ^ 6 % 81 = chainC [1, 1, 1, 3] * 2 ^ 4 % 81 := by
  decide

/-- REALIZATION UNIQUENESS at the collision fiber: over ALL 81 residues,
    each of the two colliding words is live exactly at `80 ≡ −1 (mod 81)`.
    (W1: one word, one residue — here checked exhaustively.) -/
theorem realization_unique_k4 :
    ∀ r, r < 81 →
      (wlive r [1, 1, 1, 1] = true ↔ r = 80) ∧
        (wlive r [1, 1, 1, 3] = true ↔ r = 80) := by decide

/-- Slope-blindness witness: the all-ones word has `c = 3^5 − 2^5` (stated
    additively) and is live at `−1 ≡ 242 (mod 3^5)`. -/
theorem all_ones_pins_minus_one :
    chainC [1, 1, 1, 1, 1] + 2 ^ 5 = 3 ^ 5 ∧
      wlive 242 [1, 1, 1, 1, 1] = true := by decide

/-- Extension count (W4): `#{words of length k with B_k = wcap k} = N_{k−1}`,
    at `k = 5, 6, 7`. -/
theorem extension_count_witness :
    foldW (fun B => if B = wcap 5 then 1 else 0) 5 0 0 = NN 4 ∧
      foldW (fun B => if B = wcap 6 then 1 else 0) 6 0 0 = NN 5 ∧
      foldW (fun B => if B = wcap 7 then 1 else 0) 7 0 0 = NN 6 := by decide

/-- THE STURMIAN SIGN LAW at depths `2 ≤ k ≤ 8`:
    `N_{k−1}N_{k+1} < N_k²  ↔  jump(k) = 1` (strict both ways: Theorem A
    proves the forward direction for every `k`; docs/WORDS.md). -/
theorem sign_law_witness :
    ∀ k, k < 9 → 2 ≤ k →
      (NN (k - 1) * NN (k + 1) < NN k * NN k ↔ wjump k = 1) := by decide

/-- Deficit witness at `n = 5` (Conjecture B's integer form): slack moments
    `(S0, S1, S2) = (12, 6, 8)` of `g_5 = (7, 4, 1)`. -/
theorem deficit_moments_k5 :
    foldW (fun _ => 1) 5 0 0 = 12 ∧
      foldW (fun B => wcap 5 - B) 5 0 0 = 6 ∧
      foldW (fun B => (wcap 5 - B) * (wcap 5 - B)) 5 0 0 = 8 := by decide

/-- `0 < W_5 < 2·S0²` with `W_5 = 2·S1² + S1·S0 − S2·S0 = 48`: the `n = 5`
    instance of `0 < c_n < 2` (lower half proved, upper half = Conjecture B). -/
theorem deficit_bracket_k5 :
    2 * 6 * 6 + 6 * 12 = 48 + 8 * 12 ∧ 0 < 48 ∧ 48 < 2 * (12 * 12) := by
  decide

/-- Dead dyadic mass by level `n`: `sum_{i=1}^{n-1} N_i · 2^{m_n − m_{i+1}}` (scaled
    by `2^{m_n}` to stay in `Nat`).  Each admissible `i`-word loses exactly
    `2^{-m_{i+1}}` of 2-adic measure to over-cap extensions at step `i+1`. -/
def deadMass (n : Nat) : Nat :=
  (List.range (n - 1)).foldl (fun acc i => acc + NN (i + 1) * 2 ^ (wcap n - wcap (i + 2))) 0

/-- DYADIC MASS CONSERVATION (docs/WORDS.md §11), scaled by `2^{m_n}`:
    `sum_w 2^{m_n − B_n(w)} + deadMass n = 2^{m_n − 1}` at `n = 4, 5, 6, 7`. -/
theorem dyadic_mass_conservation_witness :
    foldW (fun B => 2 ^ (wcap 4 - B)) 4 0 0 + deadMass 4 = 2 ^ (wcap 4 - 1) ∧
      foldW (fun B => 2 ^ (wcap 5 - B)) 5 0 0 + deadMass 5 = 2 ^ (wcap 5 - 1) ∧
      foldW (fun B => 2 ^ (wcap 6 - B)) 6 0 0 + deadMass 6 = 2 ^ (wcap 6 - 1) ∧
      foldW (fun B => 2 ^ (wcap 7 - B)) 7 0 0 + deadMass 7 = 2 ^ (wcap 7 - 1) := by
  decide

end Collatz
