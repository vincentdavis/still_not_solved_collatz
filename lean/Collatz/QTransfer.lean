/-
  Collatz/QTransfer.lean

  The q-transfer theorem, checked by the kernel at depth ≤ 4:

      S_k(q) = q · S_k(1)  (mod 3^k),   hence   a_k(q) = a_k(1).

  The magnitude-free sieve cannot see `q`.  The paper proof is ten lines
  (docs/FILTER.md): the chain constant is linear in `q` — `c_t(q) = q·c_t(1)`
  from `c_t = 2^{b_t} c_{t−1} + 3^{t−1} q`, `c_0 = 0` — the caps
  `2^{B_t} ≤ 3^t` are q-free, and multiplication by the unit `q` bijects
  `Z/3^k`.  What is checked HERE is the instance the corollary needs: the
  transfer holds exhaustively over every residue mod `3^4` for
  `q = 5, 7, 25` and for `q ≡ −1` — and the survivor counts all equal `aa k`.

  WHY THIS MATTERS.  `q = 5` has a real cycle `{19, 31, 49}`
  (`Examples.lean`-style; census).  Identical sieve statistics for a cycling
  system and the conjecturally cycle-free one mean: no argument whose
  hypotheses are magnitude-free sieve statistics alone can prove `q = 1`
  cyclelessness — instantiated at `q = 5` it would prove a falsehood.  This is
  the sharpened form of docs/WHY_NOT.md's "the sieve never empties".

  ENCODING.  `Census.lean`'s `alive` hardcodes `q = 1` and subtracts.  Here the
  step test is stated subtraction-free — step `t` with `b` halvings is live iff

      2^{B_t} · M  ≡  c_t   (mod 3^t)

  — so a negative `q` enters as its residue (`q ≡ −1 (mod 3^4)` is `qr = 80`),
  and everything stays in `Nat`.  The parity of each `b` is not special-cased:
  a wrong-parity `b` simply fails its congruence.  `liveQ 1` is pinned to
  `Census.lean`'s `aa` by value below.

  Mathlib-free: Lean 4 core only.
-/
import Collatz.Census

namespace Collatz

/-- Scan halving counts `b = 1, 2, …` under the magnitude-free cap
    `2 ^ (B + b) ≤ 3 ^ (j + 1)`, testing the subtraction-free step congruence
    `2 ^ (B + b) * r ≡ 2 ^ b * c + 3 ^ j * qr  (mod 3 ^ (j + 1))` and calling
    `cont` with the new halving total and chain constant.  `fuel := 2 (j + 1)`
    always suffices: `3 ^ (j+1) < 2 ^ (2 (j+1))` caps `b`, and the scan may
    stop at the first over-cap `b` because `2 ^ (B + b)` is increasing. -/
def scanQ (cont : Nat → Nat → Bool) (qr r B j c : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | (fuel + 1), b =>
      if 2 ^ (B + b) ≤ 3 ^ (j + 1) then
        (((2 ^ (B + b) * r) % 3 ^ (j + 1)
            == (2 ^ b * c + 3 ^ j * qr) % 3 ^ (j + 1))
          && cont (B + b) (2 ^ b * c + 3 ^ j * qr))
        || scanQ cont qr r B j c fuel (b + 1)
      else false

/-- `liveQ qr d r B j c`: does the residue `r` admit `d` further backward hops
    under the magnitude-free sieve with offset `q ≡ qr (mod 3 ^ (j + d))`,
    having taken `j` hops for `B` halvings with chain constant `c` so far?
    The chain constant is carried exactly (`c' = 2 ^ b * c + 3 ^ j * qr`),
    never reduced, so each depth's congruence is tested at its own modulus. -/
def liveQ (qr : Nat) : Nat → Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _, _ => true
  | (d + 1), r, B, j, c =>
      scanQ (fun B' c' => liveQ qr d r B' (j + 1) c') qr r B j c
        (2 * (j + 1)) 1

/-- `a_k(q)` — survivors mod `3 ^ k` of the magnitude-free sieve at offset
    `q ≡ qr`.  `aaQ 1` recomputes `Census.lean`'s `aa` by a different route
    (no parity shortcut, no subtraction); the theorems below pin them equal. -/
def aaQ (qr k : Nat) : Nat := countLE (fun r => liveQ qr k r 0 0 0) (3 ^ k - 1)

/-- `transferOK qr k n`: for every `r < n`, residue `r` is live for `q = 1`
    exactly when `qr · r  (mod 3 ^ k)` is live for `q = qr` — the transfer
    bijection, checked pointwise. -/
def transferOK (qr k : Nat) : Nat → Bool
  | 0 => true
  | (r + 1) =>
      (liveQ 1 k r 0 0 0 == liveQ qr k ((qr * r) % 3 ^ k) 0 0 0)
        && transferOK qr k r

/-! `liveQ 1` agrees with `Census.lean`'s `aa` (values 1, 2, 3, 6): the
    subtraction-free encoding changes nothing. -/

theorem aaQ_one : aaQ 1 1 = 1 ∧ aaQ 1 2 = 2 ∧ aaQ 1 3 = 3 ∧ aaQ 1 4 = 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! **The q-transfer, exhaustively at every depth `k ≤ 4`** — all residues
    mod `3 ^ k` for `k = 1, 2, 3, 4`, four offsets.  `qr = 80 ≡ −1 (mod 3^k)`
    for every `k ≤ 4` (`80 = 3^4 − 1`, and `80 mod 3^k = 3^k − 1`), so the
    fourth offset is the `3x − 1` system: the sieve cannot tell it from
    Collatz either. -/

theorem qtransfer_5 : transferOK 5 4 (3 ^ 4) = true := by decide
theorem qtransfer_7 : transferOK 7 4 (3 ^ 4) = true := by decide
theorem qtransfer_25 : transferOK 25 4 (3 ^ 4) = true := by decide
theorem qtransfer_neg_one : transferOK 80 4 (3 ^ 4) = true := by decide

/-- Depths 1–3 as well, for all four offsets: depth-4 transfer does not
    formally entail the shallower set equalities (an audit point), so each
    depth is checked outright. -/
theorem qtransfer_shallow :
    (transferOK 5 1 (3 ^ 1) && transferOK 5 2 (3 ^ 2) && transferOK 5 3 (3 ^ 3)
      && transferOK 7 1 (3 ^ 1) && transferOK 7 2 (3 ^ 2) && transferOK 7 3 (3 ^ 3)
      && transferOK 25 1 (3 ^ 1) && transferOK 25 2 (3 ^ 2) && transferOK 25 3 (3 ^ 3)
      && transferOK 80 1 (3 ^ 1) && transferOK 80 2 (3 ^ 2) && transferOK 80 3 (3 ^ 3))
      = true := by decide

/-! Hence equal survivor counts — `a_k` is q-blind at every checked depth. -/

theorem aaQ_5 : aaQ 5 1 = 1 ∧ aaQ 5 2 = 2 ∧ aaQ 5 3 = 3 ∧ aaQ 5 4 = 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem aaQ_7_4 : aaQ 7 4 = 6 := by decide
theorem aaQ_25_4 : aaQ 25 4 = 6 := by decide
theorem aaQ_neg_one_4 : aaQ 80 4 = 6 := by decide

/-- The transfer image of the `−1` witness: `−q (mod 3 ^ 4)` survives to
    depth 4 for each checked offset (for `q ≡ −1` that image is `+1`… times
    `−1` again: `80 · 80 ≡ 1`, and indeed `1`'s class survives). -/
theorem witness_minus_q :
    liveQ 5 4 (3 ^ 4 - 5) 0 0 0 = true
      ∧ liveQ 7 4 (3 ^ 4 - 7) 0 0 0 = true
      ∧ liveQ 25 4 (3 ^ 4 - 25) 0 0 0 = true
      ∧ liveQ 80 4 1 0 0 0 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end Collatz
