/-
  Collatz/Unproved.lean

  WHAT IS **NOT** FORMALIZED, AND WHY.

  This file contains NO declarations and no unproved placeholders.  It exists
  so that the gaps are recorded inside the source tree, not only in a README.
  Everything listed here is stated as a comment; nothing here is available as
  a Lean theorem, and nothing elsewhere in the project depends on it.

  ---------------------------------------------------------------------------
  1.  T4 "recurses to higher powers of 3"          (mod 108, mod 324, …)
  ---------------------------------------------------------------------------
  Formalized: only the base level, `Cycle.T4_base` (`M ≡ 17 or 29 mod 36`).

  NOT formalized:
      M > 11q/7  →  M ≡ 17q, 29q, 53q, 101q (mod 108)
      M > 49q/5  →  M ≡ 101q, 125q, 161q, 233q, 269q, 317q (mod 324)

  WHY NOT: each further level needs (a) its own size threshold `M > C_k · q`,
  (b) the fact that `b_k` is then uniquely determined (parity from Lemma U
  plus a size bound), and (c) a 3-adic induction that is essentially a
  `padicValNat` development one would have to build from scratch without
  Mathlib.  Estimated 200–400 lines.  Note also that the recursion is NOT
  uniform: it is a single forced chain only for depths 1–3, and becomes a
  branching sieve from depth 4 on (the backward prefix (b₁,b₂,b₃,b₄)=(1,1,1,3)
  has 2^{B₄} = 64 < 81 = 3⁴, so the size test `y₄ ≤ M` imposes nothing there).
  Formalizing "T4 recurses" as a uniform statement would be formalizing a
  FALSE statement.

  ---------------------------------------------------------------------------
  2.  T6 threshold form:  `M ≥ 2^68 → B_k ≤ ⌊k · log₂ 3⌋`
  ---------------------------------------------------------------------------
  Formalized: `Cycle.T6`, the exact inequality `2^{B_k} M ≤ 3^k M + c_k`.
  This is the correct and unconditional statement.

  NOT formalized: the implication to `2^{B_k} ≤ 3^k` under a largeness
  hypothesis on `M`.

  WHY NOT: this needs `c_k < M (2^{B_k} − 3^k)`-style estimates bounding `c_k`
  against `2^{B_k}`, plus an externally-justified numeric threshold on `M`
  (which comes from continued-fraction / verification-limit input that is not
  proved anywhere in this project).  The unconditional version is FALSE —
  `Collatz/Examples.lean`'s `cycle5` (q = 5, M = 49) has `B₃ = 5 > 4`.

  ---------------------------------------------------------------------------
  3.  T6 backward-prefix counts  (1, 2, 3, 7, 12, 30, 85, …)
  ---------------------------------------------------------------------------
  NOT formalized, and should not be: this is a *computation* over a tree with
  ~8^k nodes, not a theorem.  `decide` will not scale past k ≈ 4.  It belongs
  in the Python side of the project.

  ---------------------------------------------------------------------------
  4.  T7 quantitative part:  `2^B / 3^L` within ~1/M of 1, and the Diophantine
      (Baker / continued-fraction) consequence
  ---------------------------------------------------------------------------
  Formalized: `Cycle.T7_eq` (the cycle equation, subtraction-free) and
  `Cycle.T7` (`3^L < 2^{B_L}`).

  NOT formalized: anything rational or transcendental.  Rationals would need a
  `ℚ` development; the irrationality-measure input (Baker 1968, Rhin 1987,
  Laurent–Mignotte–Nesterenko) is out of reach without Mathlib and largely out
  of reach with it.

  ---------------------------------------------------------------------------
  5.  The 2-adic forward sieve beyond `Cycle.T8`
  ---------------------------------------------------------------------------
  Formalized: `Cycle.T8` (`M ≢ 9 mod 16`) and `Cycle.T3_T8`
  (`M ≡ 5, 17, 29 mod 48`), both with no size hypothesis.

  NOT formalized: the deeper kills at `a = 7, 10, 12, 15, …` (`M ≢ 97, 125
  mod 128`, etc.), nor the limiting density 0.2863153965.  Each individual kill
  is the same three-line forward computation as T8 and could be added by hand;
  the *general* statement needs an induction over forward exponent vectors, and
  the density statement needs analysis that has no place in this development.

  ---------------------------------------------------------------------------
  6.  Soundness of the `Cycle` encoding          [NOW FORMALIZED — see Bridge]
  ---------------------------------------------------------------------------
  This entry used to read "NOT formalized".  It now IS formalized, both ways:

  * FORWARD (real cycle ⇒ `Cycle q`): `Cycle.ofOrbit` in `Collatz/Bridge.lean`
    builds a `Cycle q` from hypotheses that mention only the forward map `S_q`
    — `n` odd, `iter q L n = n`, `n` maximal on the orbit, `L` least such.
    Those are the textbook defining conditions of "n is the largest element of
    an `S_q`-cycle of length L".  Hence every theorem in `Collatz/Cycle.lean`
    is a theorem about every genuine cycle, not only about the postulated
    structure.  `Collatz/Guards.lean` uses it to build `one`, `two7`, `three5`.

  * BACKWARD (`Cycle q` ⇒ real cycle): `Cycle.S_eq` shows the listed elements
    are closed under `S_q` and permuted cyclically, and `Cycle.y_ne_of_lt`
    shows `y 0, …, y (L-1)` are pairwise DISTINCT — so a `Cycle q` cannot be a
    shorter orbit padded out to length `L`.

  STILL NOT formalized: a `List`-based front end (`ofList : List Nat → …`),
  which would only be sugar over `ofOrbit`; and any statement that a cycle
  EXISTS for a given `q`, which is exactly the open problem.

  ---------------------------------------------------------------------------
  7.  The elephant: no nontrivial `q = 1` cycle is known to exist
  ---------------------------------------------------------------------------
  NOT PROVED, and not provable here: that `Cycle 1` has an instance with
  `M > 1`.  It is the Collatz cycle conjecture that none does.

  Consequence for reading this development honestly: the theorems whose
  hypotheses are `(C : Cycle 1)` together with `M > 1` / `M ≥ 2` / `L ≥ 2` —
  namely `T2_q1`, `T3`, `T3_of_L`, `T4_base`, `T4_base_of_L`, `T5`, `T5'`,
  `T5_of_L`, `T5_bb`, `T3_T8` — are CONDITIONAL statements about a hypothetical
  object, and are vacuously true if the Collatz cycle conjecture holds.  That
  is what a constraint on a hypothetical counterexample *is*; it is not a
  defect.  But it does mean those particular theorems have no witness, so the
  general-`q` versions (`T1_mod4`, `T2`, `T3_gen`, `T4_mod9`, `T4_base_gen`,
  `T5_gen`, `T5_bb_gen`, `T6`, `T7`) carry the evidential load: those DO have
  witnesses (`three5 : Cycle 5`, `two7 : Cycle 7`), so the derivation machinery
  is demonstrably not broken.  `Cycle 1` itself is inhabited by `one` = {1}.

  ---------------------------------------------------------------------------
  4.  KÖNIG'S LEMMA — the missing link in Collatz/Equivalence.lean
  ---------------------------------------------------------------------------
  Formalized: `BackChain q M` (an INFINITE bounded backward chain) implies a
  periodic point of `S_q` at or below `M`, and for `q = 1, M > 1` a NONTRIVIAL
  one.  That is `BackChain.exists_periodic` / `exists_nontrivial_periodic`.

  NOT formalized:
      (M survives the backward sieve at every finite depth k)
        =>  (an infinite backward chain bounded by M exists)

  i.e. the step from "chains of every finite length" to "one infinite chain".
  This is KÖNIG'S LEMMA applied to the tree of backward chains from M.  Two
  pieces would be needed:

    (a) that the tree is finitely branching — true, and elementary: a
        predecessor y of x satisfies 3y + q = 2^b x, so y <= M bounds
        2^b <= (3M + q)/x, hence only finitely many b are admissible;

    (b) König's lemma itself, which for a finitely-branching tree needs
        DEPENDENT CHOICE.  It is not provable in the choice-free fragment the
        rest of this project lives in, and adding it would put `Classical.choice`
        into the axiom certificate of Collatz/Audit.lean.

  This is a deliberate boundary, not an oversight.  The mathematically
  substantive half — pigeonhole plus the fact that `1` cannot occur in a
  q = 1 chain above 1 — is fully proved and choice-free.  What is assumed
  away is a standard compactness step.

  Consequence for how the result should be read: what is machine-checked is

      infinite bounded backward chain  <=>  cycle

  and NOT the slightly stronger, more quotable

      survives every finite depth      <=>  cycle

  which needs (a) + (b) on top.

-/
