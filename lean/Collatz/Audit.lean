/-
  Collatz/Audit.lean

  AXIOM CERTIFICATE.

  `#print axioms` for EVERY named declaration in this project — every theorem,
  every definition, the `Cycle` structure itself, and every `Cycle` instance.
  These commands run at build time, so the `lake build` log IS the certificate:
  if any declaration below depended on `sorryAx`, it would say so here.

  Expected output for every line: `depends on axioms: [propext, Quot.sound]`
  (or "does not depend on any axioms").  `propext` and `Quot.sound` come from
  core `Nat` lemmas and from the well-founded recursion used to define `v2` and
  `oddPart`.  Neither `Classical.choice` nor `sorryAx` appears anywhere.

  COVERAGE.  The list below is complete for named declarations, with one
  deliberate exception: the `private theorem pred_step_absurd` in
  `Collatz/Core.lean`, whose mangled private name is not addressable from this
  file.  It is covered *transitively*: `#print axioms` reports the transitive
  closure of a declaration's dependencies, and `pred_step_absurd` is used only
  by `pred_unique_core`, which is audited below.  Anonymous `example`s cannot
  be `#print axioms`-ed at all, but a `sorry` in one would emit a build warning,
  and this build has zero warnings.

  There is a machine check of the same thing in `lean/check.sh`.
-/
import Collatz.Guards

/-! ## Definitions (`Collatz/Odd.lean`) -/
#print axioms Collatz.v2
#print axioms Collatz.oddPart
#print axioms Collatz.S

/-! ## `Collatz/Odd.lean` -/
#print axioms Collatz.oddPart_of_odd
#print axioms Collatz.oddPart_of_even
#print axioms Collatz.v2_of_odd
#print axioms Collatz.v2_of_even
#print axioms Collatz.oddPart_two_mul
#print axioms Collatz.oddPart_mod_two
#print axioms Collatz.oddPart_pos
#print axioms Collatz.two_pow_v2_mul_oddPart
#print axioms Collatz.three_mul_add_even
#print axioms Collatz.S_spec
#print axioms Collatz.S_odd
#print axioms Collatz.S_pos

/-! ## `Collatz/Core.lean` -/
#print axioms Collatz.two_pow_le
#print axioms Collatz.two_pow_split
#print axioms Collatz.two_pow_shift
#print axioms Collatz.T0_core
#print axioms Collatz.no_odd_pred_of_three_dvd
#print axioms Collatz.T1_core
#print axioms Collatz.T1_core_mod4
#print axioms Collatz.lt_S_of_three_mod_four
#print axioms Collatz.T2_core
#print axioms Collatz.T2_pred
#print axioms Collatz.pred_unique_core       -- transitively covers pred_step_absurd
#print axioms Collatz.pred_unique
#print axioms Collatz.pred_exists
#print axioms Collatz.pred_le_eq_q1
#print axioms Collatz.pred_le_unique_q1
#print axioms Collatz.pred_lt_exists_q1
#print axioms Collatz.pred_le_iff_q1
#print axioms Collatz.T5_ineq
#print axioms Collatz.T5_core_sharp
#print axioms Collatz.T5_core_q1

/-! ## `Collatz/Cycle.lean` — the structure, its defs, and T0–T8 -/
#print axioms Collatz.Cycle
#print axioms Collatz.Cycle.M
#print axioms Collatz.Cycle.bb
#print axioms Collatz.Cycle.BB
#print axioms Collatz.Cycle.cc
#print axioms Collatz.Cycle.M_odd
#print axioms Collatz.Cycle.M_pos
#print axioms Collatz.Cycle.y_pos
#print axioms Collatz.Cycle.step_mul
#print axioms Collatz.Cycle.S_eq
#print axioms Collatz.Cycle.S_le_M
#print axioms Collatz.Cycle.S_M_le_M
#print axioms Collatz.Cycle.S_S_le_M
#print axioms Collatz.Cycle.M_ge_three_of_L
#print axioms Collatz.Cycle.shift_zero
#print axioms Collatz.Cycle.y_ne_of_lt
#print axioms Collatz.Cycle.T0
#print axioms Collatz.Cycle.T1
#print axioms Collatz.Cycle.T1_mod4
#print axioms Collatz.Cycle.T1_q1
#print axioms Collatz.Cycle.T2
#print axioms Collatz.Cycle.T2_mod3
#print axioms Collatz.Cycle.T2_unique
#print axioms Collatz.Cycle.T2_q1
#print axioms Collatz.Cycle.T3_gen
#print axioms Collatz.Cycle.T3
#print axioms Collatz.Cycle.T3_of_L
#print axioms Collatz.Cycle.T4_mod9
#print axioms Collatz.Cycle.T4_base_gen
#print axioms Collatz.Cycle.T4_base
#print axioms Collatz.Cycle.T4_base_of_L
#print axioms Collatz.Cycle.T5_gen
#print axioms Collatz.Cycle.T5
#print axioms Collatz.Cycle.T5'
#print axioms Collatz.Cycle.T5_of_L
#print axioms Collatz.Cycle.T8
#print axioms Collatz.Cycle.T8_mod16
#print axioms Collatz.Cycle.T3_T8
#print axioms Collatz.Cycle.bb_spec
#print axioms Collatz.Cycle.bb_pos
#print axioms Collatz.Cycle.closed_form
#print axioms Collatz.Cycle.cc_pos
#print axioms Collatz.Cycle.T6
#print axioms Collatz.Cycle.T6_iff
#print axioms Collatz.Cycle.T2_bb
#print axioms Collatz.Cycle.T5_bb
#print axioms Collatz.Cycle.T5_bb_gen
#print axioms Collatz.Cycle.T7_eq
#print axioms Collatz.Cycle.T7

/-! ## `Collatz/Bridge.lean` — forward iteration and the soundness bridge -/
#print axioms Collatz.iter
#print axioms Collatz.iter_zero
#print axioms Collatz.iter_succ
#print axioms Collatz.iter_add
#print axioms Collatz.iter_forward
#print axioms Collatz.iter_odd
#print axioms Collatz.iter_period
#print axioms Collatz.iter_period_mul
#print axioms Collatz.iter_le_of_lt
#print axioms Collatz.Cycle.ofOrbit
#print axioms Collatz.Cycle.ofOrbit_M
#print axioms Collatz.Cycle.ofOrbit_L
#print axioms Collatz.Cycle.ofOrbit_y

/-! ## Cycle instances — hand-built (`Examples`) and bridge-built (`Guards`) -/
#print axioms Collatz.trivialCycle
#print axioms Collatz.cycle7
#print axioms Collatz.cycle5
#print axioms Collatz.one
#print axioms Collatz.two7
#print axioms Collatz.three5
