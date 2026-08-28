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
import Collatz.Length
import Collatz.Minimum
import Collatz.Reach
import Collatz.Periodic

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

/-! ## Pigeonhole and the sieve/cycle equivalence (`Collatz/Equivalence.lean`).

`exists_repeat` is proved by an explicit recursive search rather than by
classical choice, so these stay at `[propext, Quot.sound]` like the rest. -/

#print axioms Collatz.hasEq
#print axioms Collatz.Siter
#print axioms Collatz.BackChain
#print axioms Collatz.hasEq_true
#print axioms Collatz.hasEq_false
#print axioms Collatz.exists_repeat
#print axioms Collatz.S_one_eq_one
#print axioms Collatz.BackChain.iter
#print axioms Collatz.BackChain.exists_periodic
#print axioms Collatz.BackChain.eq_one_of_mem
#print axioms Collatz.BackChain.ne_one
#print axioms Collatz.BackChain.exists_nontrivial_periodic
#print axioms Collatz.Cycle.toBackChain
#print axioms Collatz.q7_has_periodic_point
#print axioms Collatz.Cycle.periodic_of_max_gt_one

/-! ## Cycle-length bound (`Collatz/Length.lean`).

The Baker input is a HYPOTHESIS of `length_bound`, not an axiom: it appears
in the theorem's statement, so it cannot hide in the certificate below. -/

#print axioms Collatz.Cycle.prodFrom
#print axioms Collatz.Cycle.prodG
#print axioms Collatz.Cycle.prodFrom_pos
#print axioms Collatz.Cycle.prodG_eq
#print axioms Collatz.Cycle.prodFrom_shift
#print axioms Collatz.Cycle.prodFrom_one_eq_zero
#print axioms Collatz.Cycle.prod_squeeze
#print axioms Collatz.Cycle.pow_le_of_min
#print axioms Collatz.pow_succ_le
#print axioms Collatz.Cycle.prod_squeeze_max
#print axioms Collatz.Cycle.pow_ge_of_max
#print axioms Collatz.Cycle.countOnes
#print axioms Collatz.Cycle.two_mul_le_BB_add_countOnes
#print axioms Collatz.Cycle.single_halving_count
#print axioms Collatz.Cycle.squeeze
#print axioms Collatz.Cycle.length_bound
#print axioms Collatz.Cycle.length_bound_q1
#print axioms Collatz.Cycle.pow_le_m
#print axioms Collatz.Cycle.length_bound_m
#print axioms Collatz.cycle5_BB
#print axioms Collatz.cycle5_min
#print axioms Collatz.cycle5_length_bound
#print axioms Collatz.cycle5_length_bound_m

/-! ## The minimum of a cycle (`Collatz/Minimum.lean`).

The minimum is *derived*, not postulated: `argMinFrom` is structural recursion,
so nothing here needs choice, and no existing instance changed.  The hypothesis
`q < m` is load-bearing — `min_bb_out_needs_hypothesis` exhibits a real cycle
that fails it and fails the conclusion. -/

#print axioms Collatz.argMinFrom
#print axioms Collatz.argMinFrom_pos
#print axioms Collatz.argMinFrom_le
#print axioms Collatz.argMinFrom_min
#print axioms Collatz.Cycle.y_add_mul
#print axioms Collatz.Cycle.y_mod
#print axioms Collatz.Cycle.exists_idx
#print axioms Collatz.Cycle.minIdx
#print axioms Collatz.Cycle.m
#print axioms Collatz.Cycle.minIdx_pos
#print axioms Collatz.Cycle.minIdx_le
#print axioms Collatz.Cycle.m_le
#print axioms Collatz.Cycle.m_odd
#print axioms Collatz.Cycle.m_pos
#print axioms Collatz.Cycle.m_le_M
#print axioms Collatz.Cycle.m_le_y_le_M
#print axioms Collatz.Cycle.m_step
#print axioms Collatz.Cycle.m_bb_pos
#print axioms Collatz.Cycle.min_bb_out
#print axioms Collatz.Cycle.m_step_one
#print axioms Collatz.Cycle.min_mod4
#print axioms Collatz.Cycle.min_mod4'
#print axioms Collatz.Cycle.min_bb_in
#print axioms Collatz.Cycle.min_not_three
#print axioms Collatz.Cycle.min_gt_one_q1
#print axioms Collatz.Cycle.min_mod4_q1
#print axioms Collatz.Cycle.min_mod12_q1
#print axioms Collatz.Cycle.ends_disjoint_q1
#print axioms Collatz.cycle17
#print axioms Collatz.cycle5_minIdx
#print axioms Collatz.cycle5_m
#print axioms Collatz.cycle7_m
#print axioms Collatz.cycle17_m
#print axioms Collatz.trivial_m
#print axioms Collatz.cycle5_m_le
#print axioms Collatz.cycle5_q_lt_m
#print axioms Collatz.cycle5_min_out
#print axioms Collatz.cycle5_min_mod4
#print axioms Collatz.cycle5_max_mod4
#print axioms Collatz.cycle5_ends_mod4
#print axioms Collatz.cycle5_min_in
#print axioms Collatz.cycle17_minIdx
#print axioms Collatz.cycle17_bb_out
#print axioms Collatz.min_bb_out_needs_hypothesis
#print axioms Collatz.cycle37
#print axioms Collatz.cycle37_M
#print axioms Collatz.cycle37_minIdx
#print axioms Collatz.cycle37_m
#print axioms Collatz.cycle37_bb_out
#print axioms Collatz.min_bb_out_needs_its_own_hypothesis
#print axioms Collatz.min_bb_out_hypothesis_not_necessary

/-! ## `L ≤ |R(O)|` (`Collatz/Reach.lean`).

No finite-set machinery: `R(O)` is bounded by `O`, so it is counted by a
recursion over `[0, O]` and the bound comes from the project's own choice-free
pigeonhole. -/

#print axioms Collatz.countLT
#print axioms Collatz.countLE
#print axioms Collatz.countLT_succ
#print axioms Collatz.countLT_mono
#print axioms Collatz.countLT_lt
#print axioms Collatz.countLT_inj
#print axioms Collatz.countLT_lt_countLE
#print axioms Collatz.countLE_pos_eq
#print axioms Collatz.Cycle.length_le_count
#print axioms Collatz.Cycle.length_le_M
#print axioms Collatz.Cycle.reachIn
#print axioms Collatz.Cycle.inR
#print axioms Collatz.Cycle.reach_y
#print axioms Collatz.Cycle.inR_y
#print axioms Collatz.Cycle.length_le_reach
#print axioms Collatz.Cycle.length_le_reach_M
#print axioms Collatz.Cycle.length_le_odd_count
#print axioms Collatz.Cycle.length_le_odd_not_three_count
#print axioms Collatz.cycle5_length_le_reach
#print axioms Collatz.cycle7_length_le_reach
#print axioms Collatz.cycle37_length_le_reach
#print axioms Collatz.cycle5_length_le_M

/-! ## Periodic points and the `−1` witness (`Collatz/Periodic.lean`).

The first file to leave ℕ — the witness is negative, so it has to.  Core `Int`
only; still no Mathlib, still no `ℝ`, still no choice. -/

#print axioms Collatz.PB
#print axioms Collatz.Pc
#print axioms Collatz.two_pow_pos
#print axioms Collatz.three_pow_pos
#print axioms Collatz.two_pow_le_three_pow
#print axioms Collatz.two_pow_int_le_add
#print axioms Collatz.two_pow_int_le
#print axioms Collatz.eq_one_of_pos_mul_eq_one
#print axioms Collatz.two_pow_lt_three_pow
#print axioms Collatz.IsPeriodic
#print axioms Collatz.IsPeriodic.closed
#print axioms Collatz.IsPeriodic.cycle_equation
#print axioms Collatz.periodic_unique
#print axioms Collatz.ones
#print axioms Collatz.PB_ones
#print axioms Collatz.Pc_ones
#print axioms Collatz.onesPeriodic
#print axioms Collatz.minus_one_of_ones
#print axioms Collatz.ones_not_a_cycle
#print axioms Collatz.const
#print axioms Collatz.PB_const
#print axioms Collatz.Pc_const
#print axioms Collatz.const_equation
#print axioms Collatz.constTwoPeriodic
#print axioms Collatz.const_positive_integer
#print axioms Collatz.neg_one_emod
#print axioms Collatz.neg_one_residue
#print axioms Collatz.digit_pow_sub_one
#print axioms Collatz.shift_pow_sub_one
#print axioms Collatz.all_digits_two
#print axioms Collatz.neg_one_all_digits_two
#print axioms Collatz.Cycle.toPeriodic
#print axioms Collatz.Cycle.cycle_is_positive_periodic
#print axioms Collatz.Cycle.PB_eq_BB
#print axioms Collatz.Cycle.Pc_eq_cc
#print axioms Collatz.Cycle.T7_from_periodic
#print axioms Collatz.Pc_ones_1
#print axioms Collatz.Pc_ones_2
#print axioms Collatz.Pc_ones_3
#print axioms Collatz.Pc_ones_4
#print axioms Collatz.PB_ones_3
#print axioms Collatz.ones_three_equation
#print axioms Collatz.ones_witness
#print axioms Collatz.trivial_is_const_two
#print axioms Collatz.only_b_two
#print axioms Collatz.const_two_exists
#print axioms Collatz.cycle5_is_periodic
#print axioms Collatz.cycle7_is_periodic
