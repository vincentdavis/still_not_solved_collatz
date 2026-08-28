/-
  Collatz/Minimum.lean

  The *smallest* odd element of a cycle, and the mirror of T1–T3 at that end.

  WHY THIS FILE EXISTS.  Every theorem in `Collatz/Cycle.lean` constrains the
  maximum `M = y 0`, because `hmax` is a field of the structure.  A finite cycle
  has a smallest element too, and docs/CERTIFY.md derives an exact mirror image
  for it.  That mirror was for a long time the one result in the project with a
  recorded Lean blocker: "`Cycle` carries `hmax` but no `hmin`, so it needs a
  refactor of the structure".

  It does not.  The minimum is *derivable*.  `hper` makes `y` periodic, so the
  whole orbit is the finite list `y 1, …, y L`, and an index minimising `y` over
  that range can be computed by structural recursion — no choice principle, no
  new field, no change to any existing instance.  `argMinFrom` below is that
  computation; `Cycle.m` is the minimum it finds; `Cycle.m_le` is the proof that
  it really is one.

  THE HYPOTHESIS `q < m` IS LOAD-BEARING.  The step out of the minimum obeys
  `2 ^ b ≤ 3 + q / m`, which forces `b = 1` only once `q / m < 1`.  Drop it and
  the statement is false: 197 of the primitive cycles of length `≥ 2` in the
  project's `3n+q` census (`q < 600`) break it — the longest being `q = 541`,
  whose length-90 cycle has minimum `m = 25` and `3·25 + 541 = 616 = 2³ · 77`,
  three halvings out rather than one.  So `q < m` appears in the statement of
  every theorem here that needs it, exactly as `q < M` does for T2/T3/T4, and
  `Collatz/Examples.lean` carries three witnesses: `cycle17` fails it outright,
  `cycle37` fails it while *satisfying* `q < M` (so the mirror does not inherit
  the maximum's hypothesis), and `cycle7` fails it yet still satisfies the
  conclusion — the hypothesis is sufficient, not necessary.

  For `q = 1` it is free: any cycle with `m = 1` is the trivial one
  (`min_gt_one_q1`), so the `q = 1` theorems below ask only for `1 < M`.

  VACUITY, HONESTLY.  The `q = 1` statements are conditional on a `Cycle 1` with
  `M > 1`, and no such cycle is known — that is the Collatz conjecture.  They are
  not vacuous *as stated about `3n+q`*, which is why every general-`q` theorem
  here is instantiated on a real cycle in `Collatz/Examples.lean`; but the `q=1`
  corollaries have no witness, exactly as `Cycle.T3` has none.

  NOTE ON NAMES.  The structure field `Cycle.hmin` is NOT about the minimum —
  it says `L` counts *distinct* elements.  The genuine minimality statement is
  `Cycle.m_le`.

  Mathlib-free: Lean 4 core only.
-/
import Collatz.Cycle

namespace Collatz

/-! ## 1. A choice-free argmin

`argMinFrom f n` is an index in `[1, n+1]` at which `f` is least.  Structural
recursion on `n`, so it computes, and its axiom certificate stays clean. -/

/-- Index in `[1, n+1]` minimising `f`.  Ties go to the smaller index. -/
def argMinFrom (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | (n + 1) => if f (n + 2) < f (argMinFrom f n) then n + 2 else argMinFrom f n

theorem argMinFrom_pos (f : Nat → Nat) (n : Nat) : 1 ≤ argMinFrom f n := by
  induction n with
  | zero => simp [argMinFrom]
  | succ n ih =>
      simp only [argMinFrom]
      split
      · omega
      · exact ih

theorem argMinFrom_le (f : Nat → Nat) (n : Nat) : argMinFrom f n ≤ n + 1 := by
  induction n with
  | zero => simp [argMinFrom]
  | succ n ih =>
      simp only [argMinFrom]
      split
      · omega
      · omega

/-- **`argMinFrom` earns its name.** -/
theorem argMinFrom_min (f : Nat → Nat) (n : Nat) :
    ∀ i, 1 ≤ i → i ≤ n + 1 → f (argMinFrom f n) ≤ f i := by
  induction n with
  | zero =>
      intro i h1 h2
      have : i = 1 := by omega
      subst this
      simp [argMinFrom]
  | succ n ih =>
      intro i h1 h2
      rcases (show i ≤ n + 1 ∨ i = n + 2 by omega) with hle | heq
      · have hprev := ih i h1 hle
        simp only [argMinFrom]
        split
        · omega
        · exact hprev
      · subst heq
        simp only [argMinFrom]
        split
        · exact Nat.le_refl _
        · omega

namespace Cycle

variable {q : Nat} (C : Cycle q)

/-! ## 2. The orbit is finite: every index reduces into `[1, L]` -/

/-- Periodicity, iterated: `y (i + L·k) = y i`. -/
theorem y_add_mul (i k : Nat) : C.y (i + C.L * k) = C.y i := by
  induction k with
  | zero => simp
  | succ k ih =>
      have e : i + C.L * (k + 1) = (i + C.L * k) + C.L := by
        rw [Nat.mul_succ]; omega
      rw [e, C.hper, ih]

theorem y_mod (i : Nat) : C.y i = C.y (i % C.L) := by
  have e : i % C.L + C.L * (i / C.L) = i := Nat.mod_add_div i C.L
  calc C.y i = C.y (i % C.L + C.L * (i / C.L)) := by rw [e]
    _ = C.y (i % C.L) := C.y_add_mul _ _

/-- Every element of the orbit is listed among `y 1, …, y L`.  (Index `0` is
    covered because `y L = y 0`, which is what makes the search range `[1, L]`
    legitimate — and keeping `0` out of the range is what makes `minIdx ≥ 1`,
    so that `bb minIdx` is always a real backward hop.) -/
theorem exists_idx (i : Nat) : ∃ j, 1 ≤ j ∧ j ≤ C.L ∧ C.y j = C.y i := by
  have hL := C.hL
  rcases Nat.eq_zero_or_pos (i % C.L) with h0 | hpos
  · refine ⟨C.L, hL, Nat.le_refl _, ?_⟩
    have hLy : C.y C.L = C.y 0 := by have := C.hper 0; simpa using this
    rw [hLy, C.y_mod i, h0]
  · exact ⟨i % C.L, hpos, Nat.le_of_lt (Nat.mod_lt _ hL), (C.y_mod i).symm⟩

/-! ## 3. The minimum -/

/-- The index of the smallest element, searched over `[1, L]`. -/
def minIdx : Nat := argMinFrom C.y (C.L - 1)

/-- `m` — the smallest odd element of the cycle. -/
def m : Nat := C.y C.minIdx

theorem minIdx_pos : 1 ≤ C.minIdx := argMinFrom_pos _ _

theorem minIdx_le : C.minIdx ≤ C.L := by
  have h := argMinFrom_le C.y (C.L - 1)
  have := C.hL
  show argMinFrom C.y (C.L - 1) ≤ C.L
  omega

/-- **`m` is the minimum.**  This is the field the structure never had. -/
theorem m_le (i : Nat) : C.m ≤ C.y i := by
  obtain ⟨j, hj1, hjL, hje⟩ := C.exists_idx i
  have hL := C.hL
  show C.y C.minIdx ≤ C.y i
  rw [← hje]
  exact argMinFrom_min C.y (C.L - 1) j hj1 (by omega)

theorem m_odd : C.m % 2 = 1 := C.hodd _

theorem m_pos : 0 < C.m := C.y_pos _

theorem m_le_M : C.m ≤ C.M := C.hmax _

/-- The two ends bracket the whole orbit. -/
theorem m_le_y_le_M (i : Nat) : C.m ≤ C.y i ∧ C.y i ≤ C.M :=
  ⟨C.m_le i, C.hmax i⟩

/-! ## 4. The mirror

At the maximum the forward step must fall, which costs `≥ 2` halvings (T1) and
forces the hop *in* to be a single one (T2).  At the minimum the forward step
cannot fall, so it costs exactly one halving and the hop *in* costs `≥ 2`.
Everything below is that sentence, in `ℕ`. -/

/-- The hop out of the minimum, multiplicatively.  `bb minIdx` is the number of
    halvings on `y minIdx → y (minIdx − 1)`, i.e. the forward step out of `m`. -/
theorem m_step : 3 * C.m + q = 2 ^ C.bb C.minIdx * C.y (C.minIdx - 1) := by
  have h1 : C.minIdx - 1 + 1 = C.minIdx := by have := C.minIdx_pos; omega
  have h := C.bb_spec (C.minIdx - 1)
  rwa [h1] at h

theorem m_bb_pos : 1 ≤ C.bb C.minIdx := by
  have h1 : C.minIdx - 1 + 1 = C.minIdx := by have := C.minIdx_pos; omega
  have h := C.bb_pos (C.minIdx - 1)
  rwa [h1] at h

/-- **The mirror of T2.**  If `q < m` the forward step out of the minimum is a
    *single* halving.  Contrast T2, where the hop into the *maximum* is the
    single one: the two ends are exact opposites. -/
theorem min_bb_out (hqm : q < C.m) : C.bb C.minIdx = 1 := by
  have hstep := C.m_step
  have hlow : C.m ≤ C.y (C.minIdx - 1) := C.m_le _
  have hb1 := C.m_bb_pos
  rcases Nat.lt_or_ge (C.bb C.minIdx) 2 with h | h
  · omega
  · exfalso
    have h4 : (4 : Nat) ≤ 2 ^ C.bb C.minIdx := by
      have h' := two_pow_le h
      have e : (2 : Nat) ^ 2 = 4 := by decide
      omega
    have hmul : 4 * C.m ≤ 2 ^ C.bb C.minIdx * C.y (C.minIdx - 1) :=
      Nat.mul_le_mul h4 hlow
    omega

/-- The hop out of the minimum, unpacked: `3m + q = 2 · (the next element)`. -/
theorem m_step_one (hqm : q < C.m) : 3 * C.m + q = 2 * C.y (C.minIdx - 1) := by
  have h := C.m_step
  rw [C.min_bb_out hqm] at h
  have e : (2 : Nat) ^ 1 = 2 := by decide
  rwa [e] at h

/-- **The mirror of T1.**  T1 says `3M + q ≡ 0 (mod 4)`.  At the other end
    `3m + q ≡ 2 (mod 4)` — the *same* expression, in the other even class. -/
theorem min_mod4 (hqm : q < C.m) : (3 * C.m + q) % 4 = 2 := by
  have h := C.m_step_one hqm
  have hodd := C.hodd (C.minIdx - 1)
  omega

/-- **The mirror of `T1_mod4`.**  `T1_mod4` gives `M ≡ q (mod 4)`; here
    `m ≡ q + 2 (mod 4)`.  So the two ends of a cycle sit in *different* classes
    mod 4, exactly two apart, for every `q`. -/
theorem min_mod4' (hqm : q < C.m) : C.m % 4 = (q + 2) % 4 := by
  have h := C.min_mod4 hqm
  have hm := C.m_odd
  have hq := C.hq_odd
  omega

/-- **The mirror of T2's `a ≥ 2`.**  The backward hop *into* the minimum needs
    at least two halvings.  Needs no size hypothesis at all. -/
theorem min_bb_in : 2 ≤ C.bb (C.minIdx + 1) := by
  have h := C.bb_spec C.minIdx
  have hge : C.m ≤ C.y (C.minIdx + 1) := C.m_le _
  have hq := C.hq_pos
  have hm := C.m_pos
  rcases Nat.lt_or_ge (C.bb (C.minIdx + 1)) 2 with hlt | hge2
  · exfalso
    have hb1 : 1 ≤ C.bb (C.minIdx + 1) := C.bb_pos C.minIdx
    have hb : C.bb (C.minIdx + 1) = 1 := by omega
    rw [hb] at h
    have e : (2 : Nat) ^ 1 = 2 := by decide
    rw [e] at h
    show False
    unfold m at hge hm
    omega
  · exact hge2

/-- `3 ∤ m` — T0 at the other end. -/
theorem min_not_three : C.m % 3 ≠ 0 := C.T0 _

/-! ## 5. `q = 1` -/

/-- For `q = 1` the hypothesis `q < m` is not an extra assumption: a cycle whose
    minimum is `1` has `M = 1`, so it is the trivial cycle.  (`S 1 1 = 1`, and
    the minimum's forward image is `≥ m` while everything is `≤ M`.) -/
theorem min_gt_one_q1 (C : Cycle 1) (hM : 1 < C.M) : 1 < C.m := by
  rcases Nat.lt_or_ge 1 C.m with h | h
  · exact h
  · exfalso
    have hpos := C.m_pos
    have hy : C.y C.minIdx = 1 := by
      have h1 : C.m = 1 := by omega
      exact h1
    have h11 : S 1 (1 : Nat) = 1 := by simp [S, oddPart]
    -- `S 1` fixes 1, and each forward step drops the index by one, so the value
    -- 1 propagates from `minIdx` all the way down to index 0.
    have key : ∀ k, k ≤ C.minIdx → C.y (C.minIdx - k) = 1 := by
      intro k
      induction k with
      | zero => intro _; simpa using hy
      | succ k ih =>
          intro hk
          have hprev := ih (by omega)
          have e : C.minIdx - k = (C.minIdx - (k + 1)) + 1 := by omega
          have hs := C.hstep (C.minIdx - (k + 1))
          rw [← e, hprev, h11] at hs
          exact hs.symm
    have h0 := key C.minIdx (Nat.le_refl _)
    have e0 : C.minIdx - C.minIdx = 0 := by omega
    rw [e0] at h0
    have hM1 : C.M = 1 := h0
    omega

/-- **The mirror of T1, `q = 1`:** `m ≡ 3 (mod 4)`.  The maximum is
    `≡ 1 (mod 4)` (`T1_q1`), so the two ends never share a class mod 4. -/
theorem min_mod4_q1 (C : Cycle 1) (hM : 1 < C.M) : C.m % 4 = 3 := by
  have h := C.min_mod4 (C.min_gt_one_q1 hM)
  have hm := C.m_odd
  omega

/-- **The mirror of T3, `q = 1`:** `m ≡ 7 or 11 (mod 12)`.
    Against the maximum's `M ≡ 5 (mod 12)` (`T3`): the two ends of a Collatz
    cycle occupy *disjoint* residue classes mod 12. -/
theorem min_mod12_q1 (C : Cycle 1) (hM : 1 < C.M) :
    C.m % 12 = 7 ∨ C.m % 12 = 11 := by
  have h4 := C.min_mod4_q1 hM
  have h3 := C.min_not_three
  omega

/-- **The two ends are disjoint mod 12** — stated as one theorem, since that is
    the claim docs/CERTIFY.md actually makes. -/
theorem ends_disjoint_q1 (C : Cycle 1) (hM : 1 < C.M) :
    C.M % 12 = 5 ∧ (C.m % 12 = 7 ∨ C.m % 12 = 11) :=
  ⟨C.T3 hM, C.min_mod12_q1 hM⟩

end Cycle

end Collatz
