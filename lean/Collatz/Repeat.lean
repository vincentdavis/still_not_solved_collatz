/-
  Collatz/Repeat.lean

  THE REPEAT THEOREM (docs/BALANCE.md section 6, Lemmas 13-14 and Theorem 4),
  in whole numbers.

  WHAT IS PROVED.  Take a cycle of `3n + q` and suppose the same stretch of
  halving counts occurs at two different places of it: `j` consecutive steps
  with `X` halvings in total.  Then

    1. `Cycle.repeat_identity`      3^j (n_a - n_b) = 2^X (n_a' - n_b'),
       where `n_a, n_b` are the members at which the two copies start and
       `n_a', n_b'` the members at which they end;
    2. `Cycle.repeat_split`         the two differences share one cofactor:
       `n_a - n_b = 2^X t` and `n_a' - n_b' = 3^j t`;
    3. `Cycle.repeat_gap_M`         `M - m >= 2^(X+1)` and `M - m >= 2 * 3^j`;
    4. `Cycle.max_pow_le`           the largest member is at most
       `(a/b) * 2^(D/L)`, for any fraction `a/b` that passes the size test
       and any `D` bounding how far the largest member sits above the lowest
       level of the staircase;
    5. `Cycle.repeat_bound`, `Cycle.repeat_theorem`
                                    hence `(X + 1) * L < N * L + D`,
       that is `X + 1 < N + D/L`;
    6. `Cycle.repeat_unique`        so a stretch with `X + 1 >= N + s`
       halvings occurs at one place only, and
       `Cycle.bb_period`            the halving pattern has no period shorter
       than `L`.

  HOW THIS MATCHES THE WRITTEN THEOREM.  docs/BALANCE.md states Theorem 4 as
  `X < sigma + tau - 1` with two real numbers:

      tau   = -log2 (2^(B/L) - 3)          the size exponent,
      sigma = (max level - min level) / L  the height spread.

  Lean 4 core has no real numbers, so both enter through whole-number
  certificates, exactly as `log2 3` enters `Collatz/Halving.lean`:

      N >= tau        <=>   (3 * 2^N + 1)^L <= 2^(N L + B)      (`hN`)
      D/L <= sigma    <==   k B <= L B_k + D  for 1 <= k <= L   (`hD`)

  `B_k` is the number of halvings on the `k` steps that lead up to the largest
  member, so `k B - L B_k` is how far the largest member sits above the member
  `k` steps before it, in the level units of docs/BALANCE.md.  `hD` therefore
  asks only for the height of the LARGEST member above the lowest level, which
  is at most the full spread `sigma L`.  The Lean statement is the local form
  of Theorem 4 and implies it.

  NOTHING IS LOST BY CLEARING DENOMINATORS.  `repeat_bound` takes the size
  threshold as an arbitrary fraction `a/b >= 1/(2^(B/L) - 3)`, certified by
  `(3a + qb)^L <= a^L 2^B`.  Letting `a/b` decrease to the threshold recovers
  the real statement `M <= 2^(tau + D/L)`; the family of whole-number
  statements is equivalent to the real one, not a weakening of it.

  WHAT IS NOT HERE.  The two Diophantine inputs that bound `tau` from above
  (Ellison 1971, Rhin 1987) are cited, not formalized.  The word combinatorics
  that turns "few moved corners" into "some stretch repeats" (Lemma 15 and
  Corollaries 16-18 of docs/BALANCE.md) is checked in Python, not here.
  Theorems 1-3 of docs/BALANCE.md need the number field `Q(2^(1/L))` and are
  out of reach without Mathlib.

  THE PROOF OF `max_pow_le` DIFFERS FROM THE WRITTEN ONE.  docs/BALANCE.md
  proves Lemma 14 by summing a geometric series with ratio `2^(B/L)/3`, a real
  number.  Here the sum is replaced by a walk: go backwards from the largest
  member until the first member that is `<= a/b`.  Every member passed on the
  way is `> a/b`, so each step multiplies by less than `2^(B/L)`, and the
  first member below the threshold costs at most `(3a + qb)/b`.  That is an
  induction on whole numbers (`max_chain`).

  NOVELTY: none is claimed for the ingredients.  The identity is the Syracuse
  form of the Terras (1976) / Everett (1977) periodicity theorem; the size
  bound is Crandall (1978) / Eliahou (1993), and Belaga (2003) for `3x + d`.
  Whether the combination is new is discussed, with hedges, in
  docs/BALANCE.md section 9.

  Mathlib-free: Lean 4 core only.  Valid for every `q`, not only `q = 1`.
-/
import Collatz.Length

namespace Collatz

/-! ## 1. Two coprime powers split a common cofactor

`3 ^ j * u = 2 ^ X * s` forces `u = 2 ^ X * t` and `s = 3 ^ j * t`.  This is
Euclid's lemma for the pair `(2 ^ X, 3 ^ j)`, proved by two plain inductions so
that no `gcd` is needed. -/

/-- One factor of three: `3 * u = 2 ^ X * s` gives `u = 2 ^ X * t`, `s = 3 * t`. -/
theorem three_mul_split : ∀ (X : Nat) {u s : Nat}, 3 * u = 2 ^ X * s →
    ∃ t, u = 2 ^ X * t ∧ s = 3 * t := by
  intro X
  induction X with
  | zero =>
      intro u s h
      refine ⟨u, by simp, ?_⟩
      rw [Nat.pow_zero, Nat.one_mul] at h
      exact h.symm
  | succ X ih =>
      intro u s h
      have e : 2 ^ (X + 1) * s = 2 * (2 ^ X * s) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ X) 2, Nat.mul_assoc]
      rw [e] at h
      obtain ⟨u', hu'⟩ : ∃ u', u = 2 * u' := ⟨u / 2, by omega⟩
      subst hu'
      have h' : 3 * u' = 2 ^ X * s := by omega
      obtain ⟨t, ht1, ht2⟩ := ih h'
      refine ⟨t, ?_, ht2⟩
      rw [ht1, Nat.pow_succ, Nat.mul_comm (2 ^ X) 2, Nat.mul_assoc]

/-- **Coprime split.**  `3 ^ j * u = 2 ^ X * s` gives one `t` with
    `u = 2 ^ X * t` and `s = 3 ^ j * t`. -/
theorem coprime_split (X : Nat) : ∀ (j : Nat) {u s : Nat}, 3 ^ j * u = 2 ^ X * s →
    ∃ t, u = 2 ^ X * t ∧ s = 3 ^ j * t := by
  intro j
  induction j with
  | zero =>
      intro u s h
      rw [Nat.pow_zero, Nat.one_mul] at h
      exact ⟨s, h, by simp⟩
  | succ j ih =>
      intro u s h
      have e : 3 ^ (j + 1) * u = 3 * (3 ^ j * u) := by
        rw [Nat.pow_succ, Nat.mul_comm (3 ^ j) 3, Nat.mul_assoc]
      rw [e] at h
      obtain ⟨t₁, h1, h2⟩ := three_mul_split X h
      obtain ⟨t, h3, h4⟩ := ih h1
      refine ⟨t, h3, ?_⟩
      rw [h2, h4, Nat.pow_succ, Nat.mul_comm (3 ^ j) 3, Nat.mul_assoc]

/-- Powers of three are odd. -/
theorem three_pow_odd : ∀ j : Nat, 3 ^ j % 2 = 1 := by
  intro j
  induction j with
  | zero => decide
  | succ j ih => rw [Nat.pow_succ]; omega

/-! ## 2. The size test

`(3a + qb) ^ L ≤ a ^ L * E` with `E = 2 ^ B` says `3 + q b / a ≤ 2 ^ (B/L)`,
i.e. the fraction `a / b` is at least `q / (2 ^ (B/L) − 3)`.  Members above the
threshold multiply by less than `2 ^ (B/L)` per step; a member whose own step
multiplies by at least `2 ^ (B/L)` lies below it. -/

/-- A fraction that passes the size test has a positive numerator. -/
theorem size_pos {q a b L E : Nat} (hq : 0 < q) (hb : 0 < b)
    (hK : (3 * a + q * b) ^ L ≤ a ^ L * E) (hL : 0 < L) : 0 < a := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · exfalso
    subst h0
    have hqb : 0 < q * b := Nat.mul_pos hq hb
    have hp : 0 < (3 * 0 + q * b) ^ L := Nat.pow_pos (by omega)
    have hz : (0 : Nat) ^ L = 0 := by
      obtain ⟨n, hn⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
      rw [hn, Nat.pow_succ, Nat.mul_zero]
    rw [hz, Nat.zero_mul] at hK
    omega
  · exact hpos

/-- **Above the threshold a step multiplies by at most `2 ^ (B/L)`.**
    If `a / b` passes the size test and `a / b ≤ n`, then `n` passes it too. -/
theorem size_mono {q a b n L E : Nat} (ha : 0 < a)
    (hK : (3 * a + q * b) ^ L ≤ a ^ L * E) (hn : a ≤ b * n) :
    (3 * n + q) ^ L ≤ n ^ L * E := by
  have step : (3 * n + q) * a ≤ (3 * a + q * b) * n := by
    have e1 : (3 * n + q) * a = 3 * (n * a) + q * a := by
      simp [Nat.add_mul, Nat.mul_assoc]
    have e2 : (3 * a + q * b) * n = 3 * (n * a) + q * (b * n) := by
      simp [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm a n]
    have e3 : q * a ≤ q * (b * n) := Nat.mul_le_mul_left q hn
    omega
  have p := Nat.pow_le_pow_left step L
  rw [Nat.mul_pow, Nat.mul_pow] at p
  have h2 : (3 * a + q * b) ^ L * n ^ L ≤ a ^ L * E * n ^ L :=
    Nat.mul_le_mul_right _ hK
  have goal : a ^ L * ((3 * n + q) ^ L) ≤ a ^ L * (n ^ L * E) := by
    have x : a ^ L * ((3 * n + q) ^ L) = (3 * n + q) ^ L * a ^ L := Nat.mul_comm _ _
    have y : a ^ L * (n ^ L * E) = a ^ L * E * n ^ L := by
      rw [Nat.mul_assoc, Nat.mul_comm E]
    omega
  exact Nat.le_of_mul_le_mul_left goal (Nat.pow_pos ha)

/-- **A member whose step multiplies by at least `2 ^ (B/L)` is below the
    threshold.**  If `n ^ L * E ≤ (3n + q) ^ L` then `n ≤ a / b`. -/
theorem le_of_size {q a b n L E : Nat} (hq : 0 < q) (hL : 0 < L)
    (hK : (3 * a + q * b) ^ L ≤ a ^ L * E)
    (hn : n ^ L * E ≤ (3 * n + q) ^ L) : b * n ≤ a := by
  rcases Nat.lt_or_ge a (b * n) with hlt | hge
  · exfalso
    have step : (3 * n + q) * a < (3 * a + q * b) * n := by
      have e1 : (3 * n + q) * a = 3 * (n * a) + q * a := by
        simp [Nat.add_mul, Nat.mul_assoc]
      have e2 : (3 * a + q * b) * n = 3 * (n * a) + q * (b * n) := by
        simp [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm a n]
      have e3 : q * a < q * (b * n) :=
        Nat.mul_lt_mul_of_le_of_lt (Nat.le_refl q) hlt hq
      omega
    have p := Nat.pow_lt_pow_left step (by omega : L ≠ 0)
    rw [Nat.mul_pow, Nat.mul_pow] at p
    have h2 : (3 * a + q * b) ^ L * n ^ L ≤ a ^ L * E * n ^ L :=
      Nat.mul_le_mul_right _ hK
    have h3 : n ^ L * E * a ^ L ≤ (3 * n + q) ^ L * a ^ L :=
      Nat.mul_le_mul_right _ hn
    have y : n ^ L * E * a ^ L = a ^ L * E * n ^ L := by
      rw [Nat.mul_comm (n ^ L * E), Nat.mul_assoc, Nat.mul_comm E]
    omega
  · exact hge

namespace Cycle

variable {q : Nat} (C : Cycle q)

/-! ## 3. Windows of halving counts

Recall the convention of `Collatz/Cycle.lean`: `y 0 = M` and `y (k+1)` is the
member *before* `y k`, with `3 * y (k+1) + q = 2 ^ bb (k+1) * y k`.  So the `j`
forward steps from `y (p+j)` to `y p` use the halving counts
`bb (p+j), …, bb (p+1)`. -/

/-- `window p j = bb (p+1) + … + bb (p+j)`: the halvings on the `j` steps that
    lead from `y (p+j)` to `y p`. -/
def window (C : Cycle q) (p : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => C.window p j + C.bb (p + j + 1)

/-- The windows that end at the maximum are the partial sums `B_k`. -/
theorem window_zero_left : ∀ k, C.window 0 k = C.BB k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      show C.window 0 k + C.bb (0 + k + 1) = C.BB k + C.bb (k + 1)
      rw [ih, Nat.zero_add]

/-- Equal stretches have equal weight. -/
theorem window_congr {p r : Nat} : ∀ j,
    (∀ i, i < j → C.bb (p + i + 1) = C.bb (r + i + 1)) →
    C.window p j = C.window r j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro h
      show C.window p j + C.bb (p + j + 1) = C.window r j + C.bb (r + j + 1)
      rw [ih (fun i hi => h i (by omega)), h j (by omega)]

/-- Every step halves at least once, so `j` steps weigh at least `j`. -/
theorem le_window (p : Nat) : ∀ j, j ≤ C.window p j := by
  intro j
  induction j with
  | zero => exact Nat.le_refl 0
  | succ j ih =>
      have hb := C.bb_pos (p + j)
      show j + 1 ≤ C.window p j + C.bb (p + j + 1)
      omega

/-! ## 4. The repeat identity (Lemma 13 of docs/BALANCE.md) -/

/-- **The repeat identity.**  If the `j` halving counts below `p` equal the `j`
    halving counts below `r`, with `X = window p j` halvings in total, then

        3 ^ j * (y (p+j) − y (r+j))  =  2 ^ X * (y p − y r) ,

    written here without subtraction.  `q` cancels: the identity holds for
    every `3n + q`. -/
theorem repeat_identity {p r : Nat} : ∀ j,
    (∀ i, i < j → C.bb (p + i + 1) = C.bb (r + i + 1)) →
    3 ^ j * C.y (p + j) + 2 ^ C.window p j * C.y r
      = 3 ^ j * C.y (r + j) + 2 ^ C.window p j * C.y p := by
  intro j
  induction j with
  | zero =>
      intro _
      show 3 ^ 0 * C.y p + 2 ^ 0 * C.y r = 3 ^ 0 * C.y r + 2 ^ 0 * C.y p
      omega
  | succ j ih =>
      intro h
      have hj := ih (fun i hi => h i (by omega))
      have hb : C.bb (p + j + 1) = C.bb (r + j + 1) := h j (by omega)
      have sp := C.bb_spec (p + j)
      have sr := C.bb_spec (r + j)
      rw [← hb] at sr
      show 3 ^ (j + 1) * C.y (p + j + 1)
            + 2 ^ (C.window p j + C.bb (p + j + 1)) * C.y r
         = 3 ^ (j + 1) * C.y (r + j + 1)
            + 2 ^ (C.window p j + C.bb (p + j + 1)) * C.y p
      -- the step relations, multiplied by `3 ^ j`
      have a1 : 3 ^ (j + 1) * C.y (p + j + 1) + 3 ^ j * q
              = 2 ^ C.bb (p + j + 1) * (3 ^ j * C.y (p + j)) := by
        rw [Nat.pow_succ, Nat.mul_assoc, ← Nat.mul_add, sp, Nat.mul_left_comm]
      have a2 : 3 ^ (j + 1) * C.y (r + j + 1) + 3 ^ j * q
              = 2 ^ C.bb (p + j + 1) * (3 ^ j * C.y (r + j)) := by
        rw [Nat.pow_succ, Nat.mul_assoc, ← Nat.mul_add, sr, Nat.mul_left_comm]
      -- the induction hypothesis, multiplied by `2 ^ b`
      have a3 : 2 ^ C.bb (p + j + 1) * (3 ^ j * C.y (p + j))
                + 2 ^ (C.window p j + C.bb (p + j + 1)) * C.y r
              = 2 ^ C.bb (p + j + 1) * (3 ^ j * C.y (r + j))
                + 2 ^ (C.window p j + C.bb (p + j + 1)) * C.y p := by
        have e : ∀ z, 2 ^ (C.window p j + C.bb (p + j + 1)) * z
                    = 2 ^ C.bb (p + j + 1) * (2 ^ C.window p j * z) := by
          intro z
          rw [Nat.pow_add, Nat.mul_comm (2 ^ C.window p j), Nat.mul_assoc]
        rw [e, e, ← Nat.mul_add, ← Nat.mul_add, hj]
      omega

/-- **The repeat identity, split.**  The two differences share one cofactor:
    with `X = window p j`, and the copies ordered so that
    `y (r+j) ≤ y (p+j)`,

        y (p+j) = y (r+j) + 2 ^ X * t      and      y p = y r + 3 ^ j * t . -/
theorem repeat_split {p r j : Nat}
    (hagree : ∀ i, i < j → C.bb (p + i + 1) = C.bb (r + i + 1))
    (hle : C.y (r + j) ≤ C.y (p + j)) :
    ∃ t, C.y (p + j) = C.y (r + j) + 2 ^ C.window p j * t
       ∧ C.y p = C.y r + 3 ^ j * t := by
  have h := C.repeat_identity j hagree
  obtain ⟨u, hu⟩ : ∃ u, C.y (p + j) = C.y (r + j) + u :=
    ⟨C.y (p + j) - C.y (r + j), by omega⟩
  rw [hu, Nat.mul_add] at h
  have hdc : 2 ^ C.window p j * C.y r ≤ 2 ^ C.window p j * C.y p := by omega
  have hle' : C.y r ≤ C.y p :=
    Nat.le_of_mul_le_mul_left hdc (Nat.pow_pos (by decide))
  obtain ⟨s, hs⟩ : ∃ s, C.y p = C.y r + s := ⟨C.y p - C.y r, by omega⟩
  rw [hs, Nat.mul_add] at h
  have hus : 3 ^ j * u = 2 ^ C.window p j * s := by omega
  obtain ⟨t, ht1, ht2⟩ := coprime_split (C.window p j) j hus
  exact ⟨t, by rw [hu, ht1], by rw [hs, ht2]⟩

/-! ## 5. Different places carry different members -/

/-- Two positions that differ modulo `L` carry two different members. -/
theorem y_ne_of_mod_ne {p r : Nat} (h : p % C.L ≠ r % C.L) : C.y p ≠ C.y r := by
  rw [C.y_mod p, C.y_mod r]
  have hp := Nat.mod_lt p C.hL
  have hr := Nat.mod_lt r C.hL
  rcases Nat.lt_or_gt_of_ne h with hlt | hgt
  · exact C.y_ne_of_lt hlt hr
  · exact (C.y_ne_of_lt hgt hp).symm

/-! ## 6. A repeat forces members apart -/

/-- **Lemma 13, ordered form.**  If the same stretch (`j` steps, `X` halvings)
    occurs at two different places, the two members it starts from differ by at
    least `2 ^ (X+1)`, and the two members it ends at by at least `2 * 3 ^ j`. -/
theorem repeat_gap {p r j : Nat}
    (hpr : p % C.L ≠ r % C.L)
    (hagree : ∀ i, i < j → C.bb (p + i + 1) = C.bb (r + i + 1))
    (hle : C.y (r + j) ≤ C.y (p + j)) :
    C.y (r + j) + 2 ^ (C.window p j + 1) ≤ C.y (p + j)
      ∧ C.y r + 2 * 3 ^ j ≤ C.y p := by
  obtain ⟨t, h1, h2⟩ := C.repeat_split hagree hle
  have hne : C.y p ≠ C.y r := C.y_ne_of_mod_ne hpr
  have hp := C.hodd p
  have hr := C.hodd r
  -- `t` is even, because `3 ^ j` is odd and both members are odd
  have hm : (3 ^ j * t) % 2 = t % 2 := by
    rw [Nat.mul_mod, three_pow_odd j, Nat.one_mul, Nat.mod_mod]
  have ht2 : 2 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · exfalso
      rw [h0, Nat.mul_zero, Nat.add_zero] at h2
      exact hne h2
    · omega
  have g1 : 2 ^ (C.window p j + 1) ≤ 2 ^ C.window p j * t := by
    rw [Nat.pow_succ]
    exact Nat.mul_le_mul_left _ ht2
  have g2 : 2 * 3 ^ j ≤ 3 ^ j * t := by
    rw [Nat.mul_comm 2]
    exact Nat.mul_le_mul_left _ ht2
  exact ⟨by omega, by omega⟩

/-- **Lemma 13.**  A stretch of `j` steps and `X` halvings that occurs at two
    different places of a cycle forces

        M − m ≥ 2 ^ (X+1)        and        M − m ≥ 2 · 3 ^ j . -/
theorem repeat_gap_M {p r j : Nat}
    (hpr : p % C.L ≠ r % C.L)
    (hagree : ∀ i, i < j → C.bb (p + i + 1) = C.bb (r + i + 1)) :
    C.m + 2 ^ (C.window p j + 1) ≤ C.M ∧ C.m + 2 * 3 ^ j ≤ C.M := by
  have hM1 : C.y (p + j) ≤ C.M := C.hmax _
  have hM2 : C.y (r + j) ≤ C.M := C.hmax _
  have hM3 : C.y p ≤ C.M := C.hmax _
  have hM4 : C.y r ≤ C.M := C.hmax _
  have hm1 := C.m_le (p + j)
  have hm2 := C.m_le (r + j)
  have hm3 := C.m_le p
  have hm4 := C.m_le r
  rcases Nat.le_total (C.y (r + j)) (C.y (p + j)) with hle | hle
  · obtain ⟨g1, g2⟩ := C.repeat_gap hpr hagree hle
    exact ⟨by omega, by omega⟩
  · have hagree' : ∀ i, i < j → C.bb (r + i + 1) = C.bb (p + i + 1) :=
      fun i hi => (hagree i hi).symm
    obtain ⟨g1, g2⟩ := C.repeat_gap (fun e => hpr e.symm) hagree' hle
    rw [← C.window_congr j hagree] at g1
    exact ⟨by omega, by omega⟩

/-- **Terras–Everett, Syracuse form.**  A stretch with `2 ^ (X+1) ≥ M` occurs
    at most once in a cycle. -/
theorem repeat_lt_M {p r j : Nat}
    (hpr : p % C.L ≠ r % C.L)
    (hagree : ∀ i, i < j → C.bb (p + i + 1) = C.bb (r + i + 1)) :
    2 ^ (C.window p j + 1) < C.M := by
  have h := (C.repeat_gap_M hpr hagree).1
  have hm := C.m_pos
  omega

/-- **The halving pattern of a cycle has no shorter period.**  If the halving
    counts are unchanged by a shift of `d` places, then `L` divides `d`.

    Otherwise the whole pattern would occur at two different places, as a
    stretch of any length, and `repeat_lt_M` with a stretch of `M` steps gives
    `2 ^ (M+1) < M`.  In the words of docs/BALANCE.md: the halving word of a
    cycle with `L` distinct odd members is primitive.  (Classical.) -/
theorem bb_period {d : Nat} (h : ∀ i, C.bb (i + 1) = C.bb (d + i + 1)) :
    d % C.L = 0 := by
  rcases Nat.eq_zero_or_pos (d % C.L) with h0 | hpos
  · exact h0
  · exfalso
    have hpr : 0 % C.L ≠ d % C.L := by rw [Nat.zero_mod]; omega
    have hagree : ∀ i, i < C.M → C.bb (0 + i + 1) = C.bb (d + i + 1) := by
      intro i _
      rw [Nat.zero_add]
      exact h i
    have hlt := C.repeat_lt_M hpr hagree
    have hw := C.le_window 0 C.M
    have h2 : C.M < 2 ^ C.M := Nat.lt_two_pow_self
    have h3 : 2 ^ C.M ≤ 2 ^ (C.window 0 C.M + 1) := two_pow_le (by omega)
    omega

/-! ## 7. The size of the members (Lemma 14 of docs/BALANCE.md) -/

/-- **The smallest member is below the threshold** (Crandall / Eliahou; Belaga
    for general `q`): `m ≤ a / b` for every fraction that passes the size test. -/
theorem m_le_of_size {a b : Nat}
    (hK : (3 * a + q * b) ^ C.L ≤ a ^ C.L * 2 ^ C.BB C.L) : b * C.m ≤ a :=
  le_of_size C.hq_pos C.hL hK C.pow_le_m

/-- **The walk back from the maximum.**  After `k` backward steps, either some
    earlier member `y k'` was at most `a / b`, and then

        (b M) ^ L · 2 ^ (L · B_{k'})  ≤  a ^ L · 2 ^ (k' · B) ,

    or every member met so far exceeds `a / b`, and then

        M ^ L · 2 ^ (L · B_k)  ≤  y_k ^ L · 2 ^ (k · B) . -/
theorem max_chain {a b : Nat} (hb : 0 < b)
    (hK : (3 * a + q * b) ^ C.L ≤ a ^ C.L * 2 ^ C.BB C.L) :
    ∀ k,
      (∃ k', 1 ≤ k' ∧ k' ≤ k ∧
        b ^ C.L * C.M ^ C.L * 2 ^ (C.L * C.BB k') ≤ a ^ C.L * 2 ^ (k' * C.BB C.L))
      ∨ ((∀ i, 1 ≤ i → i ≤ k → a < b * C.y i) ∧
          C.M ^ C.L * 2 ^ (C.L * C.BB k) ≤ C.y k ^ C.L * 2 ^ (k * C.BB C.L)) := by
  have ha : 0 < a := size_pos C.hq_pos hb hK C.hL
  intro k
  induction k with
  | zero =>
      refine Or.inr ⟨fun i h1 h2 => by omega, ?_⟩
      show C.y 0 ^ C.L * 2 ^ (C.L * 0) ≤ C.y 0 ^ C.L * 2 ^ (0 * C.BB C.L)
      rw [Nat.mul_zero, Nat.zero_mul]
      exact Nat.le_refl _
  | succ k ih =>
      rcases ih with ⟨k', h1, h2, h3⟩ | ⟨hall, hch⟩
      · exact Or.inl ⟨k', h1, by omega, h3⟩
      · have sp := C.bb_spec k
        -- one more step back: `M^L 2^(L B_(k+1)) ≤ (3 y_(k+1) + q)^L 2^(k B)`
        have step : C.M ^ C.L * 2 ^ (C.L * C.BB (k + 1))
                  ≤ (3 * C.y (k + 1) + q) ^ C.L * 2 ^ (k * C.BB C.L) := by
          have e1 : C.M ^ C.L * 2 ^ (C.L * C.BB (k + 1))
                  = (C.M ^ C.L * 2 ^ (C.L * C.BB k)) * (2 ^ C.bb (k + 1)) ^ C.L := by
            show C.M ^ C.L * 2 ^ (C.L * (C.BB k + C.bb (k + 1)))
               = (C.M ^ C.L * 2 ^ (C.L * C.BB k)) * (2 ^ C.bb (k + 1)) ^ C.L
            rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm C.L (C.bb (k + 1)),
                Nat.pow_mul 2 (C.bb (k + 1)) C.L, Nat.mul_assoc]
          have e2 : (3 * C.y (k + 1) + q) ^ C.L * 2 ^ (k * C.BB C.L)
                  = (C.y k ^ C.L * 2 ^ (k * C.BB C.L)) * (2 ^ C.bb (k + 1)) ^ C.L := by
            rw [sp, Nat.mul_pow]
            simp [Nat.mul_comm, Nat.mul_left_comm]
          rw [e1, e2]
          exact Nat.mul_le_mul_right _ hch
        have eB : 2 ^ ((k + 1) * C.BB C.L) = 2 ^ C.BB C.L * 2 ^ (k * C.BB C.L) := by
          rw [Nat.succ_mul, Nat.pow_add, Nat.mul_comm]
        rcases Nat.lt_or_ge a (b * C.y (k + 1)) with hbig | hsmall
        · -- still above the threshold: this step multiplies by at most `2^(B/L)`
          refine Or.inr ⟨?_, ?_⟩
          · intro i h1 h2
            rcases (show i ≤ k ∨ i = k + 1 by omega) with hi | hi
            · exact hall i h1 hi
            · rw [hi]; exact hbig
          · have hm := size_mono ha hK (Nat.le_of_lt hbig)
            calc C.M ^ C.L * 2 ^ (C.L * C.BB (k + 1))
                ≤ (3 * C.y (k + 1) + q) ^ C.L * 2 ^ (k * C.BB C.L) := step
              _ ≤ (C.y (k + 1) ^ C.L * 2 ^ C.BB C.L) * 2 ^ (k * C.BB C.L) :=
                  Nat.mul_le_mul_right _ hm
              _ = C.y (k + 1) ^ C.L * 2 ^ ((k + 1) * C.BB C.L) := by
                  rw [eB, Nat.mul_assoc]
        · -- first member at or below the threshold: stop here
          refine Or.inl ⟨k + 1, by omega, Nat.le_refl _, ?_⟩
          have hz : b * (3 * C.y (k + 1) + q) ≤ 3 * a + q * b := by
            have e : b * (3 * C.y (k + 1) + q) = 3 * (b * C.y (k + 1)) + q * b := by
              rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm b q]
            omega
          have hzp := Nat.pow_le_pow_left hz C.L
          rw [Nat.mul_pow] at hzp
          calc b ^ C.L * C.M ^ C.L * 2 ^ (C.L * C.BB (k + 1))
              = b ^ C.L * (C.M ^ C.L * 2 ^ (C.L * C.BB (k + 1))) := Nat.mul_assoc _ _ _
            _ ≤ b ^ C.L * ((3 * C.y (k + 1) + q) ^ C.L * 2 ^ (k * C.BB C.L)) :=
                Nat.mul_le_mul_left _ step
            _ = (b ^ C.L * (3 * C.y (k + 1) + q) ^ C.L) * 2 ^ (k * C.BB C.L) :=
                (Nat.mul_assoc _ _ _).symm
            _ ≤ (3 * a + q * b) ^ C.L * 2 ^ (k * C.BB C.L) :=
                Nat.mul_le_mul_right _ hzp
            _ ≤ (a ^ C.L * 2 ^ C.BB C.L) * 2 ^ (k * C.BB C.L) :=
                Nat.mul_le_mul_right _ hK
            _ = a ^ C.L * 2 ^ ((k + 1) * C.BB C.L) := by
                rw [eB, Nat.mul_assoc]

/-- **Lemma 14, upper half, for the largest member.**

    Let `a / b` pass the size test, and let `D` bound how far the largest
    member sits above every other member in level units:
    `k · B ≤ L · B_k + D` for `1 ≤ k ≤ L`.  Then

        (b · M) ^ L  ≤  a ^ L · 2 ^ D ,      i.e.   M ≤ (a/b) · 2 ^ (D/L) . -/
theorem max_pow_le {a b D : Nat} (hb : 0 < b)
    (hK : (3 * a + q * b) ^ C.L ≤ a ^ C.L * 2 ^ C.BB C.L)
    (hD : ∀ k, 1 ≤ k → k ≤ C.L → k * C.BB C.L ≤ C.L * C.BB k + D) :
    (b * C.M) ^ C.L ≤ a ^ C.L * 2 ^ D := by
  rcases C.max_chain hb hK C.L with ⟨k', h1, h2, h3⟩ | ⟨hall, _⟩
  · have hd := hD k' h1 h2
    have hp : 2 ^ (k' * C.BB C.L) ≤ 2 ^ (C.L * C.BB k' + D) := two_pow_le hd
    rw [Nat.pow_add] at hp
    have h4 : a ^ C.L * 2 ^ (k' * C.BB C.L)
            ≤ a ^ C.L * (2 ^ (C.L * C.BB k') * 2 ^ D) := Nat.mul_le_mul_left _ hp
    have h5 : (b * C.M) ^ C.L * 2 ^ (C.L * C.BB k')
            ≤ (a ^ C.L * 2 ^ D) * 2 ^ (C.L * C.BB k') := by
      calc (b * C.M) ^ C.L * 2 ^ (C.L * C.BB k')
          = b ^ C.L * C.M ^ C.L * 2 ^ (C.L * C.BB k') := by rw [Nat.mul_pow]
        _ ≤ a ^ C.L * 2 ^ (k' * C.BB C.L) := h3
        _ ≤ a ^ C.L * (2 ^ (C.L * C.BB k') * 2 ^ D) := h4
        _ = (a ^ C.L * 2 ^ D) * 2 ^ (C.L * C.BB k') := by
            rw [Nat.mul_comm (2 ^ (C.L * C.BB k')), Nat.mul_assoc]
    exact Nat.le_of_mul_le_mul_right h5 (Nat.pow_pos (by decide))
  · -- every member above the threshold contradicts `m ≤ a / b`
    exfalso
    have hbig := hall C.minIdx C.minIdx_pos C.minIdx_le
    have hsmall : b * C.y C.minIdx ≤ a := C.m_le_of_size hK
    omega

/-! ## 8. The repeat theorem (Theorem 4 of docs/BALANCE.md) -/

/-- **The repeat theorem, fraction form.**

    Suppose a stretch of `j` steps and `X = window p j` halvings occurs at two
    different places of a cycle.  Let `a / b` pass the size test and let `D`
    bound the height of the largest member as in `max_pow_le`.  Then

        (b · 2 ^ (X+1)) ^ L  <  a ^ L · 2 ^ D ,

    i.e. `2 ^ (X+1) < (a/b) · 2 ^ (D/L)`. -/
theorem repeat_bound {p r j a b D : Nat} (hb : 0 < b)
    (hpr : p % C.L ≠ r % C.L)
    (hagree : ∀ i, i < j → C.bb (p + i + 1) = C.bb (r + i + 1))
    (hK : (3 * a + q * b) ^ C.L ≤ a ^ C.L * 2 ^ C.BB C.L)
    (hD : ∀ k, 1 ≤ k → k ≤ C.L → k * C.BB C.L ≤ C.L * C.BB k + D) :
    (b * 2 ^ (C.window p j + 1)) ^ C.L < a ^ C.L * 2 ^ D := by
  have hlt : b * 2 ^ (C.window p j + 1) < b * C.M :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_refl b) (C.repeat_lt_M hpr hagree) hb
  have hL := C.hL
  have hpow := Nat.pow_lt_pow_left hlt (by omega : C.L ≠ 0)
  exact Nat.lt_of_lt_of_le hpow (C.max_pow_le hb hK hD)

/-- **THE REPEAT THEOREM** (Theorem 4 of docs/BALANCE.md, in whole numbers).

    Let a stretch of `j` steps and `X = window p j` halvings occur at two
    different places of a cycle of `3n + q` with `L` odd members and `B`
    halvings.  Let

    * `N` be at least the size exponent: `(3 · 2^N + q)^L ≤ 2^(N·L + B)`, and
    * `D` bound the height of the largest member: `k·B ≤ L·B_k + D` for
      `1 ≤ k ≤ L`.

    Then `(X + 1) · L < N · L + D`, that is, `X + 1 < N + D / L`. -/
theorem repeat_theorem {p r j N D : Nat}
    (hpr : p % C.L ≠ r % C.L)
    (hagree : ∀ i, i < j → C.bb (p + i + 1) = C.bb (r + i + 1))
    (hN : (3 * 2 ^ N + q) ^ C.L ≤ 2 ^ (N * C.L + C.BB C.L))
    (hD : ∀ k, 1 ≤ k → k ≤ C.L → k * C.BB C.L ≤ C.L * C.BB k + D) :
    (C.window p j + 1) * C.L < N * C.L + D := by
  have hK : (3 * 2 ^ N + q * 1) ^ C.L ≤ (2 ^ N) ^ C.L * 2 ^ C.BB C.L := by
    rw [Nat.mul_one, ← Nat.pow_mul, ← Nat.pow_add]
    exact hN
  have h := C.repeat_bound (by decide : 0 < 1) hpr hagree hK hD
  rw [Nat.one_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add] at h
  rcases Nat.lt_or_ge ((C.window p j + 1) * C.L) (N * C.L + D) with hlt | hge
  · exact hlt
  · exfalso
    have := two_pow_le hge
    omega

/-- **The repeat theorem for `3n + 1`.**  The same statement with `q = 1`: the
    size test reads `(3 · 2^N + 1)^L ≤ 2^(N·L + B)`, which is the exact test
    `window_suffices` of `python/collatz_maxodd/balance.py`. -/
theorem repeat_theorem_q1 (C : Cycle 1) {p r j N D : Nat}
    (hpr : p % C.L ≠ r % C.L)
    (hagree : ∀ i, i < j → C.bb (p + i + 1) = C.bb (r + i + 1))
    (hN : (3 * 2 ^ N + 1) ^ C.L ≤ 2 ^ (N * C.L + C.BB C.L))
    (hD : ∀ k, 1 ≤ k → k ≤ C.L → k * C.BB C.L ≤ C.L * C.BB k + D) :
    (C.window p j + 1) * C.L < N * C.L + D :=
  C.repeat_theorem hpr hagree hN hD

/-- **A heavy stretch occurs only once.**  The form the corollaries of
    docs/BALANCE.md consume.  Let `N` pass the size test and let the largest
    member sit at most `s` whole halvings above the lowest level
    (`k·B ≤ L·(B_k + s)`).  Then a stretch with `X + 1 ≥ N + s` halvings that is
    seen below `p` and below `r` is seen at one place: `p ≡ r (mod L)`. -/
theorem repeat_unique {p r j N s : Nat}
    (hagree : ∀ i, i < j → C.bb (p + i + 1) = C.bb (r + i + 1))
    (hN : (3 * 2 ^ N + q) ^ C.L ≤ 2 ^ (N * C.L + C.BB C.L))
    (hD : ∀ k, 1 ≤ k → k ≤ C.L → k * C.BB C.L ≤ C.L * (C.BB k + s))
    (hX : N + s ≤ C.window p j + 1) : p % C.L = r % C.L := by
  rcases Nat.decEq (p % C.L) (r % C.L) with hne | heq
  · exfalso
    have hD' : ∀ k, 1 ≤ k → k ≤ C.L → k * C.BB C.L ≤ C.L * C.BB k + C.L * s := by
      intro k h1 h2
      have h := hD k h1 h2
      rw [Nat.mul_add] at h
      exact h
    have h := C.repeat_theorem hne hagree hN hD'
    have h2 : (N + s) * C.L ≤ (C.window p j + 1) * C.L := Nat.mul_le_mul_right _ hX
    rw [Nat.add_mul, Nat.mul_comm s C.L] at h2
    omega
  · exact heq

end Cycle

/-! ## 9. Non-vacuity — every statement above, on a cycle that exists

`cycle5 : Cycle 5` is the genuine cycle `49 → 19 → 31 → 49` of `3n + 5`
(`Collatz/Examples.lean`).  Backwards from the maximum its halving counts are
`bb 1 = 1`, `bb 2 = 1`, `bb 3 = 3`.  The stretch "one step, one halving" occurs
at two different places: below position `0` (the step `31 → 49`) and below
position `1` (the step `19 → 31`).  So `j = 1`, `X = 1`, and

    3 · (31 − 19) = 36 = 2 · (49 − 31) ,       t = 6 ,
    M − m = 30 ≥ 2 ^ 2 = 4 ,                    M − m = 30 ≥ 2 · 3 = 6 . -/

theorem cycle5_bb : cycle5.bb 1 = 1 ∧ cycle5.bb 2 = 1 ∧ cycle5.bb 3 = 3 := by
  have h1 : cycle5.y 1 = 31 := rfl
  have h2 : cycle5.y 2 = 19 := rfl
  have h3 : cycle5.y 3 = 49 := rfl
  simp [Cycle.bb, h1, h2, h3, v2]

/-- The stretch below position `0` equals the stretch below position `1`. -/
theorem cycle5_agree : ∀ i, i < 1 → cycle5.bb (0 + i + 1) = cycle5.bb (1 + i + 1) := by
  intro i hi
  have h0 : i = 0 := by omega
  subst h0
  show cycle5.bb 1 = cycle5.bb 2
  rw [cycle5_bb.1, cycle5_bb.2.1]

theorem cycle5_window : cycle5.window 0 1 = 1 := by
  show 0 + cycle5.bb 1 = 1
  rw [cycle5_bb.1]

/-- The repeat identity on a real cycle: `3 · 31 + 2 · 31 = 3 · 19 + 2 · 49`. -/
theorem cycle5_repeat_identity :
    3 ^ 1 * cycle5.y (0 + 1) + 2 ^ cycle5.window 0 1 * cycle5.y 1
      = 3 ^ 1 * cycle5.y (1 + 1) + 2 ^ cycle5.window 0 1 * cycle5.y 0 :=
  cycle5.repeat_identity 1 cycle5_agree

/-- Lemma 13 on a real cycle: `19 + 4 ≤ 49` and `19 + 6 ≤ 49`. -/
theorem cycle5_repeat_gap :
    cycle5.m + 2 ^ (cycle5.window 0 1 + 1) ≤ cycle5.M
      ∧ cycle5.m + 2 * 3 ^ 1 ≤ cycle5.M :=
  cycle5.repeat_gap_M (by decide) cycle5_agree

/-- The size test at `a / b = 29`: `92 ^ 3 = 778688 ≤ 780448 = 29 ^ 3 · 32`,
    so the smallest member is at most `29` (it is `19`). -/
theorem cycle5_size : (3 * 29 + 5 * 1) ^ cycle5.L ≤ 29 ^ cycle5.L * 2 ^ cycle5.BB cycle5.L := by
  show (3 * 29 + 5 * 1) ^ 3 ≤ 29 ^ 3 * 2 ^ cycle5.BB 3
  rw [cycle5_BB]
  decide

/-- The largest member of `cycle5` sits at most `4` level units above the rest:
    `k · 5 ≤ 3 · B_k + 4` for `k = 1, 2, 3`, with `B_1, B_2, B_3 = 1, 2, 5`. -/
theorem cycle5_height :
    ∀ k, 1 ≤ k → k ≤ cycle5.L → k * cycle5.BB cycle5.L ≤ cycle5.L * cycle5.BB k + 4 := by
  intro k h1 h2
  have hL : cycle5.L = 3 := rfl
  rw [hL] at h2 ⊢
  have b1 : cycle5.BB 1 = 1 := by
    show 0 + cycle5.bb 1 = 1
    rw [cycle5_bb.1]
  have b2 : cycle5.BB 2 = 2 := by
    show 0 + cycle5.bb 1 + cycle5.bb 2 = 2
    rw [cycle5_bb.1, cycle5_bb.2.1]
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega) with h | h | h <;> subst h
  · rw [cycle5_BB, b1]; decide
  · rw [cycle5_BB, b2]; decide
  · rw [cycle5_BB]; decide

/-- Lemma 14 on a real cycle: `49 ^ 3 = 117649 ≤ 390224 = 29 ^ 3 · 2 ^ 4`. -/
theorem cycle5_max_pow_le : (1 * cycle5.M) ^ cycle5.L ≤ 29 ^ cycle5.L * 2 ^ 4 :=
  cycle5.max_pow_le (by decide) cycle5_size cycle5_height

/-- The repeat theorem, fraction form, on a real cycle:
    `(2 ^ 2) ^ 3 = 64 < 390224`. -/
theorem cycle5_repeat_bound :
    (1 * 2 ^ (cycle5.window 0 1 + 1)) ^ cycle5.L < 29 ^ cycle5.L * 2 ^ 4 :=
  cycle5.repeat_bound (by decide) (by decide) cycle5_agree cycle5_size cycle5_height

/-- The repeat theorem on a real cycle, with `N = 5`:
    `(3 · 32 + 5) ^ 3 = 1030301 ≤ 2 ^ 20`, and `(1 + 1) · 3 = 6 < 5 · 3 + 4`. -/
theorem cycle5_repeat_theorem :
    (cycle5.window 0 1 + 1) * cycle5.L < 5 * cycle5.L + 4 := by
  refine cycle5.repeat_theorem (N := 5) (by decide) cycle5_agree ?_ cycle5_height
  show (3 * 2 ^ 5 + 5) ^ 3 ≤ 2 ^ (5 * 3 + cycle5.BB 3)
  rw [cycle5_BB]
  decide

end Collatz
