/-
  Collatz/Pigeonhole.lean

  A self-contained pigeonhole principle.

  Mathlib-free, and deliberately CHOICE-free: the search for a collision is an
  explicit recursive function (`hasEq`), and every case split is on a decidable
  `Nat` comparison.  Nothing here drags in `Classical.choice`, so the axiom
  certificate in `Collatz/Audit.lean` stays at `[propext, Quot.sound]`.
-/
namespace Collatz

/-- `hasEq f v n = true` exactly when some `i ≤ n` has `f i = v`. -/
def hasEq (f : Nat → Nat) (v : Nat) : Nat → Bool
  | 0     => f 0 == v
  | n + 1 => hasEq f v n || (f (n + 1) == v)

theorem hasEq_true {f : Nat → Nat} {v : Nat} :
    ∀ n, hasEq f v n = true → ∃ i, i ≤ n ∧ f i = v := by
  intro n
  induction n with
  | zero =>
      intro h
      exact ⟨0, Nat.le_refl 0, by simpa [hasEq] using h⟩
  | succ n ih =>
      intro h
      simp only [hasEq, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · obtain ⟨i, hi, hfi⟩ := ih h
        exact ⟨i, by omega, hfi⟩
      · exact ⟨n + 1, Nat.le_refl _, h⟩

theorem hasEq_false {f : Nat → Nat} {v : Nat} :
    ∀ n, hasEq f v n = false → ∀ i, i ≤ n → f i ≠ v := by
  intro n
  induction n with
  | zero =>
      intro h i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simpa [hasEq] using h
  | succ n ih =>
      intro h i hi
      simp only [hasEq, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
      rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · exact ih h.1 i (by omega)
      · have he : i = n + 1 := by omega
        subst he
        exact h.2

/-- **Pigeonhole.**  The `n + 1` indices `0 … n`, with every value below `n`,
    must collide somewhere.

    Proof by the standard *compression* trick: if nothing below `n + 1` already
    matches `f (n + 1)`, delete that one value from the codomain (shifting
    everything above it down by one) and apply the induction hypothesis. -/
theorem exists_repeat :
    ∀ (n : Nat) (f : Nat → Nat), (∀ i, i ≤ n → f i < n) →
      ∃ i j, i < j ∧ j ≤ n ∧ f i = f j := by
  intro n
  induction n with
  | zero =>
      intro f h
      exact absurd (h 0 (Nat.le_refl 0)) (Nat.not_lt_zero _)
  | succ n ih =>
      intro f h
      cases hs : hasEq f (f (n + 1)) n with
      | true =>
          obtain ⟨i, hi, hfi⟩ := hasEq_true n hs
          exact ⟨i, n + 1, by omega, Nat.le_refl _, hfi⟩
      | false =>
          have hne := hasEq_false n hs
          have key : ∀ i, i ≤ n →
              (if f i < f (n + 1) then f i else f i - 1) < n := by
            intro i hi
            have h1 : f i < n + 1 := h i (by omega)
            have h2 : f (n + 1) < n + 1 := h (n + 1) (Nat.le_refl _)
            have h3 : f i ≠ f (n + 1) := hne i hi
            by_cases hc : f i < f (n + 1)
            · rw [if_pos hc]; omega
            · rw [if_neg hc]; omega
          obtain ⟨i, j, hij, hjn, hg⟩ :=
            ih (fun i => if f i < f (n + 1) then f i else f i - 1) key
          have hgi : (if f i < f (n + 1) then f i else f i - 1)
                   = (if f j < f (n + 1) then f j else f j - 1) := hg
          have hin : i ≤ n := by omega
          have h1 : f i < n + 1 := h i (by omega)
          have h2 : f j < n + 1 := h j (by omega)
          have h3 : f (n + 1) < n + 1 := h (n + 1) (Nat.le_refl _)
          have h4 : f i ≠ f (n + 1) := hne i hin
          have h5 : f j ≠ f (n + 1) := hne j hjn
          refine ⟨i, j, hij, by omega, ?_⟩
          by_cases hci : f i < f (n + 1)
          · by_cases hcj : f j < f (n + 1)
            · rw [if_pos hci, if_pos hcj] at hgi; omega
            · rw [if_pos hci, if_neg hcj] at hgi; omega
          · by_cases hcj : f j < f (n + 1)
            · rw [if_neg hci, if_pos hcj] at hgi; omega
            · rw [if_neg hci, if_neg hcj] at hgi; omega

end Collatz
