import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_8419 : let x1 : Type := Fin (21 : ℕ); have x2 : x1 → Finset x1 := fun (x2 : x1) => {x3 : x1 | (↑x2 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]}; have x3 : (Fin (42 : ℕ) → Bool) → Prop := fun (x3 : Fin (42 : ℕ) → Bool) => ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true; ∀ (x4 : Fin (42 : ℕ) → Bool), x3 x4 → (∀ (x6 : Fin (42 : ℕ) → Bool), (∀ (x7 : Fin (42 : ℕ)), x6 x7 = Bool.true → x4 x7 = Bool.true) → x3 x6 → x6 = x4) → ∃ (x7 : x1) (x8 : x1), x7 ∈ x2 x8 ∧ List.ofFn x4 = PEqualNP.GenericRejection.incidenceInput {x7} {x8} := by
  dsimp only
  intro x4 hx hmin
  obtain ⟨a, b, ⟨ha, hb, hd⟩, hxa, hxb⟩ := hx
  have hab : a.val ≠ b.val := by omega
  have h6 : (fun i : Fin 42 => decide (i = a ∨ i = b)) = x4 := by
    apply hmin
    · intro i hi
      simp only [decide_eq_true_eq] at hi
      rcases hi with rfl | rfl <;> assumption
    · exact ⟨a, b, ⟨ha, hb, hd⟩, by simp, by simp⟩
  refine ⟨⟨a.val, ha⟩, ⟨b.val - 21, by omega⟩, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hbb : b.val - 21 + 21 = b.val := by omega
    show (b.val - 21 + 21 - a.val) % 21 ∈ _
    rw [hbb]
    have hm : (b.val + 21 - a.val) % 21 = (b.val - a.val) % 21 := by omega
    rw [hm] at hd
    exact hd
  · rw [← h6]
    unfold PEqualNP.GenericRejection.incidenceInput
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_ofFn]
      have hi42 : i < 42 := by simpa using h1
      rw [List.getElem_append]
      split <;> rename_i hlt <;> have hlt2 := hlt <;> simp only [List.length_ofFn] at hlt2
      · simp only [List.getElem_ofFn, Finset.mem_singleton, Fin.ext_iff, List.length_ofFn]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        omega
      · simp only [List.getElem_ofFn, Finset.mem_singleton, Fin.ext_iff, List.length_ofFn]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        omega
