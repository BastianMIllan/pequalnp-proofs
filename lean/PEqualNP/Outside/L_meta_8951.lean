import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8951

open PEqualNP.CircuitLowerBounds

theorem getD_ofFn {N : ℕ} (x : Fin N → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < N then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < N
  · simp [h]
  · simp [h]

theorem dep (N : ℕ) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 N C)
    (h1 : ¬∃ g, C.gates[(1 : ℕ)]? = some g) :
    ∃ W : Finset ℕ, W.card ≤ 2 ∧ ∀ x y : Fin N → Bool,
      (∀ i : Fin N, (i : ℕ) ∈ W → x i = y i) →
      C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
  have key : ∀ (W : Finset ℕ) (x y : Fin N → Bool), (∀ i : Fin N, (i : ℕ) ∈ W → x i = y i) →
      ∀ i ∈ W, (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
    intro W x y hxy i hi
    rw [getD_ofFn, getD_ofFn]
    split_ifs with h
    · exact hxy ⟨i, h⟩ hi
    · rfl
  obtain ⟨gs, out⟩ := C
  rcases gs with _ | ⟨g, _ | ⟨g2, rest⟩⟩
  · refine ⟨{out}, by simp, ?_⟩
    intro x y hxy
    simp only [Circuit.eval, Circuit.wires, List.foldl_nil]
    exact key {out} x y hxy out (by simp)
  · have hlen : g.inputs.length = 2 := hAO.2.2 g (by simp)
    by_cases ho : out < N
    · refine ⟨{out}, by simp, ?_⟩
      intro x y hxy
      simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil]
      have hx : ∀ z : Fin N → Bool, ∀ v : Bool,
          (List.ofFn z ++ [v]).getD out false = (List.ofFn z).getD out false := by
        intro z v
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by simpa using ho)]
      rw [hx, hx]
      exact key {out} x y hxy out (by simp)
    · refine ⟨g.inputs.toFinset, (List.toFinset_card_le _).trans hlen.le, ?_⟩
      intro x y hxy
      simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil]
      have hm : g.inputs.map (fun i => (List.ofFn x).getD i false) =
          g.inputs.map (fun i => (List.ofFn y).getD i false) := by
        apply List.map_congr_left
        intro i hi
        exact key _ x y hxy i (List.mem_toFinset.mpr hi)
      have hx : ∀ z : Fin N → Bool, ∀ v : Bool,
          (List.ofFn z ++ [v]).getD out false = [v].getD (out - N) false := by
        intro z v
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by simp; omega)]
        simp
      rw [hx, hx, hm]
  · exact absurd ⟨g2, rfl⟩ h1

end PEqualNP.Outside.L_meta_8951

theorem PEqualNP.Outside.L_meta_8951 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : Finset (Fin x1 × Fin x2) → Finset (Fin (x1 + x2)) := fun (x5 : Finset (Fin x1 × Fin x2)) => x5.biUnion fun (x6 : Fin x1 × Fin x2) => {Fin.castAdd x2 x6.1, Fin.natAdd x1 x6.2};   (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x8 = Decidable.decide (∃ x9 ∈ x3, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true)) → (¬∃ (x9 : Finset (Fin x1 × Fin x2)) (x10 : Finset (Fin x1 × Fin x2)) (x11 : Fin (x1 + x2)), x9.Nonempty ∧ x9 ∪ x10 = x3 ∧ Disjoint (x5 x9) (x5 x10) ∧ ∀ x12 ∈ x9, Fin.castAdd x2 x12.1 = x11 ∨ Fin.natAdd x1 x12.2 = x11) → (¬∃ (x10 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[(1 : ℕ)]? = Option.some x10) → ∃ (x11 : Finset (Fin x1)) (x12 : Finset (Fin x2)), (∀ x13 ∈ x3, x13.1 ∈ x11 ∨ x13.2 ∈ x12) ∧ x3.card + x11.card + x12.card ≤ x4.size + (1 : ℕ) := by
  intro x1 x2 x3 C
  dsimp only
  intro _ hAO hF hstar h1
  by_cases hE : x3 = ∅
  · subst hE
    exact ⟨∅, ∅, by simp, by simp⟩
  · exfalso
    obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hE
    have hex : ∃ e' ∈ x3, e'.1 ≠ e.1 := by
      by_contra hno
      push_neg at hno
      apply hstar
      refine ⟨x3, ∅, Fin.castAdd x2 e.1, ⟨e, he⟩, by simp, by simp, ?_⟩
      intro e' he'
      left
      rw [hno e' he']
    obtain ⟨e', he', hne⟩ := hex
    obtain ⟨W, hW, hdep⟩ := PEqualNP.Outside.L_meta_8951.dep (x1 + x2) C hAO h1
    have mem : ∀ f ∈ x3, ((f.1 : ℕ) ∈ W) ∧ ∃ v ∈ W, x1 ≤ v := by
      intro f hf
      have h1' : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C
          (fun i => decide (i = Fin.castAdd x2 f.1 ∨ i = Fin.natAdd x1 f.2)) = true := by
        rw [hF]
        simp only [decide_eq_true_eq]
        exact ⟨f, hf, by simp, by simp⟩
      have h2 : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C
          (fun i => decide (i = Fin.castAdd x2 f.1 ∨ i = Fin.natAdd x1 f.2) &&
            decide ((i : ℕ) ∈ W)) = true := by
        rw [← h1']
        unfold PEqualNP.MetaComplexity.circuitFun
        apply hdep
        intro i hi
        simp [hi]
      rw [hF] at h2
      simp only [decide_eq_true_eq] at h2
      obtain ⟨g, _, hg1, hg2⟩ := h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg1 hg2
      obtain ⟨hc, hcW⟩ := hg1
      obtain ⟨_, hnW⟩ := hg2
      have hgf : (g.1 : ℕ) = f.1 := by
        rcases hc with hc | hc
        · have := congrArg Fin.val hc
          simpa using this
        · have := congrArg Fin.val hc
          simp at this
          omega
      refine ⟨?_, _, hnW, by simp⟩
      simpa [hgf] using hcW
    obtain ⟨hp, v, hv, hvx⟩ := mem e he
    obtain ⟨hp', -⟩ := mem e' he'
    have hsub : ({(e.1 : ℕ), (e'.1 : ℕ), v} : Finset ℕ) ⊆ W := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl <;> assumption
    have hne' : (e.1 : ℕ) ≠ e'.1 := fun h => hne (Fin.ext h).symm
    have hlt1 : (e.1 : ℕ) < x1 := e.1.isLt
    have hlt2 : (e'.1 : ℕ) < x1 := e'.1.isLt
    have hc3 : ({(e.1 : ℕ), (e'.1 : ℕ), v} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton]; omega
      · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have := Finset.card_le_card hsub
    omega
