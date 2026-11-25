import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7826

open PEqualNP.AndCount

theorem sideTrue_def : ∀ {k : ℕ} (U B : Finset (Fin 27)) (F : Finset (Fin k)) (i : Fin k) (val : Fin k → Bool),
    AndCountCircuit.sideTrue U B F i val =
      decide ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ val j = true) := fun _ _ _ _ _ => rfl

theorem eval_def : ∀ (E : AndCountCircuit 27) (U : Finset (Fin 27)),
    E.eval U = decide ((∃ v ∈ E.outVars, v ∈ U) ∨ ∃ j ∈ E.outGates, E.gateVal U j = true) :=
  fun _ _ => rfl

theorem sideTrue_congr : ∀ {k : ℕ} (U B : Finset (Fin 27)) (F : Finset (Fin k)) (i : Fin k)
    (val val' : Fin k → Bool), (∀ j : Fin k, j < i → val j = val' j) →
    AndCountCircuit.sideTrue U B F i val = AndCountCircuit.sideTrue U B F i val' := by
  classical
  intro k U B F i val val' h
  rw [sideTrue_def, sideTrue_def, decide_eq_decide]
  constructor
  · intro h1
    rcases h1 with h1 | h2
    · exact Or.inl h1
    · rcases h2 with ⟨j, hj, hlt, hv⟩
      exact Or.inr ⟨j, hj, hlt, by rw [← h j hlt]; exact hv⟩
  · intro h1
    rcases h1 with h1 | h2
    · exact Or.inl h1
    · rcases h2 with ⟨j, hj, hlt, hv⟩
      exact Or.inr ⟨j, hj, hlt, by rw [h j hlt]; exact hv⟩

theorem fuel_indep : ∀ (E : AndCountCircuit 27) (U : Finset (Fin 27))
    (d d' : ℕ) (i : Fin E.size), i.val < d → i.val < d' →
    E.gateValFuel U d i = E.gateValFuel U d' i := by
  classical
  intro E U d
  induction d with
  | zero =>
    intro d' i h
    exact absurd h (Nat.not_lt_zero _)
  | succ e ih =>
    intro d' i h h'
    cases d' with
    | zero => exact absurd h' (Nat.not_lt_zero _)
    | succ e' =>
      have key : ∀ j : Fin E.size, j < i → E.gateValFuel U e j = E.gateValFuel U e' j := by
        intro j hj
        have hji : j.val < i.val := hj
        exact ih e' j (by omega) (by omega)
      show (AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e) &&
            AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e)) =
           (AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e') &&
            AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e'))
      rw [sideTrue_congr U (E.leftVars i) (E.leftGates i) i _ _ key,
          sideTrue_congr U (E.rightVars i) (E.rightGates i) i _ _ key]

theorem gateVal_eq : ∀ (E : AndCountCircuit 27) (U : Finset (Fin 27)) (i : Fin E.size),
    E.gateVal U i =
      (AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateVal U) &&
       AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateVal U)) := by
  classical
  intro E U i
  have hi : i.val < E.size := i.2
  obtain ⟨e, he⟩ : ∃ e, E.size = e + 1 := ⟨E.size - 1, by omega⟩
  have key : ∀ j : Fin E.size, j < i → E.gateValFuel U e j = E.gateVal U j := by
    intro j hj
    have hji : j.val < i.val := hj
    exact fuel_indep E U e E.size j (by omega) j.2
  have h1 : E.gateVal U i = E.gateValFuel U (e + 1) i :=
    fuel_indep E U E.size (e + 1) i i.2 (by omega)
  rw [h1]
  show (AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e) &&
        AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e)) = _
  rw [sideTrue_congr U (E.leftVars i) (E.leftGates i) i _ _ key,
      sideTrue_congr U (E.rightVars i) (E.rightGates i) i _ _ key]

-- The indices at which gate `g` is false.
def Z (C : AndCountCircuit 27) (X : Fin 19 → Finset (Fin 27)) (g : Fin C.size) : Finset (Fin 19) :=
  Finset.univ.filter (fun i => C.gateVal (X i) g = false)

theorem mem_Z (C : AndCountCircuit 27) (X : Fin 19 → Finset (Fin 27)) (g : Fin C.size) (i : Fin 19) :
    i ∈ Z C X g ↔ C.gateVal (X i) g = false := by
  simp [Z]

-- A good set: at most one element, or the false set of an earlier true gate.
def Good (C : AndCountCircuit 27) (X : Fin 19 → Finset (Fin 27)) (T : Finset (Fin C.size))
    (g : Fin C.size) (A : Finset (Fin 19)) : Prop :=
  A.card ≤ 1 ∨ ∃ h : Fin C.size, h < g ∧ h ∈ T ∧ A = Z C X h

theorem side_lemma (C : AndCountCircuit 27) (U : Finset (Fin 27)) (X : Fin 19 → Finset (Fin 27))
    (T : Finset (Fin C.size)) (hT : ∀ g, g ∈ T ↔ C.gateVal U g = true)
    (hcov : ∀ i j : Fin 19, i ≠ j → U ⊆ X i ∪ X j)
    (g : Fin C.size) (B : Finset (Fin 27)) (F : Finset (Fin C.size))
    (hs : AndCountCircuit.sideTrue U B F g (C.gateVal U) = true) :
    ∃ A : Finset (Fin 19), (∀ i : Fin 19,
      AndCountCircuit.sideTrue (X i) B F g (C.gateVal (X i)) = false → i ∈ A) ∧ Good C X T g A := by
  classical
  rw [sideTrue_def] at hs
  have hs' := of_decide_eq_true hs
  rcases hs' with ⟨v, hvB, hvU⟩ | ⟨h, hF, hlt, hval⟩
  · refine ⟨Finset.univ.filter (fun i => v ∉ X i), ?_, ?_⟩
    · intro i hi
      rw [sideTrue_def] at hi
      have hi' := of_decide_eq_false hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hvX
      exact hi' (Or.inl ⟨v, hvB, hvX⟩)
    · left
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      by_contra hab
      have := hcov a b hab hvU
      rcases Finset.mem_union.mp this with h1 | h1
      · exact ha h1
      · exact hb h1
  · refine ⟨Z C X h, ?_, Or.inr ⟨h, hlt, (hT h).mpr hval, rfl⟩⟩
    intro i hi
    rw [sideTrue_def] at hi
    have hi' := of_decide_eq_false hi
    rw [mem_Z]
    cases hc : C.gateVal (X i) h with
    | false => rfl
    | true => exact absurd (Or.inr ⟨h, hF, hlt, hc⟩) hi'

theorem gate_lemma (C : AndCountCircuit 27) (U : Finset (Fin 27)) (X : Fin 19 → Finset (Fin 27))
    (T : Finset (Fin C.size)) (hT : ∀ g, g ∈ T ↔ C.gateVal U g = true)
    (hcov : ∀ i j : Fin 19, i ≠ j → U ⊆ X i ∪ X j)
    (g : Fin C.size) (hg : g ∈ T) :
    ∃ A B : Finset (Fin 19), Z C X g ⊆ A ∪ B ∧ Good C X T g A ∧ Good C X T g B := by
  classical
  have hgv := (hT g).mp hg
  rw [gateVal_eq] at hgv
  rw [Bool.and_eq_true] at hgv
  obtain ⟨A, hA, gA⟩ := side_lemma C U X T hT hcov g _ _ hgv.1
  obtain ⟨B, hB, gB⟩ := side_lemma C U X T hT hcov g _ _ hgv.2
  refine ⟨A, B, ?_, gA, gB⟩
  intro i hi
  rw [mem_Z, gateVal_eq, Bool.and_eq_false_iff] at hi
  rcases hi with h1 | h1
  · exact Finset.mem_union_left _ (hA i h1)
  · exact Finset.mem_union_right _ (hB i h1)

theorem uf (C : AndCountCircuit 27) (U : Finset (Fin 27)) (X : Fin 19 → Finset (Fin 27))
    (T : Finset (Fin C.size)) (hT : ∀ g, g ∈ T ↔ C.gateVal U g = true)
    (hcov : ∀ i j : Fin 19, i ≠ j → U ⊆ X i ∪ X j) :
    ∀ k : ℕ, ∃ cls : Fin 19 → Fin 19,
      19 ≤ (Finset.univ.image cls).card + (T.filter (fun h => h.val < k)).card ∧
      ∀ g ∈ T, g.val < k → ∃ c, ∀ i ∈ Z C X g, cls i = c := by
  classical
  intro k
  induction k with
  | zero =>
    refine ⟨id, ?_, ?_⟩
    · simp
    · intro g _ hg; omega
  | succ k ih =>
    obtain ⟨cls, hcard, hcls⟩ := ih
    by_cases hk : ∃ g ∈ T, g.val = k
    · obtain ⟨g, hgT, hgk⟩ := hk
      obtain ⟨A, B, hAB, gA, gB⟩ := gate_lemma C U X T hT hcov g hgT
      have within : ∀ S : Finset (Fin 19), Good C X T g S → ∃ c, ∀ i ∈ S, cls i = c := by
        intro S hS
        rcases hS with hS | ⟨h, hlt, hhT, rfl⟩
        · by_cases hne : S.Nonempty
          · obtain ⟨a, ha⟩ := hne
            refine ⟨cls a, ?_⟩
            intro i hi
            rw [Finset.card_le_one] at hS
            rw [hS i hi a ha]
          · refine ⟨0, ?_⟩
            intro i hi
            exact absurd ⟨i, hi⟩ hne
        · have : h.val < k := by
            have : h.val < g.val := hlt
            omega
          exact hcls h hhT this
      obtain ⟨c1, hc1⟩ := within A gA
      obtain ⟨c2, hc2⟩ := within B gB
      refine ⟨fun i => if cls i = c2 then c1 else cls i, ?_, ?_⟩
      · have himg : (Finset.univ.image cls).erase c2 ⊆
            Finset.univ.image (fun i => if cls i = c2 then c1 else cls i) := by
          intro c hc
          rw [Finset.mem_erase] at hc
          obtain ⟨hne, hc⟩ := hc
          rw [Finset.mem_image] at hc ⊢
          obtain ⟨i, _, hi⟩ := hc
          refine ⟨i, Finset.mem_univ _, ?_⟩
          rw [if_neg (by rw [hi]; exact hne)]
          exact hi
        have h1 := Finset.card_le_card himg
        have h2 := Finset.pred_card_le_card_erase (s := Finset.univ.image cls) (a := c2)
        have hsub : T.filter (fun h => h.val < k) ⊂ T.filter (fun h => h.val < k + 1) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨g, ?_, ?_⟩
            · rw [Finset.mem_filter]; exact ⟨hgT, by omega⟩
            · rw [Finset.mem_filter]; intro h; omega
          · intro x hx
            rw [Finset.mem_filter] at hx ⊢
            exact ⟨hx.1, by omega⟩
        have h3 := Finset.card_lt_card hsub
        omega
      · intro g' hg'T hg'k
        by_cases hgg : g' = g
        · subst hgg
          refine ⟨c1, ?_⟩
          intro i hi
          rcases Finset.mem_union.mp (hAB hi) with hA | hB
          · have := hc1 i hA
            simp only [this]
            split_ifs <;> simp_all
          · have := hc2 i hB
            simp [this]
        · have : g'.val < k := by
            have hne : g'.val ≠ g.val := fun h => hgg (Fin.ext h)
            omega
          obtain ⟨c, hc⟩ := hcls g' hg'T this
          refine ⟨if c = c2 then c1 else c, ?_⟩
          intro i hi
          simp [hc i hi]
    · refine ⟨cls, ?_, ?_⟩
      · have heq : T.filter (fun h => h.val < k + 1) = T.filter (fun h => h.val < k) := by
          apply Finset.filter_congr
          intro x hx
          have : x.val ≠ k := fun h => hk ⟨x, hx, h⟩
          omega
        rw [heq]; exact hcard
      · intro g hgT hgk
        have : g.val ≠ k := fun h => hk ⟨g, hgT, h⟩
        exact hcls g hgT (by omega)

end PEqualNP.Outside.L_meta_7826

theorem PEqualNP.Outside.L_meta_7826 : ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)) (x2 : Finset (Fin (27 : ℕ))) (x3 : Fin (19 : ℕ) → Finset (Fin (27 : ℕ))) (x4 : Finset (Fin x1.size)), (∀ (x5 : Fin x1.size), x5 ∈ x4 ↔ x1.gateVal x2 x5 = Bool.true) → (∀ (x6 : Fin (19 : ℕ)), x1.eval (x3 x6) = Bool.false) → x1.eval x2 = Bool.true → (∀ (x8 x9 : Fin (19 : ℕ)), x8 ≠ x9 → x2 ⊆ x3 x8 ∪ x3 x9) → (19 : ℕ) ≤ x4.card + (1 : ℕ) := by
  classical
  intro C U X T hT hX hU hcov
  obtain ⟨cls, hcard, hcls⟩ := PEqualNP.Outside.L_meta_7826.uf C U X T hT hcov C.size
  have hfil : T.filter (fun h => h.val < C.size) = T := by
    apply Finset.filter_true_of_mem
    intro x _
    exact x.2
  rw [hfil] at hcard
  rw [PEqualNP.Outside.L_meta_7826.eval_def] at hU
  have hU' := of_decide_eq_true hU
  rcases hU' with ⟨v, hv, hvU⟩ | ⟨o, ho, hoU⟩
  · exfalso
    have := hcov 0 1 (by decide) hvU
    rcases Finset.mem_union.mp this with h1 | h1
    · have h0 := hX 0
      rw [PEqualNP.Outside.L_meta_7826.eval_def] at h0
      exact of_decide_eq_false h0 (Or.inl ⟨v, hv, h1⟩)
    · have h0 := hX 1
      rw [PEqualNP.Outside.L_meta_7826.eval_def] at h0
      exact of_decide_eq_false h0 (Or.inl ⟨v, hv, h1⟩)
  · have hoT : o ∈ T := (hT o).mpr hoU
    obtain ⟨c, hc⟩ := hcls o hoT o.2
    have hZ : ∀ i : Fin 19, i ∈ PEqualNP.Outside.L_meta_7826.Z C X o := by
      intro i
      rw [PEqualNP.Outside.L_meta_7826.mem_Z]
      have h0 := hX i
      rw [PEqualNP.Outside.L_meta_7826.eval_def] at h0
      have h0' := of_decide_eq_false h0
      cases hci : C.gateVal (X i) o with
      | false => rfl
      | true => exact absurd (Or.inr ⟨o, ho, hci⟩) h0'
    have himg : Finset.univ.image cls ⊆ {c} := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      rw [Finset.mem_singleton]
      exact hc i (hZ i)
    have := Finset.card_le_card himg
    rw [Finset.card_singleton] at this
    omega
