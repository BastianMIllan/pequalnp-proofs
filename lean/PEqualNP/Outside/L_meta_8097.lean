import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8097

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

theorem gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

theorem gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

theorem side_flip {n : ℕ} (C : AndCountCircuit n) (I : Finset (Fin n)) (v : Fin n)
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) (j : Fin C.size)
    (hI : sideTrue I B F j (C.gateVal I) = false)
    (hU : sideTrue (insert v I) B F j (C.gateVal (insert v I)) = true) :
    v ∈ B ∨ ∃ j' ∈ F, j' < j ∧ C.gateVal (insert v I) j' = true ∧ C.gateVal I j' = false := by
  unfold sideTrue at hI hU
  rw [decide_eq_true_eq] at hU
  rw [decide_eq_false_iff_not] at hI
  rcases hU with ⟨u, huB, huU⟩ | ⟨j', hjF, hjj, hval⟩
  · rcases Finset.mem_insert.mp huU with h | h
    · subst h; exact Or.inl huB
    · exact absurd (Or.inl ⟨u, huB, h⟩) hI
  · right
    refine ⟨j', hjF, hjj, hval, ?_⟩
    cases hx : C.gateVal I j'
    · rfl
    · exact absurd (Or.inr ⟨j', hjF, hjj, hx⟩) hI

theorem flip_lemma {n : ℕ} (C : AndCountCircuit n) (I : Finset (Fin n)) (v : Fin n) :
    ∀ (m : ℕ) (j : Fin C.size), j.val < m → C.gateVal (insert v I) j = true →
      C.gateVal I j = false →
      ∃ k : Fin C.size,
        (sideTrue I (C.leftVars k) (C.leftGates k) k (C.gateVal I) = false ∧
          v ∈ C.leftVars k) ∨
        ((sideTrue I (C.leftVars k) (C.leftGates k) k (C.gateVal I) = true ∧
          sideTrue I (C.rightVars k) (C.rightGates k) k (C.gateVal I) = false) ∧
          v ∈ C.rightVars k) := by
  intro m
  induction m with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ m ih =>
    intro j hj hU hI
    rw [gateVal_unfold] at hU hI
    rw [Bool.and_eq_true] at hU
    cases ha : sideTrue I (C.leftVars j) (C.leftGates j) j (C.gateVal I)
    · rcases side_flip C I v _ _ j ha hU.1 with h | ⟨j', _, hjj, h1, h2⟩
      · exact ⟨j, Or.inl ⟨ha, h⟩⟩
      · exact ih j' (by have : j'.val < j.val := hjj; omega) h1 h2
    · rw [ha, Bool.true_and] at hI
      rcases side_flip C I v _ _ j hI hU.2 with h | ⟨j', _, hjj, h1, h2⟩
      · exact ⟨j, Or.inr ⟨⟨ha, hI⟩, h⟩⟩
      · exact ih j' (by have : j'.val < j.val := hjj; omega) h1 h2

end PEqualNP.Outside.L_meta_8097

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit in
theorem PEqualNP.Outside.L_meta_8097 : ∀ (x1 : ℕ) (x2 : PEqualNP.AndCount.AndCountCircuit x1) (x3 : SimpleGraph (Fin x1)), x2.Computes x3 → x2.outVars = ∅ → ∀ (x6 : Finset (Fin x1)), (∀ (x7 x8 : Fin x1), x3.Adj x7 x8 → x7 ∈ x6 ∨ x8 ∈ x6) → (∀ x8 ⊆ x6, (∀ (x10 x11 : Fin x1), x3.Adj x10 x11 → x10 ∈ x8 ∨ x11 ∈ x8) → x6 ⊆ x8) → ∃ (x9 : Finset (Fin x2.size)) (x10 : Finset (Fin x2.size)), Disjoint x9 x10 ∧ x9.biUnion x2.leftVars ∪ x10.biUnion x2.rightVars = x6 := by
  intro n C G hC hout X hcov hmin
  classical
  set I : Finset (Fin n) := Finset.univ \ X with hIdef
  have memI : ∀ u, u ∈ I ↔ u ∉ X := by intro u; simp [hIdef]
  refine ⟨Finset.univ.filter
      (fun k => sideTrue I (C.leftVars k) (C.leftGates k) k (C.gateVal I) = false),
    Finset.univ.filter
      (fun k => sideTrue I (C.leftVars k) (C.leftGates k) k (C.gateVal I) = true ∧
        sideTrue I (C.rightVars k) (C.rightGates k) k (C.gateVal I) = false), ?_, ?_⟩
  · rw [Finset.disjoint_filter]
    intro k _ h1 h2
    rw [h1] at h2
    exact Bool.false_ne_true h2.1
  · ext v
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro (⟨k, hk, hv⟩ | ⟨k, ⟨_, hk⟩, hv⟩)
      · unfold sideTrue at hk
        rw [decide_eq_false_iff_not] at hk
        by_contra hX
        exact hk (Or.inl ⟨v, hv, (memI v).mpr hX⟩)
      · unfold sideTrue at hk
        rw [decide_eq_false_iff_not] at hk
        by_contra hX
        exact hk (Or.inl ⟨v, hv, (memI v).mpr hX⟩)
    · intro hvX
      have hw : ∃ w, G.Adj v w ∧ w ∉ X := by
        by_contra hno
        push Not at hno
        have hcov' : ∀ a b : Fin n, G.Adj a b → a ∈ X.erase v ∨ b ∈ X.erase v := by
          intro a b hab
          by_cases hav : a = v
          · subst hav
            exact Or.inr (Finset.mem_erase.mpr ⟨(G.ne_of_adj hab).symm, hno b hab⟩)
          · by_cases hbv : b = v
            · subst hbv
              exact Or.inl (Finset.mem_erase.mpr ⟨G.ne_of_adj hab, hno a hab.symm⟩)
            · rcases hcov a b hab with h | h
              · exact Or.inl (Finset.mem_erase.mpr ⟨hav, h⟩)
              · exact Or.inr (Finset.mem_erase.mpr ⟨hbv, h⟩)
        have := hmin (X.erase v) (Finset.erase_subset v X) hcov' hvX
        exact (Finset.notMem_erase v X) this
      obtain ⟨w, hvw, hwX⟩ := hw
      have hEU : C.eval (insert v I) = true :=
        (hC (insert v I)).mpr ⟨v, Finset.mem_insert_self v I, w,
          Finset.mem_insert_of_mem ((memI w).mpr hwX), hvw⟩
      have hEI : C.eval I = false := by
        cases he : C.eval I
        · rfl
        · obtain ⟨a, ha, c, hc, hac⟩ := (hC I).mp he
          rcases hcov a c hac with h | h
          · exact absurd h ((memI a).mp ha)
          · exact absurd h ((memI c).mp hc)
      unfold AndCountCircuit.eval at hEU hEI
      rw [decide_eq_true_eq] at hEU
      rw [decide_eq_false_iff_not] at hEI
      rcases hEU with ⟨u, hu, _⟩ | ⟨j, hj, hjv⟩
      · rw [hout] at hu
        exact absurd hu (Finset.notMem_empty u)
      · have hjI : C.gateVal I j = false := by
          cases hx : C.gateVal I j
          · rfl
          · exact absurd (Or.inr ⟨j, hj, hx⟩) hEI
        obtain ⟨k, hk⟩ := PEqualNP.Outside.L_meta_8097.flip_lemma C I v C.size j j.isLt hjv hjI
        rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨k, h1, h2⟩
        · exact Or.inr ⟨k, h1, h2⟩
