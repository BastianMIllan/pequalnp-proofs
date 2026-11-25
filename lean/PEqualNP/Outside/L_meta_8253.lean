import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8253

def stp (L : List Bool) (p : Finset ℕ × Finset ℕ) : List Bool :=
  L ++ [decide (∀ i ∈ p.1, L.getD i false = true) || decide (∀ i ∈ p.2, L.getD i false = true)]

def fs (n : ℕ) (S : Finset ℕ) : Finset ℕ :=
  if (S.filter (· < n)).card ≤ 2 then S else {n}

def fp (n : ℕ) (p : Finset ℕ × Finset ℕ) : Finset ℕ × Finset ℕ := (fs n p.1, fs n p.2)

theorem fs_card (n : ℕ) (S : Finset ℕ) : ((fs n S).filter (· < n)).card ≤ 2 := by
  unfold fs
  split_ifs with h
  · exact h
  · exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)

theorem getD_snoc (L : List Bool) (a : Bool) (i : ℕ) :
    (L ++ [a]).getD i false = if i < L.length then L.getD i false else if i = L.length then a else false := by
  rcases lt_trichotomy i L.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · have h1 : ¬ i < L.length := by omega
    have h2 : i ≠ L.length := by omega
    simp only [h1, h2, ite_false]
    rw [List.getD_eq_default]
    simp; omega

theorem foldl_len (gs : List (Finset ℕ × Finset ℕ)) :
    ∀ L : List Bool, (gs.foldl stp L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; simp
  | cons p gs ih =>
    intro L
    simp only [List.foldl_cons, ih, stp, List.length_append, List.length_cons, List.length_nil]
    omega

theorem foldl_pre (gs : List (Finset ℕ × Finset ℕ)) :
    ∀ (L : List Bool) (i : ℕ), i < L.length → (gs.foldl stp L).getD i false = L.getD i false := by
  induction gs with
  | nil => intro L i h; simp
  | cons p gs ih =>
    intro L i h
    simp only [List.foldl_cons]
    rw [ih _ i (by simp [stp]; omega)]
    simp only [stp, getD_snoc, h, ite_true]

theorem main (n : ℕ) (x : Fin n → Bool) (gs : List (Finset ℕ × Finset ℕ)) :
    (∀ i, ((gs.map (fp n)).foldl stp (List.ofFn x ++ [false])).getD i false = true →
      (gs.foldl stp (List.ofFn x ++ [false])).getD i false = true) ∧
    (({k : Fin n | x k = true} : Finset (Fin n)).card ≤ 2 → ∀ i,
      ((gs.map (fp n)).foldl stp (List.ofFn x ++ [false])).getD i false =
        (gs.foldl stp (List.ofFn x ++ [false])).getD i false) := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs p ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hA : (gs.map (fp n)).foldl stp (List.ofFn x ++ [false]) = A at ih1 ih2
    generalize hB : gs.foldl stp (List.ofFn x ++ [false]) = B at ih1 ih2
    have hlen : A.length = B.length := by
      rw [← hA, ← hB, foldl_len, foldl_len]; simp
    have hAn : A.getD n false = false := by
      rw [← hA, foldl_pre _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    have hBx : ∀ i (h : i < n), B.getD i false = x ⟨i, h⟩ := by
      intro i h
      rw [← hB, foldl_pre _ _ _ (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < (List.ofFn x).length by simp; omega), h]
    have and1 : ∀ S : Finset ℕ, (∀ i ∈ fs n S, A.getD i false = true) → (∀ i ∈ S, B.getD i false = true) := by
      intro S h
      unfold fs at h
      split_ifs at h
      · exact fun i hi => ih1 i (h i hi)
      · have := h n (by simp)
        rw [hAn] at this
        exact absurd this (by simp)
    have and2 : (({k : Fin n | x k = true} : Finset (Fin n)).card ≤ 2) → ∀ S : Finset ℕ,
        ((∀ i ∈ fs n S, A.getD i false = true) ↔ (∀ i ∈ S, B.getD i false = true)) := by
      intro hc S
      unfold fs
      split_ifs with hS
      · exact forall₂_congr (fun i _ => by rw [ih2 hc i])
      · constructor
        · intro h
          have := h n (by simp)
          rw [hAn] at this
          exact absurd this (by simp)
        · intro h
          exfalso
          apply hS
          refine le_trans (Finset.card_le_card (t := ({k : Fin n | x k = true} : Finset (Fin n)).image Fin.val) ?_) (le_trans Finset.card_image_le hc)
          intro i hi
          rw [Finset.mem_filter] at hi
          rw [Finset.mem_image]
          refine ⟨⟨i, hi.2⟩, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← hBx i hi.2]
          exact h i hi.1
    constructor
    · intro i h
      simp only [stp, getD_snoc] at h ⊢
      rw [← hlen]
      split_ifs at h ⊢ with h1 h2
      · exact ih1 i h
      · simp only [Bool.or_eq_true, decide_eq_true_eq] at h ⊢
        rcases h with h | h
        · exact Or.inl (and1 p.1 h)
        · exact Or.inr (and1 p.2 h)
      all_goals try exact h
    · intro hc i
      simp only [stp, getD_snoc]
      rw [← hlen]
      split_ifs with h1 h2
      · exact ih2 hc i
      · rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact or_congr (and2 hc p.1) (and2 hc p.2)
      all_goals try rfl

end PEqualNP.Outside.L_meta_8253

theorem PEqualNP.Outside.L_meta_8253 : ∀ (x1 : ℕ) (x2 : List (Finset ℕ × Finset ℕ)),   have x3 : List (Finset ℕ × Finset ℕ) → (Fin x1 → Bool) → Finset ℕ → Bool := fun (x3 : List (Finset ℕ × Finset ℕ)) (x4 : Fin x1 → Bool) (x5 : Finset ℕ) =>     have x6 : List Bool := List.foldl (fun (x6 : List Bool) (x7 : Finset ℕ × Finset ℕ) => x6 ++ [Decidable.decide (∀ x8 ∈ x7.1, x6.getD x8 Bool.false = Bool.true) || Decidable.decide (∀ x8 ∈ x7.2, x6.getD x8 Bool.false = Bool.true)]) (List.ofFn x4 ++ [Bool.false]) x3;     Decidable.decide (∀ x7 ∈ x5, x6.getD x7 Bool.false = Bool.true);   (∀ (x4 : ℕ) (x5 : x4 < x2.length), ∀ x6 ∈ x2[x4].1 ∪ x2[x4].2, x6 < x1 + (1 : ℕ) + x4) →     ∃ (x5 : List (Finset ℕ × Finset ℕ)),       x5.length = x2.length ∧         (∀ (x6 : ℕ) (x7 : x6 < x5.length), ∀ x8 ∈ x5[x6].1 ∪ x5[x6].2, x8 < x1 + (1 : ℕ) + x6) ∧           (∀ x6 ∈ x5, {x8 ∈ x6.1 | x8 < x1}.card ≤ (2 : ℕ) ∧ {x8 ∈ x6.2 | x8 < x1}.card ≤ (2 : ℕ)) ∧             ∀ (x6 : Fin x1 → Bool) (x7 : Finset ℕ),               ((have x8 : Finset (Fin x1) := {x8 : Fin x1 | x6 x8 = Bool.true};                   x8.card ≤ (2 : ℕ)) →                   x3 x5 x6 x7 = x3 x2 x6 x7) ∧                 (x3 x5 x6 x7 = Bool.true → x3 x2 x6 x7 = Bool.true) := by
  intro x1 x2
  dsimp only
  intro hb
  refine ⟨x2.map (PEqualNP.Outside.L_meta_8253.fp x1), by simp, ?_, ?_, ?_⟩
  · intro i hi j hj
    simp only [List.getElem_map, PEqualNP.Outside.L_meta_8253.fp, Finset.mem_union] at hj
    have hi' : i < x2.length := by simpa using hi
    have key : ∀ S : Finset ℕ, j ∈ PEqualNP.Outside.L_meta_8253.fs x1 S → (j ∈ S ∨ j = x1) := by
      intro S hS
      unfold PEqualNP.Outside.L_meta_8253.fs at hS
      split_ifs at hS
      · exact Or.inl hS
      · exact Or.inr (by simpa using hS)
    rcases hj with hj | hj
    · rcases key _ hj with h | h
      · exact hb i hi' j (Finset.mem_union_left _ h)
      · omega
    · rcases key _ hj with h | h
      · exact hb i hi' j (Finset.mem_union_right _ h)
      · omega
  · intro p hp
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp
    exact ⟨PEqualNP.Outside.L_meta_8253.fs_card x1 _, PEqualNP.Outside.L_meta_8253.fs_card x1 _⟩
  · intro x x7
    obtain ⟨m1, m2⟩ := PEqualNP.Outside.L_meta_8253.main x1 x x2
    refine ⟨fun hc => ?_, fun h => ?_⟩
    · have e := m2 hc
      simp only [decide_eq_decide]
      exact forall₂_congr (fun i _ => Iff.of_eq (congrArg (fun b => b = true) (e i)))
    · simp only [decide_eq_true_eq] at h ⊢
      exact fun i hi => m1 i (h i hi)

