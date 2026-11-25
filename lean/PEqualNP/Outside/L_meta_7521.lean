import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7521

def Ch (B L : List ℕ) : Prop := ∀ (x3 : Fin L.length), ∃ x4 ∈ B ++ List.take (↑x3) L,
  ∃ x5 ∈ B ++ List.take (↑x3) L, L.get x3 = x4 &&& x5 ∨ L.get x3 = x4 ||| x5

def F (n : ℕ) (x6 : Finset ℕ) (x7 : Bool × ℕ × ℕ) : Finset ℕ :=
  have x8 : ℕ := x7.2.1
  have x9 : ℕ := x7.2.2
  if x8 ∈ x6 ∧ x9 ∈ x6 ∧ x8 ≠ x9 then Insert.insert (if x7.1 = Bool.true then x8 ||| x9 else x8 &&& x9)
    (if n = (8 : ℕ) then (x6.erase x8).erase x9 else x6) else x6

theorem ch_nil (B : List ℕ) : Ch B [] := fun i => absurd i.2 (by simp)

theorem ch_snoc (B acc : List ℕ) (v : ℕ) (h : Ch B acc)
    (hv : ∃ a ∈ B ++ acc, ∃ b ∈ B ++ acc, v = a &&& b ∨ v = a ||| b) : Ch B (acc ++ [v]) := by
  intro i
  have hi : (i : ℕ) < acc.length + 1 := by simpa using i.2
  by_cases hlt : (i : ℕ) < acc.length
  · obtain ⟨a, ha, b, hb, hab⟩ := h ⟨i, hlt⟩
    have ht : List.take (↑i) (acc ++ [v]) = List.take (↑i) acc :=
      List.take_append_of_le_length (by omega)
    have hg : (acc ++ [v]).get i = acc.get ⟨i, hlt⟩ := by
      simp [List.getElem_append_left hlt]
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [ht]; exact ha
    · rw [ht]; exact hb
    · rw [hg]; exact hab
  · have hEq : (i : ℕ) = acc.length := by omega
    have ht : List.take (↑i) (acc ++ [v]) = acc := by rw [hEq]; simp
    have hg : (acc ++ [v]).get i = v := by
      simp [List.getElem_append, hEq]
    obtain ⟨a, ha, b, hb, hab⟩ := hv
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [ht]; exact ha
    · rw [ht]; exact hb
    · rw [hg]; exact hab

theorem gen (n : ℕ) (B : List ℕ) : ∀ (x3 : List (Bool × ℕ × ℕ)) (S : Finset ℕ) (acc : List ℕ),
    Ch B acc → (∀ s ∈ S, s ∈ B ++ acc) →
    ∃ x4 : List ℕ, x4.length ≤ x3.length ∧ Ch B (acc ++ x4) ∧
      ∀ x ∈ x3.foldl (F n) S, x ∈ B ++ (acc ++ x4) := by
  intro x3
  induction x3 with
  | nil =>
    intro S acc hc hs
    exact ⟨[], by simp, by simpa using hc, by simpa using hs⟩
  | cons y ys ih =>
    intro S acc hc hs
    by_cases hcond : y.2.1 ∈ S ∧ y.2.2 ∈ S ∧ y.2.1 ≠ y.2.2
    · have hF : F n S y = insert (if y.1 = true then y.2.1 ||| y.2.2 else y.2.1 &&& y.2.2)
          (if n = 8 then (S.erase y.2.1).erase y.2.2 else S) := by
        simp only [F]; rw [if_pos hcond]
      have hc' : Ch B (acc ++ [if y.1 = true then y.2.1 ||| y.2.2 else y.2.1 &&& y.2.2]) := by
        apply ch_snoc B acc _ hc
        refine ⟨y.2.1, hs _ hcond.1, y.2.2, hs _ hcond.2.1, ?_⟩
        by_cases hb : y.1 = true
        · right; simp [hb]
        · left; simp [hb]
      have hs' : ∀ s ∈ F n S y,
          s ∈ B ++ (acc ++ [if y.1 = true then y.2.1 ||| y.2.2 else y.2.1 &&& y.2.2]) := by
        intro s hsm
        rw [hF, Finset.mem_insert] at hsm
        rcases hsm with hsm | hsm
        · rw [hsm]; simp
        · have hS : s ∈ S := by
            split_ifs at hsm with h8
            · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hsm)
            · exact hsm
          have := hs s hS
          simp only [List.mem_append] at this ⊢
          tauto
      obtain ⟨x4, hl, hch, hm⟩ := ih (F n S y) _ hc' hs'
      refine ⟨(if y.1 = true then y.2.1 ||| y.2.2 else y.2.1 &&& y.2.2) :: x4, ?_, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · simpa [List.append_assoc] using hch
      · intro x hx
        rw [List.foldl_cons] at hx
        have := hm x hx
        simpa [List.append_assoc] using this
    · have hF : F n S y = S := by simp only [F]; rw [if_neg hcond]
      obtain ⟨x4, hl, hch, hm⟩ := ih S acc hc hs
      refine ⟨x4, ?_, hch, ?_⟩
      · simp only [List.length_cons]; omega
      · intro x hx
        rw [List.foldl_cons, hF] at hx
        exact hm x hx

theorem fin : ∀ (x2 : Finset ℕ) (x3 : List (Bool × ℕ × ℕ)), ∃ (x4 : List ℕ),
    x4.length ≤ x3.length ∧ Ch x2.toList x4 ∧
      ∀ x5 ∈ List.foldl (F x2.card) x2 x3, x5 ∈ x2.toList ++ x4 := by
  intro x2 x3
  obtain ⟨x4, hl, hch, hm⟩ := gen x2.card x2.toList x3 x2 [] (ch_nil _)
    (by intro s hs; simpa using hs)
  exact ⟨x4, hl, by simpa using hch, by simpa using hm⟩

end PEqualNP.Outside.L_meta_7521

theorem PEqualNP.Outside.L_meta_7521 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; ∀ (x2 : Finset ℕ) (x3 : List (Bool × ℕ × ℕ)),   ∃ (x4 : List ℕ),     x4.length ≤ x3.length ∧       x1 x2.toList x4 ∧         ∀           x5 ∈             List.foldl               (fun (x6 : Finset ℕ) (x7 : Bool × ℕ × ℕ) =>                 have x8 : ℕ := x7.2.1;                 have x9 : ℕ := x7.2.2;                 if x8 ∈ x6 ∧ x9 ∈ x6 ∧ x8 ≠ x9 then Insert.insert (if x7.1 = Bool.true then x8 ||| x9 else x8 &&& x9) (if x2.card = (8 : ℕ) then (x6.erase x8).erase x9 else x6) else x6)               x2 x3,           x5 ∈ x2.toList ++ x4 := by
  exact PEqualNP.Outside.L_meta_7521.fin
