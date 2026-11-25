import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7414

def F (S : Finset ℕ) (t : ℕ × ℕ × ℕ) : Finset ℕ := insert t.2.1 (insert t.2.2 (S.erase t.1))

def Valid (S : Finset ℕ) (L : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ k : Fin L.length, (L.get k).1 ∈ List.foldl F S (L.take k) ∧
    ((L.get k).1 = (L.get k).2.1 &&& (L.get k).2.2 ∨ (L.get k).1 = (L.get k).2.1 ||| (L.get k).2.2)

def Builds (X Y : List ℕ) : Prop :=
  ∀ k : Fin Y.length, ∃ u ∈ X ++ Y.take k, ∃ v ∈ X ++ Y.take k, Y.get k = u &&& v ∨ Y.get k = u ||| v

theorem valid_cons {S : Finset ℕ} {t : ℕ × ℕ × ℕ} {L : List (ℕ × ℕ × ℕ)} (h : Valid S (t :: L)) :
    (t.1 ∈ S ∧ (t.1 = t.2.1 &&& t.2.2 ∨ t.1 = t.2.1 ||| t.2.2)) ∧ Valid (F S t) L := by
  refine ⟨?_, ?_⟩
  · have := h ⟨0, by simp⟩
    simpa using this
  · intro k
    have := h ⟨k.1 + 1, by simp⟩
    simpa [List.take_succ_cons] using this

theorem builds_snoc {X Y : List ℕ} {a : ℕ} (hY : Builds X Y)
    (ha : ∃ u ∈ X ++ Y, ∃ v ∈ X ++ Y, a = u &&& v ∨ a = u ||| v) : Builds X (Y ++ [a]) := by
  intro k
  rcases k with ⟨k, hk⟩
  simp only [List.length_append, List.length_singleton] at hk
  by_cases h : k < Y.length
  · have := hY ⟨k, h⟩
    simp only [List.get_eq_getElem] at this ⊢
    rw [List.getElem_append_left h, List.take_append_of_le_length h.le]
    exact this
  · have hk' : k = Y.length := by omega
    subst hk'
    simpa using ha

theorem key (X : List ℕ) : ∀ (L : List (ℕ × ℕ × ℕ)) (S : Finset ℕ), Valid S L →
    (∀ e ∈ List.foldl F S L, e ∈ X) → (List.foldl F S L).card ≤ S.card + L.length ∧
    ∃ Y : List ℕ, Y.length ≤ L.length ∧ Builds X Y ∧ ∀ e ∈ S, e ∈ X ++ Y := by
  intro L
  induction L with
  | nil =>
    intro S _ hX
    refine ⟨by simp, [], by simp, ?_, ?_⟩
    · intro k
      exact k.elim0
    · intro e he
      simpa using hX e (by simpa using he)
  | cons t L ih =>
    intro S hV hX
    obtain ⟨⟨ha, hop⟩, hV'⟩ := valid_cons hV
    rw [List.foldl_cons] at hX ⊢
    obtain ⟨hcard, Y, hYlen, hYb, hYS⟩ := ih (F S t) hV' hX
    refine ⟨?_, Y ++ [t.1], ?_, ?_, ?_⟩
    · have h1 := Finset.card_insert_le t.2.1 (insert t.2.2 (S.erase t.1))
      have h2 := Finset.card_insert_le t.2.2 (S.erase t.1)
      have h3 := Finset.card_erase_of_mem ha
      have h4 := Finset.card_pos.mpr ⟨_, ha⟩
      have h5 : (F S t).card ≤ S.card + 1 := by
        unfold F
        omega
      simp only [List.length_cons]
      omega
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · apply builds_snoc hYb
      exact ⟨t.2.1, hYS _ (by simp [F]), t.2.2, hYS _ (by simp [F]), hop⟩
    · intro e he
      by_cases h : e = t.1
      · subst h
        simp
      · have hm : e ∈ F S t := by simp [F, Finset.mem_erase, h, he]
        have := hYS e hm
        simp only [List.mem_append, List.mem_singleton] at this ⊢
        tauto

end PEqualNP.Outside.L_meta_7414

theorem PEqualNP.Outside.L_meta_7414 : have x1 : Finset ℕ → ℕ × ℕ × ℕ → Finset ℕ := fun (x1 : Finset ℕ) (x2 : ℕ × ℕ × ℕ) => Insert.insert x2.2.1 (Insert.insert x2.2.2 (x1.erase x2.1)); have x2 : Finset ℕ → List (ℕ × ℕ × ℕ) → Prop := fun (x2 : Finset ℕ) (x3 : List (ℕ × ℕ × ℕ)) =>   ∀ (x4 : Fin x3.length),     have x5 : ℕ × ℕ × ℕ := x3.get x4;     x5.1 ∈ List.foldl x1 x2 (List.take (↑x4) x3) ∧ (x5.1 = x5.2.1 &&& x5.2.2 ∨ x5.1 = x5.2.1 ||| x5.2.2); have x3 : List ℕ → List ℕ → Prop := fun (x3 x4 : List ℕ) => ∀ (x5 : Fin x4.length), ∃ x6 ∈ x3 ++ List.take (↑x5) x4, ∃ x7 ∈ x3 ++ List.take (↑x5) x4, x4.get x5 = x6 &&& x7 ∨ x4.get x5 = x6 ||| x7; ∀ (x4 : List ℕ) (x5 : Finset ℕ) (x6 : List (ℕ × ℕ × ℕ)), x2 x5 x6 → (∀ x8 ∈ List.foldl x1 x5 x6, x8 ∈ x4) → (List.foldl x1 x5 x6).card ≤ x5.card + x6.length ∧ ∃ (x9 : List ℕ), x9.length ≤ x6.length ∧ x3 x4 x9 ∧ ∀ x10 ∈ x5, x10 ∈ x4 ++ x9 := by
  intro x1 x2 x3 X S L hV hX
  exact PEqualNP.Outside.L_meta_7414.key X L S hV hX
