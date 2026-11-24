import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3328

def P (L : List ℕ) (v : ℕ) : Prop := ∃ a ∈ L, ∃ b ∈ L, v = a &&& b ∨ v = a ||| b

def Good (base L : List ℕ) : Prop := ∀ i : Fin L.length, P (base ++ L.take i) (L.get i)

theorem P_mono {A B : List ℕ} {v : ℕ} (h : ∀ y ∈ A, y ∈ B) (hp : P A v) : P B v := by
  obtain ⟨a, ha, b, hb, h'⟩ := hp
  exact ⟨a, h a ha, b, h b hb, h'⟩

theorem good_snoc (base L : List ℕ) (v : ℕ) :
    Good base (L ++ [v]) ↔ Good base L ∧ P (base ++ L) v := by
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · obtain ⟨k, hk⟩ := i
      have := h ⟨k, by simp; omega⟩
      simp only [List.get_eq_getElem] at this ⊢
      rw [List.take_append_of_le_length (by omega), List.getElem_append_left hk] at this
      exact this
    · have := h ⟨L.length, by simp⟩
      simpa using this
  · rintro ⟨h1, h2⟩ ⟨k, hk⟩
    simp only [List.get_eq_getElem]
    have hk' := hk
    simp only [List.length_append, List.length_singleton] at hk'
    rcases Nat.lt_or_ge k L.length with hlt | hge
    · rw [List.take_append_of_le_length (by omega), List.getElem_append_left hlt]
      have := h1 ⟨k, hlt⟩
      simpa using this
    · have heq : k = L.length := by omega
      subst heq
      simpa using h2

theorem good_of (base L : List ℕ) (a : ℕ) (ha : P base a)
    (hL : ∀ i : Fin L.length, P ((a :: base) ++ L.take i) (L.get i)) : Good base (a :: L) := by
  intro ⟨k, hk⟩
  cases k with
  | zero => simpa using ha
  | succ k =>
    have := hL ⟨k, by simpa using hk⟩
    simp only [List.get_eq_getElem, List.take_succ_cons, List.getElem_cons_succ] at this ⊢
    refine P_mono ?_ this
    intro y hy
    simp only [List.mem_append, List.mem_cons] at hy ⊢
    tauto

theorem dedup (base : List ℕ) : ∀ S : List ℕ, Good base S → ∃ K : List ℕ,
    K.length ≤ S.length ∧ K.Nodup ∧ (∀ y ∈ K, y ∉ base) ∧
    (∀ y, y ∈ base ++ K ↔ y ∈ base ++ S) ∧ Good base K := by
  intro S
  induction S using List.reverseRecOn with
  | nil =>
    intro _
    exact ⟨[], by simp, List.nodup_nil, by simp, fun y => Iff.rfl,
      fun i => absurd i.2 (by simp)⟩
  | append_singleton S v ih =>
    intro h
    rw [good_snoc] at h
    obtain ⟨K, hlen, hnd, hnb, hmem, hg⟩ := ih h.1
    by_cases hv : v ∈ base ++ K
    · refine ⟨K, by simp; omega, hnd, hnb, fun y => ?_, hg⟩
      have hv' := (hmem v).1 hv
      rw [hmem]
      simp only [List.mem_append, List.mem_singleton] at hv' ⊢
      constructor
      · tauto
      · intro hy
        rcases hy with hy | hy | rfl
        · exact Or.inl hy
        · exact Or.inr hy
        · exact hv'
    · have hvb : v ∉ base := fun h => hv (List.mem_append_left _ h)
      have hvK : v ∉ K := fun h => hv (List.mem_append_right _ h)
      refine ⟨K ++ [v], by simp; omega, ?_, ?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton v, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        intro hab
        subst hab
        exact hvK ha
      · intro y hy
        simp only [List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | hy
        · exact hnb y hy
        · subst hy; exact hvb
      · intro y
        have := hmem y
        simp only [List.mem_append, List.mem_singleton] at this ⊢
        tauto
      · rw [good_snoc]
        refine ⟨hg, P_mono ?_ h.2⟩
        intro y hy
        exact (hmem y).2 hy

theorem final (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ) (h1 : x5 ∉ x3) (h2 : P x3 x4)
    (h3 : Good (x4 :: x3) x6) (h4 : P (x4 :: x3 ++ x6) x5) :
    ∃ x11 : List ℕ, x11.length ≤ x6.length + 2 ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧
      x5 ∈ x11 ∧ Good x3 x11 := by
  have hS : Good x3 ((x4 :: x6) ++ [x5]) := by
    rw [good_snoc]
    refine ⟨good_of x3 x6 x4 h2 h3, P_mono ?_ h4⟩
    intro y hy
    simp only [List.mem_append, List.mem_cons] at hy ⊢
    tauto
  obtain ⟨K, hlen, hnd, hnb, hmem, hg⟩ := dedup x3 _ hS
  refine ⟨K, by simp at hlen; omega, hnd, hnb, ?_, hg⟩
  have := (hmem x5).2 (by simp)
  simp only [List.mem_append] at this
  rcases this with h | h
  · exact absurd h h1
  · exact h

end PEqualNP.Outside.L_meta_3328

theorem PEqualNP.Outside.L_meta_3328 : have x1 : List ℕ → ℕ → Prop := fun (x1 : List ℕ) (x2 : ℕ) => ∃ x3 ∈ x1, ∃ x4 ∈ x1, x2 = x3 &&& x4 ∨ x2 = x3 ||| x4; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), x1 (x2 ++ List.take (↑x4) x3) (x3.get x4); ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x5 ∉ x3 → x1 x3 x4 → x2 (x4 :: x3) x6 → x1 (x4 :: x3 ++ x6) x5 → ∃ (x11 : List ℕ), x11.length ≤ x6.length + (2 : ℕ) ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧ x5 ∈ x11 ∧ x2 x3 x11 := by
  intro x1 x2 x3 x4 x5 x6 h1 h2 h3 h4
  exact PEqualNP.Outside.L_meta_3328.final x3 x4 x5 x6 h1 h2 h3 h4
