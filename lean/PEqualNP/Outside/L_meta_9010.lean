import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9010

open PEqualNP.HeptadCover

def E : Fin 4 → Fin 13 := ![0, 1, 3, 9]

abbrev inS (a l : Fin 13) : Prop := ∃ e : Fin 4, a = l + E e

lemma memS : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ inS p l := by decide

lemma onLine : ∀ x : Fin 13, ∀ d : Fin 4, x ∈ singerLines3 (x - E d) := by decide

lemma shiftS : ∀ p l x : Fin 13, p + x ∈ singerLines3 (l + x) ↔ p ∈ singerLines3 l := by decide

abbrev T (a b c l : Fin 13) : Prop := a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ inS a l ∧ inS b l ∧ inS c l

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
lemma C0 : ∀ e0 e1 e2 e3 : Fin 4, -E 0 + E e0 ≠ 0 → -E 1 + E e1 ≠ 0 → -E 2 + E e2 ≠ 0 →
    -E 3 + E e3 ≠ 0 → ∃ l : Fin 13,
      T (-E 0 + E e0) (-E 1 + E e1) (-E 2 + E e2) l ∨
      T (-E 0 + E e0) (-E 1 + E e1) (-E 3 + E e3) l ∨
      T (-E 0 + E e0) (-E 2 + E e2) (-E 3 + E e3) l ∨
      T (-E 1 + E e1) (-E 2 + E e2) (-E 3 + E e3) l := by
  delta T inS
  decide +kernel

lemma close (Q : Finset (Fin 13)) (hl : ∀ l : Fin 13, (Q ∩ singerLines3 l).card ≤ 2)
    (x l a b c : Fin 13) (hT : T a b c l) (qa : a + x ∈ Q) (qb : b + x ∈ Q) (qc : c + x ∈ Q) :
    False := by
  obtain ⟨ab, ac, bc, ha, hb, hc⟩ := hT
  have ma : a + x ∈ Q ∩ singerLines3 (l + x) :=
    Finset.mem_inter.2 ⟨qa, (shiftS _ _ _).2 ((memS _ _).2 ha)⟩
  have mb : b + x ∈ Q ∩ singerLines3 (l + x) :=
    Finset.mem_inter.2 ⟨qb, (shiftS _ _ _).2 ((memS _ _).2 hb)⟩
  have mc : c + x ∈ Q ∩ singerLines3 (l + x) :=
    Finset.mem_inter.2 ⟨qc, (shiftS _ _ _).2 ((memS _ _).2 hc)⟩
  have sub : ({a + x, b + x, c + x} : Finset (Fin 13)) ⊆ Q ∩ singerLines3 (l + x) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact ma
    · exact mb
    · exact mc
  have h3 : ({a + x, b + x, c + x} : Finset (Fin 13)).card = 3 :=
    Finset.card_eq_three.2 ⟨_, _, _, by simpa using ab, by simpa using ac, by simpa using bc, rfl⟩
  have h4 := Finset.card_le_card sub
  have h5 := hl (l + x)
  omega

end PEqualNP.Outside.L_meta_9010

open PEqualNP.Outside.L_meta_9010 in
theorem PEqualNP.Outside.L_meta_9010 : ∀ x1 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, ∀ x3 ∉ x1, ∃ x5 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1, x3 ∈ PEqualNP.HeptadCover.singerLines3 x5 := by
  intro Q hQ x hx
  simp only [PEqualNP.HeptadCover.quadrangles, Finset.mem_filter, Finset.mem_powersetCard] at hQ
  obtain ⟨_, hl⟩ := hQ
  by_contra H
  have key : ∀ d : Fin 4, ∃ e : Fin 4, x - E d + E e ∈ Q := by
    intro d
    have h1 : (x - E d) ∉ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q :=
      fun hm => H ⟨_, hm, onLine x d⟩
    simp only [PEqualNP.HeptadCover.missLines, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.not_disjoint_iff] at h1
    obtain ⟨p, hp1, hp2⟩ := h1
    obtain ⟨e, rfl⟩ := (memS p _).1 hp1
    exact ⟨e, hp2⟩
  have hq : ∀ d e : Fin 4, x - E d + E e = (-E d + E e) + x := by intros; abel
  have nz : ∀ d e : Fin 4, (-E d + E e) + x ∈ Q → -E d + E e ≠ 0 := by
    intro d e h hz
    rw [hz, zero_add] at h
    exact hx h
  obtain ⟨e0, h0⟩ := key 0
  obtain ⟨e1, h1⟩ := key 1
  obtain ⟨e2, h2⟩ := key 2
  obtain ⟨e3, h3⟩ := key 3
  rw [hq] at h0 h1 h2 h3
  obtain ⟨l, hT⟩ := C0 e0 e1 e2 e3 (nz _ _ h0) (nz _ _ h1) (nz _ _ h2) (nz _ _ h3)
  rcases hT with hT | hT | hT | hT
  · exact close Q hl x l _ _ _ hT h0 h1 h2
  · exact close Q hl x l _ _ _ hT h0 h1 h3
  · exact close Q hl x l _ _ _ hT h0 h2 h3
  · exact close Q hl x l _ _ _ hT h1 h2 h3
