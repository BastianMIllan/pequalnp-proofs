import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6824

def D : Finset (Fin 13) := {0, 1, 3, 9}

def inc (p l : Fin 13) : Prop := p - l ∈ D

instance : DecidableRel inc := fun p l => by unfold inc; infer_instance

def av (S : Finset (Fin 13)) (l : Fin 13) : Prop := ∀ p ∈ S, ¬ inc p l

instance (S : Finset (Fin 13)) : DecidablePred (av S) := fun l => by unfold av; infer_instance

def Cl (S : Finset (Fin 13)) : Prop := ∀ q ∉ S, ∃ l, av S l ∧ inc q l

instance (S : Finset (Fin 13)) : Decidable (Cl S) := by unfold Cl; infer_instance

def Sz (S : Finset (Fin 13)) : Prop :=
  S.card ≤ 2 ∨ (Finset.univ.filter (av S)).card ≤ 2 ∨ (S.card = 3 ∧ ∃ l, ∀ p ∈ S, inc p l)

instance (S : Finset (Fin 13)) : Decidable (Sz S) := by unfold Sz; infer_instance

def off (Y : Finset (Fin 13)) : Finset (Fin 13) := Finset.univ.filter fun p => ∀ l ∈ Y, ¬ inc p l

def onb (L : Fin 13) (b0 b1 b2 b3 : Bool) : Finset (Fin 13) :=
  Finset.univ.filter fun p => (b0 = true ∧ p = L) ∨ (b1 = true ∧ p = L + 1) ∨
    (b2 = true ∧ p = L + 3) ∨ (b3 = true ∧ p = L + 9)

def offb (P : Fin 13) (b0 b1 b2 b3 : Bool) : Finset (Fin 13) :=
  Finset.univ.filter fun p => (b0 = true → ¬ inc p P) ∧ (b1 = true → ¬ inc p (P - 1)) ∧
    (b2 = true → ¬ inc p (P - 3)) ∧ (b3 = true → ¬ inc p (P - 9))

theorem ln : ∀ p L : Fin 13, inc p L ↔ p = L ∨ p = L + 1 ∨ p = L + 3 ∨ p = L + 9 := by
  decide +kernel

theorem pn : ∀ P l : Fin 13, inc P l ↔ l = P ∨ l = P - 1 ∨ l = P - 3 ∨ l = P - 9 := by
  decide +kernel

theorem c1 : ∀ L : Fin 13, ∀ b0 b1 b2 b3 : Bool, (onb L b0 b1 b2 b3).card ≤ 3 →
    Cl (onb L b0 b1 b2 b3) ∧ Sz (onb L b0 b1 b2 b3) := by
  decide +kernel

theorem c1b : ∀ L : Fin 13, ∀ b0 b1 b2 b3 : Bool, 4 ≤ (onb L b0 b1 b2 b3).card →
    ∀ l, ∃ p ∈ onb L b0 b1 b2 b3, inc p l := by
  decide +kernel

theorem c2 : ∀ P : Fin 13, ∀ b0 b1 b2 b3 : Bool, Sz (offb P b0 b1 b2 b3) := by
  decide +kernel

theorem cu : Cl Finset.univ ∧ Sz Finset.univ := by
  decide +kernel

theorem onb_eq (L : Fin 13) (A : Finset (Fin 13)) (hA : ∀ p ∈ A, inc p L) :
    A = onb L (decide (L ∈ A)) (decide (L + 1 ∈ A)) (decide (L + 3 ∈ A)) (decide (L + 9 ∈ A)) := by
  ext p
  simp only [onb, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  constructor
  · intro hp
    rcases (ln p L).1 (hA p hp) with h | h | h | h <;> subst h <;> simp [hp]
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩) <;> exact h

theorem off_eq (P : Fin 13) (Y : Finset (Fin 13)) (hY : ∀ l ∈ Y, inc P l) :
    off Y = offb P (decide (P ∈ Y)) (decide (P - 1 ∈ Y)) (decide (P - 3 ∈ Y)) (decide (P - 9 ∈ Y)) := by
  ext p
  simp only [off, offb, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨h _, h _, h _, h _⟩
  · rintro ⟨h0, h1, h2, h3⟩ l hl
    rcases (pn P l).1 (hY l hl) with h | h | h | h <;> subst h
    exacts [h0 hl, h1 hl, h2 hl, h3 hl]

theorem off_cl (Y : Finset (Fin 13)) : Cl (off Y) := by
  intro q hq
  simp only [off, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hq
  obtain ⟨l, hl, hql⟩ := hq
  refine ⟨l, ?_, hql⟩
  intro p hp
  simp only [off, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  exact hp l hl

theorem nc (S : Finset (Fin 13)) :
    Nat.card {x : Fin 13 // av S x} = (Finset.univ.filter (av S)).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem fz (S : Finset (Fin 13)) (h1 : Cl S) (h2 : Sz S) :
    (∀ q ∉ S, ∃ l, av S l ∧ inc q l) ∧
    (S.card ≤ 2 ∨ Nat.card {x : Fin 13 // av S x} ≤ 2 ∨ (S.card = 3 ∧ ∃ l, ∀ p ∈ S, inc p l)) := by
  refine ⟨h1, ?_⟩
  rw [nc]
  exact h2

theorem main (A B : Finset (Fin 13)) (hd : ∀ p ∈ A, ∀ l ∈ B, ¬ inc p l)
    (hc : (∃ L, ∀ p ∈ A, inc p L) ∨ ∃ P, ∀ l ∈ B, inc P l) :
    ∃ S : Finset (Fin 13), ((∀ q ∉ S, ∃ l, av S l ∧ inc q l) ∧
      (S.card ≤ 2 ∨ Nat.card {x : Fin 13 // av S x} ≤ 2 ∨ (S.card = 3 ∧ ∃ l, ∀ p ∈ S, inc p l))) ∧
      A ⊆ S ∧ ∀ l ∈ B, av S l := by
  rcases hc with ⟨L, hL⟩ | ⟨P, hP⟩
  · have he := onb_eq L A hL
    by_cases h : A.card ≤ 3
    · have hh := c1 L _ _ _ _ (he ▸ h)
      rw [← he] at hh
      exact ⟨A, fz A hh.1 hh.2, Finset.Subset.refl A, fun l hl p hp => hd p hp l hl⟩
    · refine ⟨Finset.univ, fz _ cu.1 cu.2, Finset.subset_univ A, ?_⟩
      intro l hl
      exfalso
      have h4 : 4 ≤ A.card := by omega
      obtain ⟨p, hp, hpl⟩ := c1b L _ _ _ _ (he ▸ h4) l
      rw [← he] at hp
      exact hd p hp l hl hpl
  · have hs := c2 P (decide (P ∈ B)) (decide (P - 1 ∈ B)) (decide (P - 3 ∈ B)) (decide (P - 9 ∈ B))
    rw [← off_eq P B hP] at hs
    refine ⟨off B, fz _ (off_cl B) hs, ?_, ?_⟩
    · intro p hp
      simp only [off, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun l hl => hd p hp l hl
    · intro l hl p hp
      simp only [off, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact hp l hl

end PEqualNP.Outside.L_meta_6824

open PEqualNP.Outside.L_meta_6824 in
theorem PEqualNP.Outside.L_meta_6824 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => x2 - x3 ∈ x1; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; ∀ (x4 x5 : Finset (Fin (13 : ℕ))), (∀ x6 ∈ x4, ∀ x8 ∈ x5, ¬x2 x6 x8) → ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x4, x2 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x2 x7 x8) → ∃ (x8 : Finset (Fin (13 : ℕ))), (∀ x9 ∉ x8, ∃ (x11 : Fin (13 : ℕ)), x3 x8 x11 ∧ x2 x9 x11) ∧ (x8.card ≤ (2 : ℕ) ∨ Nat.card { x9 : Fin (13 : ℕ) // x3 x8 x9 } ≤ (2 : ℕ) ∨ x8.card = (3 : ℕ) ∧ ∃ (x9 : Fin (13 : ℕ)), ∀ x10 ∈ x8, x2 x10 x9) ∧ x4 ⊆ x8 ∧ ∀ x9 ∈ x5, x3 x8 x9 := by
  intro x1 x2 x3 A B hd hc
  obtain ⟨S, ⟨h1, h2⟩, h3, h4⟩ := main A B hd hc
  exact ⟨S, h1, h2, h3, h4⟩
