import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7850

open Finset

-- flip the colour of one vertex
def flipAt {n : ℕ} (a : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  Function.update x a (!x a)

theorem flipAt_flipAt {n : ℕ} (a : Fin n) (x : Fin n → Bool) : flipAt a (flipAt a x) = x := by
  funext i
  by_cases h : i = a
  · subst h
    simp [flipAt, Function.update_self]
  · simp [flipAt, Function.update_of_ne h]

-- exactly half of all colourings separate two distinct vertices
theorem count_ne {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    2 * (univ.filter (fun x : Fin n → Bool => x a ≠ x b)).card = 2 ^ n := by
  have hb : b ≠ a := fun h => hab h.symm
  have h1 : (univ.filter (fun x : Fin n → Bool => x a ≠ x b)).card
      = (univ.filter (fun x : Fin n → Bool => ¬ (x a ≠ x b))).card := by
    refine Finset.card_nbij' (flipAt a) (flipAt a) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
      simp only [flipAt, Function.update_self, Function.update_of_ne hb]
      cases h1 : x a <;> cases h2 : x b <;> simp_all
    · intro x hx
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
      simp only [flipAt, Function.update_self, Function.update_of_ne hb]
      cases h1 : x a <;> cases h2 : x b <;> simp_all
    · intro x _
      exact flipAt_flipAt a x
    · intro x _
      exact flipAt_flipAt a x
  have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n → Bool)))
    (fun x : Fin n → Bool => x a ≠ x b)
  simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h2
  omega

end PEqualNP.Outside.L_meta_7850

theorem PEqualNP.Outside.L_meta_7850 : ∀ (x1 : ℕ) (x2 : Finset (Sym2 (Fin x1))), (∀ x3 ∈ x2, ¬x3.IsDiag) → ∃ (x4 : Fin x1 → Bool), x2.card ≤ (2 : ℕ) * {x5 ∈ x2 | ¬(Sym2.map x4 x5).IsDiag}.card := by
  intro n E hE
  by_contra hcon
  push_neg at hcon
  have key : ∀ e ∈ E,
      2 * (Finset.univ.filter (fun x : Fin n → Bool => ¬(Sym2.map x e).IsDiag)).card = 2 ^ n := by
    intro e he
    have hd := hE e he
    clear he
    induction e using Sym2.ind with
    | h a b =>
      have hab : a ≠ b := by simpa using hd
      have hs : (Finset.univ.filter (fun x : Fin n → Bool => ¬(Sym2.map x s(a, b)).IsDiag))
          = Finset.univ.filter (fun x : Fin n → Bool => x a ≠ x b) := by
        ext x
        simp [Sym2.map_mk]
      rw [hs]
      exact PEqualNP.Outside.L_meta_7850.count_ne a b hab
  have hsum : ∑ x : Fin n → Bool, (E.filter (fun e => ¬(Sym2.map x e).IsDiag)).card
      = ∑ e ∈ E, (Finset.univ.filter (fun x : Fin n → Bool => ¬(Sym2.map x e).IsDiag)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h2 : 2 * ∑ x : Fin n → Bool, (E.filter (fun e => ¬(Sym2.map x e).IsDiag)).card
      = E.card * 2 ^ n := by
    rw [hsum, Finset.mul_sum, Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul]
  have hlt : ∑ x : Fin n → Bool, 2 * (E.filter (fun e => ¬(Sym2.map x e).IsDiag)).card
      < ∑ _x : Fin n → Bool, E.card :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun x _ => hcon x)
  rw [← Finset.mul_sum, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, smul_eq_mul] at hlt
  exact lt_irrefl _ (lt_of_lt_of_eq hlt (mul_comm _ _))
