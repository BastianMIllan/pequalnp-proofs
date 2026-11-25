import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7029

def cut {n : ℕ} (f : Fin n → Bool) : Sym2 (Fin n) → Bool :=
  Sym2.lift ⟨fun a b => xor (f a) (f b), fun a b => Bool.xor_comm _ _⟩

theorem cut_mk {n : ℕ} (f : Fin n → Bool) (a b : Fin n) :
    cut f s(a, b) = xor (f a) (f b) := rfl

def flipAt {n : ℕ} (u : Fin n) (f : Fin n → Bool) : Fin n → Bool :=
  Function.update f u (!f u)

theorem flipAt_flipAt {n : ℕ} (u : Fin n) (f : Fin n → Bool) :
    flipAt u (flipAt u f) = f := by
  funext x
  by_cases h : x = u
  · subst h
    simp [flipAt, Function.update_apply]
  · simp [flipAt, Function.update_apply, h]

theorem cut_flipAt {n : ℕ} (u v : Fin n) (huv : u ≠ v) (f : Fin n → Bool) :
    cut (flipAt u f) s(u, v) = !cut f s(u, v) := by
  rw [cut_mk, cut_mk]
  cases hu : f u <;> cases hv : f v <;>
    simp [flipAt, Function.update_apply, huv.symm, hu, hv]

theorem count_cut {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    2 * (Finset.univ.filter (fun f : Fin n → Bool => cut f s(u, v) = true)).card
      = Fintype.card (Fin n → Bool) := by
  have hbij : (Finset.univ.filter (fun f : Fin n → Bool => cut f s(u, v) = true)).card
      = (Finset.univ.filter (fun f : Fin n → Bool => ¬ cut f s(u, v) = true)).card := by
    apply Finset.card_nbij' (flipAt u) (flipAt u)
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and, Set.mem_setOf_eq] at hf ⊢
      rw [cut_flipAt u v huv, hf]
      decide
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and, Set.mem_setOf_eq] at hf ⊢
      rw [cut_flipAt u v huv]
      simpa using hf
    · intro f _
      exact flipAt_flipAt u f
    · intro f _
      exact flipAt_flipAt u f
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n → Bool))) (fun f : Fin n → Bool => cut f s(u, v) = true)
  rw [Finset.card_univ] at h
  omega

theorem main {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (E : Finset (Sym2 (Fin n))) (hE : E ⊆ G.edgeFinset) :
    ∃ f : Fin n → Bool, E.card ≤ 2 * (E.filter (fun e => cut f e = true)).card := by
  have hdiag : ∀ e ∈ E, 2 * (Finset.univ.filter (fun f : Fin n → Bool => cut f e = true)).card
      = Fintype.card (Fin n → Bool) := by
    intro e he
    have hmem := hE he
    rw [SimpleGraph.mem_edgeFinset] at hmem
    induction e using Sym2.ind with
    | h u v =>
      have huv : u ≠ v := G.ne_of_adj ((SimpleGraph.mem_edgeSet G).mp hmem)
      exact count_cut u v huv
  have hsum : ∑ f : Fin n → Bool, 2 * (E.filter (fun e => cut f e = true)).card
      = E.card * Fintype.card (Fin n → Bool) := by
    have h1 : ∀ f : Fin n → Bool, (E.filter (fun e => cut f e = true)).card
        = ∑ e ∈ E, if cut f e = true then 1 else 0 := fun f => Finset.card_filter _ _
    have h2 : ∀ e : Sym2 (Fin n),
        (Finset.univ.filter (fun f : Fin n → Bool => cut f e = true)).card
        = ∑ f : Fin n → Bool, if cut f e = true then 1 else 0 := fun e => Finset.card_filter _ _
    rw [← Finset.mul_sum]
    simp_rw [h1]
    rw [Finset.sum_comm, Finset.mul_sum, Finset.card_eq_sum_ones, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    rw [← h2, hdiag e he, one_mul]
  by_contra hno
  simp only [not_exists, not_le] at hno
  have hlt : ∑ f : Fin n → Bool, 2 * (E.filter (fun e => cut f e = true)).card
      < ∑ _f : Fin n → Bool, E.card :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun f _ => hno f)
  rw [hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] at hlt
  exact lt_irrefl _ hlt

end PEqualNP.Outside.L_meta_7029

theorem PEqualNP.Outside.L_meta_7029 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], ∀ x4 ⊆ x2.edgeFinset, ∃ (x6 : Finset (Sym2 (Fin x1))) (x7 : Fin x1 → Bool), x6 ⊆ x4 ∧ x4.card ≤ (2 : ℕ) * x6.card ∧ ∀ (x8 x9 : Fin x1), s(x8, x9) ∈ x6 → x7 x8 ≠ x7 x9 := by
  intro n G _ E hE
  obtain ⟨f, hf⟩ := PEqualNP.Outside.L_meta_7029.main G E hE
  refine ⟨E.filter (fun e => PEqualNP.Outside.L_meta_7029.cut f e = true), f,
    Finset.filter_subset _ _, hf, ?_⟩
  intro a b hab heq
  rw [Finset.mem_filter, PEqualNP.Outside.L_meta_7029.cut_mk, heq] at hab
  simp at hab
