import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8051

def adj (i r : Fin 21) : Prop :=
  (21 + r.val + 21 - i.val) % 21 ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]

instance (i r : Fin 21) : Decidable (adj i r) := by unfold adj; infer_instance

def line (r : Fin 21) : Finset (Fin 21) := Finset.univ.filter (fun i => adj i r)

theorem line_card (r : Fin 21) : (line r).card = 5 := by
  revert r; decide

theorem line_inter (r s : Fin 21) (h : r ≠ s) : (line r ∩ line s).card ≤ 1 := by
  revert r s; decide

theorem union_bound : ∀ (R : Finset (Fin 21)),
    11 * R.card ≤ 2 * (R.biUnion line).card + R.card * R.card := by
  intro R
  induction R using Finset.induction_on with
  | empty => simp
  | @insert r R hr ih =>
    have hU : (R.biUnion line).card + 5 ≤ ((insert r R).biUnion line).card + R.card := by
      rw [Finset.biUnion_insert]
      have h1 := Finset.card_union_add_card_inter (line r) (R.biUnion line)
      have h2 : (line r ∩ R.biUnion line).card ≤ R.card := by
        rw [Finset.inter_biUnion]
        calc (R.biUnion fun s => line r ∩ line s).card
            ≤ ∑ s ∈ R, (line r ∩ line s).card := Finset.card_biUnion_le
          _ ≤ ∑ s ∈ R, 1 := by
              apply Finset.sum_le_sum
              intro s hs
              exact line_inter r s (fun e => hr (e ▸ hs))
          _ = R.card := by simp
      rw [line_card] at h1
      omega
    rw [Finset.card_insert_of_notMem hr]
    nlinarith [ih, hU]

theorem countP_card (p : Fin 21 → Bool) :
    List.countP p (List.finRange 21) = (Finset.univ.filter (fun i => p i = true)).card := by
  rw [Fin.univ_def, List.countP_eq_length_filter]
  rfl

end PEqualNP.Outside.L_meta_8051

theorem PEqualNP.Outside.L_meta_8051 : have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : (Fin (42 : ℕ) → Bool) → Prop := fun (x2 : Fin (42 : ℕ) → Bool) => ∃ (x3 : Fin (42 : ℕ)) (x4 : Fin (42 : ℕ)), x1 x3 x4 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (42 : ℕ) → Bool) → Prop := fun (x3 : Fin (42 : ℕ) → Bool) => List.countP (fun (x4 : Fin (21 : ℕ)) => x3 (Fin.castAdd (21 : ℕ) x4)) (List.finRange (21 : ℕ)) ≤ (6 : ℕ) ∨ List.countP (fun (x4 : Fin (21 : ℕ)) => x3 (Fin.natAdd (21 : ℕ) x4)) (List.finRange (21 : ℕ)) ≤ (5 : ℕ); ∀ (x4 : Fin (42 : ℕ) → Bool), ¬x2 x4 → x3 x4 := by
  intro x1 x2 x3 x4 h
  show List.countP (fun y : Fin 21 => x4 (Fin.castAdd 21 y)) (List.finRange 21) ≤ 6 ∨
    List.countP (fun y : Fin 21 => x4 (Fin.natAdd 21 y)) (List.finRange 21) ≤ 5
  rw [PEqualNP.Outside.L_meta_8051.countP_card, PEqualNP.Outside.L_meta_8051.countP_card]
  by_contra hc
  push_neg at hc
  obtain ⟨R', hR'sub, hR'card⟩ := Finset.exists_subset_card_eq (show 6 ≤
    (Finset.univ.filter (fun y : Fin 21 => x4 (Fin.natAdd 21 y) = true)).card by omega)
  have hb := PEqualNP.Outside.L_meta_8051.union_bound R'
  rw [hR'card] at hb
  have hdisj : Disjoint (Finset.univ.filter (fun y : Fin 21 => x4 (Fin.castAdd 21 y) = true))
      (R'.biUnion PEqualNP.Outside.L_meta_8051.line) := by
    rw [Finset.disjoint_left]
    intro i hiL hiU
    obtain ⟨r, hr, hir⟩ := Finset.mem_biUnion.mp hiU
    apply h
    refine ⟨Fin.castAdd 21 i, Fin.natAdd 21 r, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · simp
    · simp
    · have := (Finset.mem_filter.mp hir).2
      simp only [PEqualNP.Outside.L_meta_8051.adj] at this
      simp only [Fin.coe_natAdd, Fin.coe_castAdd]
      exact this
    · exact (Finset.mem_filter.mp hiL).2
    · exact (Finset.mem_filter.mp (hR'sub hr)).2
  have h1 := Finset.card_union_of_disjoint hdisj
  have h2 := Finset.card_le_univ ((Finset.univ.filter (fun y : Fin 21 => x4 (Fin.castAdd 21 y) = true)) ∪
      R'.biUnion PEqualNP.Outside.L_meta_8051.line)
  simp only [Fintype.card_fin] at h2
  omega
