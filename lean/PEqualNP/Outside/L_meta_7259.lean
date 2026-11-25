import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7259

def I (p l : Fin 13) : Prop :=
  p = l ∨ p = l + (1 : Fin 13) ∨ p = l + (3 : Fin 13) ∨ p = l + (9 : Fin 13)

instance (p l : Fin 13) : Decidable (I p l) := by unfold I; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem key : ∀ a b c d : Fin 13, a < b → b < c → c < d →
    (Finset.univ.filter (fun p : Fin 13 => ¬I p a ∧ ¬I p b ∧ ¬I p c ∧ ¬I p d)).card ≤ 3 := by
  decide +kernel

end PEqualNP.Outside.L_meta_7259

theorem PEqualNP.Outside.L_meta_7259 : ∀ (x1 x2 : Finset (Fin (13 : ℕ))), (∀ x3 ∈ x1, ∀ x5 ∈ x2, ¬(x3 = x5 ∨ x3 = x5 + (1 : Fin (13 : ℕ)) ∨ x3 = x5 + (3 : Fin (13 : ℕ)) ∨ x3 = x5 + (9 : Fin (13 : ℕ)))) → x1.card ≤ (3 : ℕ) ∨ x2.card ≤ (3 : ℕ) := by
  intro x1 x2 h
  by_contra hc
  simp only [not_or, not_le] at hc
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show 4 ≤ x2.card by omega)
  have hs : (t.sort).Pairwise (· < ·) := List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort t)
  have hlen : (t.sort).length = 4 := by rw [Finset.length_sort, htc]
  have hmem : ∀ x, x ∈ t.sort → x ∈ t := fun x hx => by simpa [Finset.mem_sort] using hx
  generalize t.sort = L at hs hlen hmem
  match L, hs, hlen, hmem with
  | [], _, hl, _ => simp at hl
  | [_], _, hl, _ => simp at hl
  | [_, _], _, hl, _ => simp at hl
  | [_, _, _], _, hl, _ => simp at hl
  | _ :: _ :: _ :: _ :: _ :: _, _, hl, _ => simp at hl
  | [a, b, c, d], hs, _, hmem =>
    have hab : a < b := List.rel_of_pairwise_cons hs (by simp)
    have hbc : b < c := List.rel_of_pairwise_cons hs.of_cons (by simp)
    have hcd : c < d := List.rel_of_pairwise_cons hs.of_cons.of_cons (by simp)
    have hk := PEqualNP.Outside.L_meta_7259.key a b c d hab hbc hcd
    have ha : a ∈ x2 := hts (hmem a (by simp))
    have hb : b ∈ x2 := hts (hmem b (by simp))
    have hc' : c ∈ x2 := hts (hmem c (by simp))
    have hd : d ∈ x2 := hts (hmem d (by simp))
    have hsub : x1 ⊆ Finset.univ.filter (fun p : Fin 13 =>
        ¬PEqualNP.Outside.L_meta_7259.I p a ∧ ¬PEqualNP.Outside.L_meta_7259.I p b ∧
        ¬PEqualNP.Outside.L_meta_7259.I p c ∧ ¬PEqualNP.Outside.L_meta_7259.I p d) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h p hp a ha, h p hp b hb, h p hp c hc', h p hp d hd⟩
    have := Finset.card_le_card hsub
    omega
