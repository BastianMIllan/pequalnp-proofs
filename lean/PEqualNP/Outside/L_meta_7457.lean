import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7457

def F (x8 : List (BitVec 59)) (x9 : Bool × Fin 40 × Fin 40) : List (BitVec 59) :=
  x8 ++ [if x9.1 = true then x8.getD x9.2.1 0 ||| x8.getD x9.2.2 0
    else x8.getD x9.2.1 0 &&& x8.getD x9.2.2 0]

theorem foldl_prefix : ∀ (l : List (Bool × Fin 40 × Fin 40)) (S : List (BitVec 59)) (j : ℕ),
    j < S.length → (l.foldl F S).getD j 0 = S.getD j 0
  | [], S, j, _ => rfl
  | e :: l, S, j, h => by
    rw [List.foldl_cons, foldl_prefix l _ j (by simp [F]; omega)]
    simp only [F]
    rw [List.getD_append _ _ _ _ h]

end PEqualNP.Outside.L_meta_7457

theorem PEqualNP.Outside.L_meta_7457 : ∀ (x1 x2 : List (BitVec (59 : ℕ))), x1.length = (14 : ℕ) → x2.length ≤ (25 : ℕ) → (∀ (x5 : Fin x2.length), ∃ x6 ∈ x1 ++ List.take (↑x5) x2, ∃ x7 ∈ x1 ++ List.take (↑x5) x2, x2.get x5 = x6 &&& x7 ∨ x2.get x5 = x6 ||| x7) → ∃ (x6 : List (Bool × Fin (40 : ℕ) × Fin (40 : ℕ))), x6.length = (25 : ℕ) ∧ ∀ (x7 : Fin x2.length), (List.foldl (fun (x8 : List (BitVec (59 : ℕ))) (x9 : Bool × Fin (40 : ℕ) × Fin (40 : ℕ)) => x8 ++ [if x9.1 = Bool.true then x8.getD ↑x9.2.1 (0 : BitVec (59 : ℕ)) ||| x8.getD ↑x9.2.2 (0 : BitVec (59 : ℕ)) else x8.getD ↑x9.2.1 (0 : BitVec (59 : ℕ)) &&& x8.getD ↑x9.2.2 (0 : BitVec (59 : ℕ))]) x1 x6).getD ((14 : ℕ) + ↑x7) (0 : BitVec (59 : ℕ)) = x2.get x7 := by
  intro x1 x2 h1 h2 h3
  show ∃ x6 : List (Bool × Fin 40 × Fin 40), x6.length = 25 ∧ ∀ x7 : Fin x2.length,
    (List.foldl PEqualNP.Outside.L_meta_7457.F x1 x6).getD (14 + ↑x7) 0 = x2.get x7
  have key : ∀ i : Fin x2.length, ∃ (o : Bool) (a b : Fin 40), a.val < 14 + i.val ∧
      b.val < 14 + i.val ∧ x2.get i = (if o = true then
        (x1 ++ x2.take i).getD a 0 ||| (x1 ++ x2.take i).getD b 0 else
        (x1 ++ x2.take i).getD a 0 &&& (x1 ++ x2.take i).getD b 0) := by
    intro i
    obtain ⟨u, hu, v, hv, huv⟩ := h3 i
    have hlen : (x1 ++ x2.take i).length = 14 + i.val := by
      simp only [List.length_append, List.length_take, h1]; have := i.isLt; omega
    obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.1 hu
    obtain ⟨b, hb, rfl⟩ := List.mem_iff_getElem.1 hv
    have i25 : i.val < 25 := by have := i.isLt; omega
    have ea : (x1 ++ x2.take i).getD a 0 = (x1 ++ x2.take i)[a] := List.getD_eq_getElem _ _ ha
    have eb : (x1 ++ x2.take i).getD b 0 = (x1 ++ x2.take i)[b] := List.getD_eq_getElem _ _ hb
    rcases huv with e | e
    · exact ⟨false, ⟨a, by omega⟩, ⟨b, by omega⟩, by simp only; omega, by simp only; omega,
        by simp only [ea, eb, e]; rfl⟩
    · exact ⟨true, ⟨a, by omega⟩, ⟨b, by omega⟩, by simp only; omega, by simp only; omega,
        by simp only [ea, eb, e]; rfl⟩
  choose o a b ha hb hv using key
  refine ⟨(List.range x2.length).map (fun m => if hm : m < x2.length then
      (o ⟨m, hm⟩, a ⟨m, hm⟩, b ⟨m, hm⟩) else (false, 0, 0)) ++
      List.replicate (25 - x2.length) (false, 0, 0), ?_, ?_⟩
  · simp only [List.length_append, List.length_map, List.length_range, List.length_replicate]
    omega
  · intro i
    have ind : ∀ m ≤ x2.length, List.foldl PEqualNP.Outside.L_meta_7457.F x1
        ((List.range m).map (fun m => if hm : m < x2.length then
          (o ⟨m, hm⟩, a ⟨m, hm⟩, b ⟨m, hm⟩) else (false, 0, 0))) = x1 ++ x2.take m := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro hm
        rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
        simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
          dif_pos (show m < x2.length by omega)]
        rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
        simp only [PEqualNP.Outside.L_meta_7457.F, List.append_assoc, Option.toList_some]
        have := hv ⟨m, by omega⟩
        rw [List.get_eq_getElem] at this
        simp only at this
        rw [← this]
    rw [List.foldl_append, ind _ le_rfl, List.take_of_length_le le_rfl,
      PEqualNP.Outside.L_meta_7457.foldl_prefix _ _ _ (by simp [h1])]
    rw [List.getD_append_right _ _ _ _ (by omega), h1, Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ i.isLt, List.get_eq_getElem]
