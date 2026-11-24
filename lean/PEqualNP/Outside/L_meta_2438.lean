import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2438

open PEqualNP.CircuitLowerBounds

theorem ofFn_last' {n : ℕ} (f : Fin (n + 1) → Bool) :
    List.ofFn f = List.ofFn (fun i : Fin n => f i.castSucc) ++ [f (Fin.last n)] := by
  rw [List.ofFn_succ_last]

theorem getD_ofFn' {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD i false = f i := by
  simp [List.getD_eq_getElem?_getD]

theorem key (x1 : Fin 42) (x2 x3 : Fin 43) (C : Circuit) (x8 : Fin 42 → Bool) :
    (Circuit.mk (⟨GateOp.or, [0, (x1 : ℕ)]⟩ :: ⟨GateOp.or, [(x2 : ℕ), (x3 : ℕ)]⟩ :: C.gates)
        C.output).eval (List.ofFn x8)
      = C.eval (List.ofFn fun x10 : Fin (43 + 1) =>
          Fin.lastCases
            ((Fin.lastCases (x8 (0 : Fin 42) || x8 x1) x8 x2) ||
              (Fin.lastCases (x8 (0 : Fin 42) || x8 x1) x8 x3))
            (fun x9 : Fin (42 + 1) => Fin.lastCases (x8 (0 : Fin 42) || x8 x1) x8 x9) x10) := by
  set x9 : Fin (42 + 1) → Bool := fun x9 => Fin.lastCases (x8 (0 : Fin 42) || x8 x1) x8 x9
    with hx9
  have h9 : List.ofFn x9 = List.ofFn x8 ++ [x8 (0 : Fin 42) || x8 x1] := by
    rw [ofFn_last']
    simp only [x9, Fin.lastCases_castSucc, Fin.lastCases_last]
  have h10 : (List.ofFn fun x10 : Fin (43 + 1) => Fin.lastCases (x9 x2 || x9 x3) x9 x10)
      = List.ofFn x9 ++ [x9 x2 || x9 x3] := by
    rw [ofFn_last']
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  have ha : GateOp.or.eval ([0, (x1 : ℕ)].map fun i => (List.ofFn x8).getD i false)
      = (x8 (0 : Fin 42) || x8 x1) := by
    have h0 : (List.ofFn x8).getD 0 false = x8 (0 : Fin 42) := getD_ofFn' x8 0
    simp only [List.map_cons, List.map_nil, GateOp.eval, h0, getD_ofFn']
    simp
  have hb : GateOp.or.eval ([(x2 : ℕ), (x3 : ℕ)].map fun i =>
        (List.ofFn x8 ++ [x8 (0 : Fin 42) || x8 x1]).getD i false)
      = (x9 x2 || x9 x3) := by
    rw [← h9]
    simp only [List.map_cons, List.map_nil, GateOp.eval, getD_ofFn']
    simp
  unfold Circuit.eval Circuit.wires
  simp only [List.foldl_cons]
  simp only [ha]
  rw [hb, h10, h9]

end PEqualNP.Outside.L_meta_2438

theorem PEqualNP.Outside.L_meta_2438 : ∀ (x1 : Fin (42 : ℕ)) (x2 x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x4 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (44 : ℕ) x4 →       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.Monotone2 x7 ∧           x7.size ≤ x4.size + (2 : ℕ) ∧             ∀ (x8 : Fin (42 : ℕ) → Bool),               have x9 : Fin (43 : ℕ) → Bool := fun (x9 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x8 (0 : Fin (42 : ℕ)) || x8 x1) x8 x9;               x7.eval (List.ofFn x8) = x4.eval (List.ofFn fun (x10 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x9 x2 || x9 x3) x9 x10) := by
  intro x1 x2 x3 x4 hm _
  refine ⟨PEqualNP.CircuitLowerBounds.Circuit.mk
    (⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, (x1 : ℕ)]⟩ ::
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [(x2 : ℕ), (x3 : ℕ)]⟩ :: x4.gates) x4.output,
    ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp
    · simp
    · exact hm g hg
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x8
    exact PEqualNP.Outside.L_meta_2438.key x1 x2 x3 x4 x8
