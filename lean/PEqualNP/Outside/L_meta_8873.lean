import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8873

open PEqualNP.CircuitLowerBounds

def F (x6 : List ℕ) (x7 : Gate) : List ℕ :=
  x6 ++ [if x7.op.eval [true, false] = true then
      x6.getD (x7.inputs.getD 0 0) 0 ||| x6.getD (x7.inputs.getD 1 0) 0
    else x6.getD (x7.inputs.getD 0 0) 0 &&& x6.getD (x7.inputs.getD 1 0) 0]

theorem getD_tb (k : ℕ) (L : List ℕ) (i : ℕ) :
    (L.map (fun v => v.testBit k)).getD i false = (L.getD i 0).testBit k := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[i]? <;> simp

theorem fold_map (k : ℕ) : ∀ (gs : List Gate) (L : List ℕ),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
    (List.foldl F L gs).map (fun v => v.testBit k) =
      List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (L.map (fun v => v.testBit k)) gs
  | [], _, _ => rfl
  | g :: gs, L, h => by
    simp only [List.foldl_cons]
    rw [fold_map k gs (F L g) (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]
    congr 1
    obtain ⟨hop, hlen⟩ := h g (by simp)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    simp only [F, List.map_append, List.map_cons, List.map_nil, hab, getD_tb]
    rcases hop with hop | hop <;> simp [hop, GateOp.eval, Nat.testBit_or, Nat.testBit_and, getD_tb]

theorem main (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) (L : List ℕ) (k : ℕ) :
    ((List.foldl F L C.gates).getD C.output 0).testBit k = C.eval (L.map (fun v => v.testBit k)) := by
  have h1 := fold_map k C.gates L (fun g hg => ⟨h.1 g hg, h.2.2 g hg⟩)
  unfold Circuit.eval Circuit.wires
  rw [← h1, getD_tb]

end PEqualNP.Outside.L_meta_8873

theorem PEqualNP.Outside.L_meta_8873 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 x1 x2 →     ∀ (x4 : List ℕ) (x5 : ℕ),       have x6 : List ℕ → PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x6 : List ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) =>         have x8 : ℕ := x6.getD (x7.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);         have x9 : ℕ := x6.getD (x7.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);         x6 ++ [if x7.op.eval [Bool.true, Bool.false] = Bool.true then x8 ||| x9 else x8 &&& x9];       ((List.foldl x6 x4 x2.gates).getD x2.output (0 : ℕ)).testBit x5 = x2.eval (List.map (fun (x7 : ℕ) => x7.testBit x5) x4) := by
  intro x1 x2 hAO x4 x5
  exact PEqualNP.Outside.L_meta_8873.main x1 x2 hAO x4 x5
