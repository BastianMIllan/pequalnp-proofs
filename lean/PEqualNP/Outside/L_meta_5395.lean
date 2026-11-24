import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5395

def Cc : PEqualNP.CircuitLowerBounds.Circuit := ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 24] }], output := 25 } : PEqualNP.CircuitLowerBounds.Circuit)

def Dc : PEqualNP.CircuitLowerBounds.Circuit := ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 20] }], output := 21 } : PEqualNP.CircuitLowerBounds.Circuit)

theorem funC_b : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool, PEqualNP.MetaComplexity.circuitFun 10 Cc ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] = decide (∃ e ∈ ([(0, 6), (1, 6), (2, 6), (0, 7), (3, 7), (4, 8), (5, 8), (4, 9)] : List (Fin 10 × Fin 10)), ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] e.1 = true ∧ ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] e.2 = true) := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  simp [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, Cc, PEqualNP.CircuitLowerBounds.GateOp.eval, List.ofFn_succ]
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  decide

theorem funC : ∀ x : Fin 10 → Bool, PEqualNP.MetaComplexity.circuitFun 10 Cc x = decide (∃ e ∈ ([(0, 6), (1, 6), (2, 6), (0, 7), (3, 7), (4, 8), (5, 8), (4, 9)] : List (Fin 10 × Fin 10)), x e.1 = true ∧ x e.2 = true) := by
  intro x
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  exact funC_b _ _ _ _ _ _ _ _ _ _

theorem funD_b : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool, PEqualNP.MetaComplexity.circuitFun 10 Dc ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] = decide (∃ e ∈ ([(0, 6), (1, 6), (2, 6), (0, 7), (3, 7), (4, 8), (5, 8), (4, 9)] : List (Fin 10 × Fin 10)), ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] e.1 = true ∧ ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] e.2 = true) := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  simp [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, Dc, PEqualNP.CircuitLowerBounds.GateOp.eval, List.ofFn_succ]
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  decide

theorem funD : ∀ x : Fin 10 → Bool, PEqualNP.MetaComplexity.circuitFun 10 Dc x = decide (∃ e ∈ ([(0, 6), (1, 6), (2, 6), (0, 7), (3, 7), (4, 8), (5, 8), (4, 9)] : List (Fin 10 × Fin 10)), x e.1 = true ∧ x e.2 = true) := by
  intro x
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  exact funD_b _ _ _ _ _ _ _ _ _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem readC : ∀ e ∈ ([(0, 6), (1, 6), (2, 6), (0, 7), (3, 7), (4, 8), (5, 8), (4, 9)] : List (Fin 10 × Fin 10)), PEqualNP.Core.ReadTwiceAt 10 Cc 15 e.1 e.2 ↔ e ∈ ([(1, 6), (3, 7), (4, 8), (5, 8), (4, 9)] : List (Fin 10 × Fin 10)) := by
  decide

theorem aoC : PEqualNP.TopForm.IsAO2 10 Cc := by decide

theorem aoD : PEqualNP.TopForm.IsAO2 10 Dc := by decide

end PEqualNP.Outside.L_meta_5395

theorem PEqualNP.Outside.L_meta_5395 : ∀ C D : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 24] }], output := 25 } : PEqualNP.CircuitLowerBounds.Circuit) → D = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 20] }], output := 21 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 10 C ∧ C.size = 16 ∧ PEqualNP.TopForm.IsAO2 10 D ∧ D.size = 12 ∧
  (∀ x : Fin 10 → Bool, PEqualNP.MetaComplexity.circuitFun 10 C x = decide (∃ e ∈ ([(0, 6), (1, 6), (2, 6), (0, 7), (3, 7), (4, 8), (5, 8), (4, 9)] : List (Fin 10 × Fin 10)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ x : Fin 10 → Bool, PEqualNP.MetaComplexity.circuitFun 10 D x = decide (∃ e ∈ ([(0, 6), (1, 6), (2, 6), (0, 7), (3, 7), (4, 8), (5, 8), (4, 9)] : List (Fin 10 × Fin 10)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 6), (1, 6), (2, 6), (0, 7), (3, 7), (4, 8), (5, 8), (4, 9)] : List (Fin 10 × Fin 10)), PEqualNP.Core.ReadTwiceAt 10 C (C.output - 10) e.1 e.2 ↔ e ∈ ([(1, 6), (3, 7), (4, 8), (5, 8), (4, 9)] : List (Fin 10 × Fin 10))) := by
  intro C D hC hD
  subst hC hD
  exact ⟨PEqualNP.Outside.L_meta_5395.aoC, rfl, PEqualNP.Outside.L_meta_5395.aoD, rfl, PEqualNP.Outside.L_meta_5395.funC, PEqualNP.Outside.L_meta_5395.funD, PEqualNP.Outside.L_meta_5395.readC⟩
