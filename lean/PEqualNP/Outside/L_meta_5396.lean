import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5396

open PEqualNP.CircuitLowerBounds

def circ : Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 38] }], output := 39 }

def A2 (a b : Bool) : Bool := a && (b && true)

def O2 (a b : Bool) : Bool := a || (b || false)

def Ef (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Bool) : Bool := (O2 (A2 (O2 a11 (A2 (O2 a6 (A2 (O2 a1 a2) (O2 a0 a3))) (O2 a2 a7))) (O2 a7 a15)) (O2 (A2 (O2 a10 (A2 (O2 a1 a2) (O2 a0 a3))) (O2 a14 (A2 (O2 a6 (A2 (O2 a1 a2) (O2 a0 a3))) (O2 a2 a7)))) (O2 (A2 (O2 a8 (A2 (O2 a1 a2) (O2 a0 a3))) (O2 a12 (A2 (O2 a4 (A2 (O2 a1 a2) (O2 a0 a3))) (O2 a0 a5)))) (A2 (O2 a9 (A2 (O2 a4 (A2 (O2 a1 a2) (O2 a0 a3))) (O2 a0 a5))) (O2 a5 a13)))))

def Fm (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Bool) : Bool := (a0 && a1) || (a2 && a3) || (a4 && a5) || (a6 && a7) || (a8 && a12) || (a9 && a13) || (a10 && a14) || (a11 && a15)

def Gf (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Bool) : Bool := (a0 && a1) || (a2 && a3) || (a4 && a5) || (a6 && a7) || (a8 && a12) || (a9 && a13) || (a10 && a14) || (a11 && a15) || (a0 && a2) || (a3 && a5) || (a1 && a7) || (a1 && a12) || (a4 && a8) || (a5 && a9) || (a0 && a13) || (a3 && a14) || (a6 && a10) || (a7 && a11) || (a2 && a15)

set_option maxHeartbeats 4000000 in
theorem wiresEq (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Bool) : circ.eval [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] = Ef a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 := by
  simp only [Ef, A2, O2, circ, Circuit.eval, Circuit.wires, List.foldl, List.map, GateOp.eval, List.getD_cons_succ, List.getD_cons_zero, List.cons_append, List.nil_append, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem truth : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Bool, (Fm a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 = true → Ef a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 = true) ∧ (Ef a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 = true → Gf a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 = true) := by
  decide +kernel

theorem ofFnEq (x : Fin 16 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15] := by
  simp [List.ofFn_succ]

theorem fmEq (x : Fin 16 → Bool) : (∃ e ∈ ([(0, 1), (2, 3), (4, 5), (6, 7), (8, 12), (9, 13), (10, 14), (11, 15)] : List (Fin 16 × Fin 16)), x e.1 = true ∧ x e.2 = true) ↔ Fm (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13) (x 14) (x 15) = true := by
  simp [Fm, or_assoc]

theorem gfEq (x : Fin 16 → Bool) : (∃ e ∈ ([(0, 1), (2, 3), (4, 5), (6, 7), (8, 12), (9, 13), (10, 14), (11, 15), (0, 2), (3, 5), (1, 7), (1, 12), (4, 8), (5, 9), (0, 13), (3, 14), (6, 10), (7, 11), (2, 15)] : List (Fin 16 × Fin 16)), x e.1 = true ∧ x e.2 = true) ↔ Gf (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13) (x 14) (x 15) = true := by
  simp [Gf, or_assoc]

theorem funEq (x : Fin 16 → Bool) : PEqualNP.MetaComplexity.circuitFun 16 circ x = Ef (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13) (x 14) (x 15) := by
  unfold PEqualNP.MetaComplexity.circuitFun
  rw [ofFnEq x]
  exact wiresEq (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13) (x 14) (x 15)

theorem aoC : PEqualNP.TopForm.IsAO2 16 circ := by
  decide +kernel

theorem andC : ∀ k < circ.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt circ k).op = PEqualNP.CircuitLowerBounds.GateOp.and ↔ k ∈ ([2, 5, 8, 11, 14, 17, 20] : List ℕ) := by
  intro k hk
  have hk2 : k < 24 := hk
  interval_cases k <;> simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ]

end PEqualNP.Outside.L_meta_5396


open PEqualNP.Outside.L_meta_5396 in
theorem PEqualNP.Outside.L_meta_5396 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 38] }], output := 39 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 16 C ∧ C.size = 24 ∧
  (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ↔ k ∈ ([2, 5, 8, 11, 14, 17, 20] : List ℕ)) ∧
  ∀ x : Fin 16 → Bool,
    ((∃ e ∈ ([(0, 1), (2, 3), (4, 5), (6, 7), (8, 12), (9, 13), (10, 14), (11, 15)] : List (Fin 16 × Fin 16)), x e.1 = true ∧ x e.2 = true) → PEqualNP.MetaComplexity.circuitFun 16 C x = true) ∧
    (PEqualNP.MetaComplexity.circuitFun 16 C x = true → ∃ e ∈ ([(0, 1), (2, 3), (4, 5), (6, 7), (8, 12), (9, 13), (10, 14), (11, 15), (0, 2), (3, 5), (1, 7), (1, 12), (4, 8), (5, 9), (0, 13), (3, 14), (6, 10), (7, 11), (2, 15)] : List (Fin 16 × Fin 16)), x e.1 = true ∧ x e.2 = true) := by
  intro C hC
  subst hC
  refine ⟨aoC, rfl, andC, ?_⟩
  intro x
  have ht := truth (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13) (x 14) (x 15)
  have hf := funEq x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact hf.trans (ht.1 ((fmEq x).1 h))
  · exact (gfEq x).2 (ht.2 (hf.symm.trans h))
