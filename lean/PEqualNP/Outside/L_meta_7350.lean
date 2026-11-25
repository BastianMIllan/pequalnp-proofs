import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7350
open PEqualNP.CircuitLowerBounds

def stepF (x1 : List (ℕ × ℕ)) (x2 : Gate) : List (ℕ × ℕ) :=
  have x3 : ℕ × ℕ := x1.getD (x2.inputs.getD (0 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ))
  have x4 : ℕ × ℕ := x1.getD (x2.inputs.getD (1 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ))
  x1 ++ [(if x2.op.eval [Bool.false, Bool.true] = Bool.true then x3.1 ||| x4.1 else x3.1 &&& x4.1, x3.2 + x4.2)]

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_bit (ws : List (ℕ × ℕ)) (k i : ℕ) :
    (ws.map (fun p : ℕ × ℕ => p.1.testBit k)).getD i false = (ws.getD i (0, 0)).1.testBit k := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[i]? <;> simp

theorem main (k : ℕ) : ∀ (gs : List Gate) (ws : List (ℕ × ℕ)),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
    (gs.foldl stepF ws).map (fun p : ℕ × ℕ => p.1.testBit k)
      = gs.foldl wstep (ws.map (fun p : ℕ × ℕ => p.1.testBit k)) := by
  intro gs
  induction gs with
  | nil => intro ws _; rfl
  | cons g gs ih =>
    intro ws h
    simp only [List.foldl_cons]
    rw [ih (stepF ws g) (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]
    congr 1
    obtain ⟨hop, hlen⟩ := h g (List.mem_cons_self ..)
    match hi : g.inputs, hlen with
    | [a, b], _ =>
      simp only [stepF, wstep, List.map_append, List.map_cons, List.map_nil, hi,
        List.getD_cons_zero, List.getD_cons_succ, getD_bit]
      rcases hop with hop | hop <;>
        simp [hop, GateOp.eval, Nat.testBit_or, Nat.testBit_and]

theorem final (gs : List Gate) (ws : List (ℕ × ℕ))
    (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) (k o : ℕ) :
    ((gs.foldl stepF ws).getD o (0, 0)).1.testBit k
      = ({ gates := gs, output := o } : Circuit).eval (ws.map (fun p : ℕ × ℕ => p.1.testBit k)) := by
  rw [← getD_bit]
  unfold Circuit.eval Circuit.wires
  rw [main k gs ws h]
  rfl

end PEqualNP.Outside.L_meta_7350

theorem PEqualNP.Outside.L_meta_7350 : have x1 : List (ℕ × ℕ) → PEqualNP.CircuitLowerBounds.Gate → List (ℕ × ℕ) := fun (x1 : List (ℕ × ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) =>   have x3 : ℕ × ℕ := x1.getD (x2.inputs.getD (0 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));   have x4 : ℕ × ℕ := x1.getD (x2.inputs.getD (1 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));   x1 ++ [(if x2.op.eval [Bool.false, Bool.true] = Bool.true then x3.1 ||| x4.1 else x3.1 &&& x4.1, x3.2 + x4.2)]; ∀ (x2 : List PEqualNP.CircuitLowerBounds.Gate) (x3 : List (ℕ × ℕ)), (∀ x4 ∈ x2, (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x4.inputs.length = (2 : ℕ)) → ∀ (x5 x6 : ℕ), ((List.foldl x1 x3 x2).getD x6 ((0 : ℕ), (0 : ℕ))).1.testBit x5 = { gates := x2, output := x6 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.map (fun (x7 : ℕ × ℕ) => x7.1.testBit x5) x3) := by
  intro x1 gs ws h k o
  exact PEqualNP.Outside.L_meta_7350.final gs ws h k o
