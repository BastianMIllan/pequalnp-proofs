import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2919

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma keepWire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

-- Two gates that agree whenever the earlier wire a has the value c may be swapped at j.
lemma setEq (gs : List Gate) (w : List Bool) (j a : ℕ) (g1 g2 : Gate) (c : Bool)
    (early : a < w.length + j) (hv : (gs.foldl step w).getD a false = c)
    (hg : ∀ v : List Bool, v.getD a false = c →
      g1.op.eval (g1.inputs.map fun i => v.getD i false) =
        g2.op.eval (g2.inputs.map fun i => v.getD i false)) :
    (gs.set j g1).foldl step w = (gs.set j g2).foldl step w := by
  induction gs generalizing w j with
  | nil => simp
  | cons g gs ih =>
    cases j with
    | zero =>
      have lt : a < w.length := by simpa using early
      rw [keepWire (g :: gs) w a lt] at hv
      simp only [List.set_cons_zero, List.foldl_cons]
      congr 1
      simp only [step, hg w hv]
    | succ j =>
      simp only [List.set_cons_succ, List.foldl_cons]
      apply ih (step w g) j
      · simp only [step, List.length_append, List.length_singleton]
        omega
      · exact hv

end PEqualNP.Outside.L_meta_2919

theorem PEqualNP.Outside.L_meta_2919 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j a b : ℕ) (op : PEqualNP.CircuitLowerBounds.GateOp),
  (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or) →
  C.gates[j]? = some { op := op, inputs := [a, b] } →
  a < n + j →
  (∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD a false = PEqualNP.CircuitLowerBounds.GateOp.eval op [] →
      PEqualNP.MetaComplexity.circuitFun n
          { gates := C.gates.set j { op := op, inputs := [] }, output := C.output } x =
        PEqualNP.MetaComplexity.circuitFun n C x) →
  PEqualNP.MetaComplexity.circuitFun n
      { gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a] },
        output := C.output } =
    PEqualNP.MetaComplexity.circuitFun n C ∧
  (C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a] }).length =
    C.gates.length := by
  open PEqualNP.Outside.L_meta_2919 PEqualNP.CircuitLowerBounds in
  intro n C j a b op hop gate early hyp
  refine ⟨?_, by simp⟩
  funext x
  obtain ⟨hj, hg⟩ := List.getElem?_eq_some_iff.mp gate
  have hset : C.gates.set j ⟨op, [a, b]⟩ = C.gates := by
    rw [← hg]
    exact List.set_getElem_self hj
  have early' : a < (List.ofFn x).length + j := by simpa using early
  have hw : C.wires (List.ofFn x) = C.gates.foldl step (List.ofFn x) := rfl
  by_cases hc : (C.wires (List.ofFn x)).getD a false = GateOp.eval op []
  · rw [← hyp x hc]
    show ((C.gates.set j ⟨GateOp.or, [a]⟩).foldl step (List.ofFn x)).getD C.output false =
      ((C.gates.set j ⟨op, []⟩).foldl step (List.ofFn x)).getD C.output false
    rw [setEq C.gates (List.ofFn x) j a ⟨GateOp.or, [a]⟩ ⟨op, []⟩ (GateOp.eval op []) early'
      (by rw [← hw]; exact hc)]
    intro v hv
    rcases hop with rfl | rfl <;> simp [GateOp.eval] at hv ⊢ <;> simp [hv]
  · show ((C.gates.set j ⟨GateOp.or, [a]⟩).foldl step (List.ofFn x)).getD C.output false =
      (C.gates.foldl step (List.ofFn x)).getD C.output false
    have key := setEq C.gates (List.ofFn x) j a ⟨GateOp.or, [a]⟩ ⟨op, [a, b]⟩
      ((C.wires (List.ofFn x)).getD a false) early' (by rw [← hw])
    rw [hset] at key
    rw [key]
    intro v hv
    generalize (C.wires (List.ofFn x)).getD a false = va at hc hv
    rcases hop with rfl | rfl <;> cases va <;> simp_all [GateOp.eval]
