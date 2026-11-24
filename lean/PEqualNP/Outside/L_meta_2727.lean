import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2727

open PEqualNP.CircuitLowerBounds

def appendWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem readEarlier (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl appendWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hi' : i < (appendWire w g).length := by simp [appendWire]; omega
    rw [List.foldl_cons, ih (appendWire w g) hi']
    simp only [appendWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem replaceSame (g g' : Gate) (gs : List Gate) (w : List Bool) (j : ℕ)
    (hj : gs[j]? = some g)
    (hg : ∀ i ∈ g.inputs, i < w.length + j)
    (hg' : ∀ i ∈ g'.inputs, i < w.length + j)
    (hv : g'.op.eval (g'.inputs.map fun i => (gs.foldl appendWire w).getD i false) =
      g.op.eval (g.inputs.map fun i => (gs.foldl appendWire w).getD i false)) :
    (gs.set j g').foldl appendWire w = gs.foldl appendWire w := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      have e1 : (g'.inputs.map fun i => ((g0 :: gs).foldl appendWire w).getD i false) =
          g'.inputs.map fun i => w.getD i false := by
        apply List.map_congr_left
        intro i hi
        exact readEarlier _ w i (by have := hg' i hi; omega)
      have e2 : (g0.inputs.map fun i => ((g0 :: gs).foldl appendWire w).getD i false) =
          g0.inputs.map fun i => w.getD i false := by
        apply List.map_congr_left
        intro i hi
        exact readEarlier _ w i (by have := hg i hi; omega)
      rw [e1, e2] at hv
      have ha : appendWire w g' = appendWire w g0 := by
        simp only [appendWire, hv]
      simp only [List.set_cons_zero, List.foldl_cons, ha]
    | succ j =>
      simp only [List.set_cons_succ, List.foldl_cons]
      have hlen : (appendWire w g0).length + j = w.length + (j + 1) := by
        simp only [appendWire, List.length_append, List.length_singleton]
        omega
      apply ih (appendWire w g0) j
      · simpa using hj
      · intro i hi; have := hg i hi; omega
      · intro i hi; have := hg' i hi; omega
      · simpa only [List.foldl_cons] using hv

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl appendWire x := rfl

end PEqualNP.Outside.L_meta_2727

theorem PEqualNP.Outside.L_meta_2727 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ),
  j < C.gates.length →
  C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [u, t] } →
  u < n + j → t < n + j →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD u false = true →
      (C.wires (List.ofFn x)).getD t false = true) →
  ∀ x : Fin n → Bool,
    ({ gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] },
       output := C.output } : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x) =
    C.wires (List.ofFn x) := by
  intro n C j u t _ hj hu ht himp x
  rw [PEqualNP.Outside.L_meta_2727.wires_eq, PEqualNP.Outside.L_meta_2727.wires_eq]
  apply PEqualNP.Outside.L_meta_2727.replaceSame _ _ C.gates (List.ofFn x) j hj
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rw [List.length_ofFn]
    rcases hi with rfl | rfl <;> assumption
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rw [List.length_ofFn]
    subst hi
    exact hu
  · have h := himp x
    rw [PEqualNP.Outside.L_meta_2727.wires_eq] at h
    revert h
    simp only [List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval,
      List.any_cons, List.any_nil, List.all_cons, List.all_nil, id, Bool.or_false,
      Bool.and_true]
    cases (C.gates.foldl PEqualNP.Outside.L_meta_2727.appendWire (List.ofFn x)).getD u false <;>
      cases (C.gates.foldl PEqualNP.Outside.L_meta_2727.appendWire (List.ofFn x)).getD t false <;>
      simp
