import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7455

open PEqualNP.CircuitLowerBounds

theorem getD_app_left (l l' : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_len (l l' : List Bool) (a : Bool) :
    (l ++ a :: l').getD l.length false = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem fold_pre (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega), getD_app_left _ _ _ h]

theorem wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.size := by
  unfold Circuit.wires Circuit.size
  exact fold_len _ _

end PEqualNP.Outside.L_meta_7455

theorem PEqualNP.Outside.L_meta_7455 : ∀ (x1 : ℕ) (x2 x3 : Fin x1) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x4 → x4.output < x1 + x4.size → x5 < x1 + x4.size → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x10 ∧ x10.size = x4.size + (3 : ℕ) ∧ x10.output < x1 + x10.size ∧ (∀ x11 < x1 + x4.size, ∀ (x13 : Fin x1 → Bool), (x10.wires (List.ofFn x13)).getD x11 Bool.false = (x4.wires (List.ofFn x13)).getD x11 Bool.false) ∧ ∀ (x11 : Fin x1 → Bool), x10.eval (List.ofFn x11) = (x4.eval (List.ofFn x11) || x11 x3 && (x11 x2 || (x4.wires (List.ofFn x11)).getD x5 Bool.false)) := by
  intro n p q C k hmono hrb hout hk
  have hp := p.isLt
  have hq := q.isLt
  let g1 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [p.val, k]⟩
  let g2 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [q.val, n + C.size]⟩
  let g3 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, n + C.size + 1]⟩
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates ++ [g1, g2, g3], n + C.size + 2⟩
  have hDsize : D.size = C.size + 3 := by
    simp [D, PEqualNP.CircuitLowerBounds.Circuit.size]
  -- the wires of D
  have hwires : ∀ x : Fin n → Bool, ∃ a b c : Bool,
      D.wires (List.ofFn x) = C.wires (List.ofFn x) ++ [a, b, c] ∧
      a = (x p || (C.wires (List.ofFn x)).getD k false) ∧ b = (x q && a) ∧
      c = ((C.wires (List.ofFn x)).getD C.output false || b) := by
    intro x
    set W := C.wires (List.ofFn x) with hWdef
    have hWlen : W.length = n + C.size := by
      rw [hWdef, PEqualNP.Outside.L_meta_7455.wires_len]; simp
    have hpW : W.getD p.val false = x p := by
      rw [hWdef]
      unfold PEqualNP.CircuitLowerBounds.Circuit.wires
      rw [PEqualNP.Outside.L_meta_7455.fold_pre _ _ _ (by simp)]
      simp
    have hqW : W.getD q.val false = x q := by
      rw [hWdef]
      unfold PEqualNP.CircuitLowerBounds.Circuit.wires
      rw [PEqualNP.Outside.L_meta_7455.fold_pre _ _ _ (by simp)]
      simp
    have hD1 : D.wires (List.ofFn x) =
        ((W ++ [g1.op.eval (g1.inputs.map fun i => W.getD i false)]) ++
          [g2.op.eval (g2.inputs.map fun i =>
            (W ++ [g1.op.eval (g1.inputs.map fun i => W.getD i false)]).getD i false)]) ++
          [g3.op.eval (g3.inputs.map fun i =>
            ((W ++ [g1.op.eval (g1.inputs.map fun i => W.getD i false)]) ++
              [g2.op.eval (g2.inputs.map fun i =>
                (W ++ [g1.op.eval (g1.inputs.map fun i => W.getD i false)]).getD i false)]).getD i false)] := by
      show (C.gates ++ [g1, g2, g3]).foldl _ (List.ofFn x) = _
      rw [List.foldl_append]
      rfl
    refine ⟨x p || W.getD k false, x q && (x p || W.getD k false),
      W.getD C.output false || (x q && (x p || W.getD k false)), ?_, rfl, rfl, rfl⟩
    rw [hD1]
    have e1 : g1.op.eval (g1.inputs.map fun i => W.getD i false) = (x p || W.getD k false) := by
      simp only [g1, List.map_cons, List.map_nil, hpW]
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
    rw [e1]
    have e2a : (W ++ [x p || W.getD k false]).getD (n + C.size) false = (x p || W.getD k false) := by
      rw [← hWlen]; exact PEqualNP.Outside.L_meta_7455.getD_app_len _ _ _
    have e2b : (W ++ [x p || W.getD k false]).getD q.val false = x q := by
      rw [PEqualNP.Outside.L_meta_7455.getD_app_left _ _ _ (by rw [hWlen]; omega)]; exact hqW
    have e2 : g2.op.eval (g2.inputs.map fun i => (W ++ [x p || W.getD k false]).getD i false)
        = (x q && (x p || W.getD k false)) := by
      simp only [g2, List.map_cons, List.map_nil, e2a, e2b]
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
    rw [e2]
    have e3a : ((W ++ [x p || W.getD k false]) ++ [x q && (x p || W.getD k false)]).getD
        (n + C.size + 1) false = (x q && (x p || W.getD k false)) := by
      have : n + C.size + 1 = (W ++ [x p || W.getD k false]).length := by simp [hWlen]
      rw [this]; exact PEqualNP.Outside.L_meta_7455.getD_app_len _ _ _
    have e3b : ((W ++ [x p || W.getD k false]) ++ [x q && (x p || W.getD k false)]).getD
        C.output false = W.getD C.output false := by
      rw [List.append_assoc, PEqualNP.Outside.L_meta_7455.getD_app_left _ _ _ (by rw [hWlen]; omega)]
    have e3 : g3.op.eval (g3.inputs.map fun i =>
        ((W ++ [x p || W.getD k false]) ++ [x q && (x p || W.getD k false)]).getD i false)
        = (W.getD C.output false || (x q && (x p || W.getD k false))) := by
      simp only [g3, List.map_cons, List.map_nil, e3a, e3b]
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
    rw [e3]
    simp
  refine ⟨D, ?_, ?_, hDsize, ?_, ?_, ?_⟩
  · -- Monotone2
    intro g hg
    have hg' : g ∈ C.gates ∨ g = g1 ∨ g = g2 ∨ g = g3 := by
      simpa [D] using hg
    rcases hg' with h | h | h | h
    · exact hmono g h
    · subst h; simp [g1]
    · subst h; simp [g2]
    · subst h; simp [g3]
  · -- ReadsBack
    intro j hj i hi
    have hjl : j < C.gates.length + 3 := by simpa [D] using hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    by_cases hjc : j < C.gates.length
    · have : (D.gates).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
          = C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
        simp only [D]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hjc]
      rw [this] at hi
      exact hrb j hjc i hi
    · have hs : C.size = C.gates.length := rfl
      have hj3 : j = C.gates.length ∨ j = C.gates.length + 1 ∨ j = C.gates.length + 2 := by omega
      rcases hj3 with h | h | h
      · subst h
        have : (D.gates).getD C.gates.length ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g1 := by
          simp [D]
        rw [this] at hi
        simp [g1] at hi
        rcases hi with h | h <;> subst h <;> omega
      · subst h
        have : (D.gates).getD (C.gates.length + 1) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g2 := by
          simp [D]
        rw [this] at hi
        simp [g2] at hi
        rcases hi with h | h <;> subst h <;> omega
      · subst h
        have : (D.gates).getD (C.gates.length + 2) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g3 := by
          simp [D]
        rw [this] at hi
        simp [g3] at hi
        rcases hi with h | h <;> subst h <;> omega
  · rw [hDsize]; show n + C.size + 2 < n + (C.size + 3); omega
  · intro i hi x
    obtain ⟨a, b, c, hw, -, -, -⟩ := hwires x
    rw [hw, PEqualNP.Outside.L_meta_7455.getD_app_left _ _ _ (by rw [PEqualNP.Outside.L_meta_7455.wires_len]; simpa using hi)]
  · intro x
    obtain ⟨a, b, c, hw, ha, hb, hc⟩ := hwires x
    have hWlen : (C.wires (List.ofFn x)).length = n + C.size := by rw [PEqualNP.Outside.L_meta_7455.wires_len]; simp
    show (D.wires (List.ofFn x)).getD (n + C.size + 2) false = _
    rw [hw]
    have : n + C.size + 2 = (C.wires (List.ofFn x) ++ [a, b]).length := by simp [hWlen]
    rw [show C.wires (List.ofFn x) ++ [a, b, c] = (C.wires (List.ofFn x) ++ [a, b]) ++ c :: [] by simp,
      this, PEqualNP.Outside.L_meta_7455.getD_app_len]
    rw [hc, hb, ha]
    rfl
