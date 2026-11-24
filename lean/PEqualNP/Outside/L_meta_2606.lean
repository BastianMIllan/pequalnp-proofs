import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2606

open PEqualNP.CircuitLowerBounds

theorem getD_le {w w' : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w w') (i : ℕ) :
    w.getD i false ≤ w'.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

theorem bool_le {a b : Bool} : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

theorem gate_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {w w' : List Bool}
    (h : List.Forall₂ (fun a b => a ≤ b) w w') :
    g.op.eval (g.inputs.map fun i => w.getD i false) ≤
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  rw [bool_le]
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hx x hx'
    obtain ⟨i, hi, rfl⟩ := hx'
    exact bool_le.mp (getD_le h i) (hx _ ⟨i, hi, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, bool_le.mp (getD_le h i) hx⟩

theorem fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, List.Forall₂ (fun a b => a ≤ b) w w' →
      List.Forall₂ (fun a b => a ≤ b)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs with
  | nil => intro w w' h; simpa using h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    exact List.rel_append h (List.Forall₂.cons (gate_le g (hgs g List.mem_cons_self) h) List.Forall₂.nil)

theorem fold_prefix (gs : List Gate) : ∀ w : List Bool,
    w <+: gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons]
    exact (List.prefix_append w _).trans (ih _)

theorem fold_length (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

theorem getD_prefix {l1 l2 : List Bool} (h : l1 <+: l2) {i : ℕ} (hi : i < l1.length) :
    l2.getD i false = l1.getD i false := by
  obtain ⟨t, rfl⟩ := h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

end PEqualNP.Outside.L_meta_2606

open PEqualNP.Outside.L_meta_2606 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2606 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.TopForm.IsAO2 x2 x1 → (∀ (x4 : ℕ), Monotone fun (x5 : Fin x2 → Bool) => PEqualNP.BlindGate.wireValue x1 x2 x5 x4) ∧ ∀ (x4 x5 x6 : ℕ), x1.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } → ∀ (x8 : Fin x2 → Bool), PEqualNP.BlindGate.wireValue x1 x2 x8 (x2 + x4) = (PEqualNP.BlindGate.wireValue x1 x2 x8 x5 && PEqualNP.BlindGate.wireValue x1 x2 x8 x6) := by
  intro C n hC
  unfold PEqualNP.TopForm.IsAO2 at hC
  obtain ⟨hAO, hRB, _⟩ := hC
  refine ⟨?_, ?_⟩
  · intro w x y hxy
    have h0 : List.Forall₂ (fun a b => a ≤ b) (List.ofFn x) (List.ofFn y) := by
      rw [List.forall₂_iff_get]
      refine ⟨by simp only [List.length_ofFn], fun i h1 h2 => ?_⟩
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      exact hxy _
    exact getD_le (fold_le C.gates hAO _ _ h0) w
  · intro j u t hj x
    obtain ⟨hjl, hg⟩ := List.getElem?_eq_some_iff.mp hj
    have hrb := hRB j hjl
    have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C j =
        { op := GateOp.and, inputs := [u, t] } := by
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj,
        Option.getD_some]
    rw [hgate] at hrb
    have hu : u < n + j := hrb u (by simp)
    have ht : t < n + j := hrb t (by simp)
    have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) :=
      by rw [List.getElem_cons_drop, List.take_append_drop]
    set F : List Bool → Gate → List Bool :=
      fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] with hF
    set W := (C.gates.take j).foldl F (List.ofFn x) with hW
    have hWlen : W.length = n + j := by
      rw [hW, hF, fold_length]
      simp only [List.length_ofFn, List.length_take]
      omega
    have hwires : C.wires (List.ofFn x) = (C.gates.drop (j + 1)).foldl F (F W C.gates[j]) := by
      unfold Circuit.wires
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hpre : F W C.gates[j] <+: C.wires (List.ofFn x) := by
      rw [hwires, hF]
      exact fold_prefix _ _
    have hFW : F W C.gates[j] = W ++ [W.getD u false && W.getD t false] := by
      rw [hF, hg]
      simp [GateOp.eval]
    rw [hFW] at hpre
    have hpre' : W <+: C.wires (List.ofFn x) := (List.prefix_append W _).trans hpre
    unfold PEqualNP.BlindGate.wireValue
    rw [getD_prefix hpre (by simp [hWlen]), getD_prefix hpre' (by omega),
      getD_prefix hpre' (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [hWlen]
