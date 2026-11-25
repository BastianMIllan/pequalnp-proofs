import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6357
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem ao2 (n : ℕ) (C : Circuit) (a b : ℕ) (hC : PEqualNP.TopForm.IsAO2 n C)
    (ha : a < n + C.size) (hb : b < n + C.size) :
    PEqualNP.TopForm.IsAO2 n ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], n + C.size⟩ := by
  obtain ⟨h1, h2, h3⟩ := hC
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h1 g hg
    · exact Or.inl rfl
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < C.gates.length
    · have e : PEqualNP.MetaComplexity.NestedCover.gateAt
          ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], n + C.size⟩ j
          = PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hlt]
      rw [e] at hi
      exact h2 j hlt i hi
    · have hj' : j = C.gates.length := by omega
      subst hj'
      have e : PEqualNP.MetaComplexity.NestedCover.gateAt
          ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], n + C.size⟩ C.gates.length
          = ⟨GateOp.and, [a, b]⟩ := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD]
      rw [e] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      simp only [Circuit.size] at ha hb
      rcases hi with rfl | rfl <;> omega
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h3 g hg
    · rfl

theorem sem (n : ℕ) (C : Circuit) (a b : ℕ)
    (ha : a < n + C.size) (hb : b < n + C.size) (x : Fin n → Bool) :
    Circuit.eval ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], n + C.size⟩ (List.ofFn x)
        = ((C.wires (List.ofFn x)).getD a false && (C.wires (List.ofFn x)).getD b false) ∧
      (Circuit.wires ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], n + C.size⟩ (List.ofFn x)).getD a false
        = (C.wires (List.ofFn x)).getD a false ∧
      (Circuit.wires ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], n + C.size⟩ (List.ofFn x)).getD b false
        = (C.wires (List.ofFn x)).getD b false := by
  have hw : ∀ D : Circuit, D.wires (List.ofFn x) = wf D.gates (List.ofFn x) := fun _ => rfl
  have hl : (wf C.gates (List.ofFn x)).length = n + C.size := by
    rw [wf_len, List.length_ofFn]; rfl
  unfold Circuit.eval
  rw [hw, hw C, wf_snoc]
  refine ⟨?_, ?_, ?_⟩
  · show (wf C.gates (List.ofFn x) ++ _).getD (n + C.size) false = _
    rw [← hl, getD_snoc_eq]
    simp [GateOp.eval]
  · exact getD_snoc_lt _ _ _ (by omega)
  · exact getD_snoc_lt _ _ _ (by omega)

end PEqualNP.Outside.L_meta_6357

theorem PEqualNP.Outside.L_meta_6357 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.TopForm.IsAO2 x1 x2 →     x3 < x1 + x2.size →       x4 < x1 + x2.size →         have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate }], output := x1 + x2.size : PEqualNP.CircuitLowerBounds.Circuit };         PEqualNP.TopForm.IsAO2 x1 x8 ∧           ∀ (x9 : Fin x1 → Bool),             have x10 : List Bool := x2.wires (List.ofFn x9);             have x11 : List Bool := x8.wires (List.ofFn x9);             x8.eval (List.ofFn x9) = (x10.getD x3 Bool.false && x10.getD x4 Bool.false) ∧ x11.getD x3 Bool.false = x10.getD x3 Bool.false ∧ x11.getD x4 Bool.false = x10.getD x4 Bool.false := by
  intro n C a b hC ha hb
  exact ⟨PEqualNP.Outside.L_meta_6357.ao2 n C a b hC ha hb,
    fun x => PEqualNP.Outside.L_meta_6357.sem n C a b ha hb x⟩
