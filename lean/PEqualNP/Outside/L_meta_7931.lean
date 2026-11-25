import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7931

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem foldl_len (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons]
    rw [ih]
    simp
    omega

theorem wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.gates.length :=
  foldl_len C.gates x

theorem wires_snoc (gs : List Gate) (g : Gate) (o o' : ℕ) (x : List Bool) :
    (Circuit.mk (gs ++ [g]) o).wires x = (Circuit.mk gs o').wires x ++
      [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs o').wires x).getD i false)] := by
  unfold Circuit.wires
  rw [List.foldl_append]
  rfl

theorem gD_left {α : Type} (l m : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ m).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gD_right {α : Type} (l m : List α) (d : α) (i : ℕ) (h : l.length ≤ i) :
    (l ++ m).getD i d = m.getD (i - l.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem main (x1 : ℕ) (x2 : Circuit) (x3 x4 : ℕ) (hA : PEqualNP.TopForm.IsAO2 x1 x2)
    (hN : ∀ g ∈ x2.gates, g.inputs.Nodup) (hne : x3 ≠ x4) (h3 : x3 < x1 + x2.size)
    (h4 : x4 < x1 + x2.size) :
    let C : Circuit := { gates := x2.gates ++ [{ op := GateOp.and, inputs := [x3, x4] : Gate }], output := x1 + x2.size : Circuit };
    PEqualNP.TopForm.IsAO2 x1 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      ∀ x11 : List Bool, x11.length = x1 →
        C.eval x11 = ((x2.wires x11).getD x3 false && (x2.wires x11).getD x4 false) ∧
        (C.wires x11).getD x3 false = (x2.wires x11).getD x3 false ∧
        (C.wires x11).getD x4 false = (x2.wires x11).getD x4 false := by
  intro C
  obtain ⟨hAO, hRB, hl2⟩ := hA
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    simp only [C, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · left; rfl
  · intro j hj i hi
    simp only [C, List.length_append, List.length_singleton] at hj
    by_cases hjl : j < x2.gates.length
    · have hg : gateAt C j = gateAt x2 j := by
        unfold gateAt
        exact gD_left _ _ _ _ hjl
      rw [hg] at hi
      exact hRB j hjl i hi
    · have hj' : j = x2.gates.length := by omega
      have hg : gateAt C j = ({ op := GateOp.and, inputs := [x3, x4] } : Gate) := by
        unfold gateAt
        show (x2.gates ++ [({ op := GateOp.and, inputs := [x3, x4] } : Gate)]).getD j _ = _
        rw [gD_right _ _ _ _ (by omega), hj', Nat.sub_self]
        rfl
      rw [hg] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      unfold Circuit.size at h3 h4
      rcases hi with rfl | rfl <;> omega
  · intro g hg
    simp only [C, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hl2 g hg
    · rfl
  · intro g hg
    simp only [C, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hN g hg
    · simp [hne]
  · intro x11 hx
    have hw : C.wires x11 = x2.wires x11 ++
        [GateOp.eval GateOp.and ([x3, x4].map fun i => (x2.wires x11).getD i false)] :=
      wires_snoc x2.gates _ _ x2.output x11
    have hL : (x2.wires x11).length = x1 + x2.size := by
      rw [wires_len, hx]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · show (C.wires x11).getD (x1 + x2.size) false = _
      rw [hw, gD_right _ _ _ _ (by omega), hL, Nat.sub_self]
      simp [GateOp.eval]
    · rw [hw, gD_left _ _ _ _ (by omega)]
    · rw [hw, gD_left _ _ _ _ (by omega)]

end PEqualNP.Outside.L_meta_7931

theorem PEqualNP.Outside.L_meta_7931 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.TopForm.IsAO2 x1 x2 →     (∀ x6 ∈ x2.gates, x6.inputs.Nodup) →       x3 ≠ x4 →         x3 < x1 + x2.size →           x4 < x1 + x2.size →             have x10 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate }], output := x1 + x2.size : PEqualNP.CircuitLowerBounds.Circuit };             PEqualNP.TopForm.IsAO2 x1 x10 ∧ (∀ x11 ∈ x10.gates, x11.inputs.Nodup) ∧ ∀ (x11 : List Bool), x11.length = x1 → x10.eval x11 = ((x2.wires x11).getD x3 Bool.false && (x2.wires x11).getD x4 Bool.false) ∧ (x10.wires x11).getD x3 Bool.false = (x2.wires x11).getD x3 Bool.false ∧ (x10.wires x11).getD x4 Bool.false = (x2.wires x11).getD x4 Bool.false := by
  intro x1 x2 x3 x4 hA hN hne h3 h4
  exact PEqualNP.Outside.L_meta_7931.main x1 x2 x3 x4 hA hN hne h3 h4
