import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2353

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_prefix (gs : List Gate) : ∀ w : List Bool, ∃ t, gs.foldl stp w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (stp w g)
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by
      rw [List.foldl_cons, ht]
      unfold stp
      simp⟩

theorem fold_length (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl stp w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    unfold stp
    simp
    omega

theorem getD_pre (a b : List Bool) (i : ℕ) (h : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem stp_length (w : List Bool) (g : Gate) : (stp w g).length = w.length + 1 := by
  unfold stp
  simp

theorem stp_getD_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (stp w g).getD i false = w.getD i false := by
  unfold stp
  exact getD_pre _ _ _ h

theorem stp_getD_len (w : List Bool) (g : Gate) :
    (stp w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold stp
  simp [List.getD_eq_getElem?_getD]

theorem gate_val (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hb : ∀ i ∈ (C.gates[j]).inputs, i < x.length + j) :
    (C.wires x).getD (x.length + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  have hsplit : C.gates.take j ++ C.gates[j] :: C.gates.drop (j+1) = C.gates := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have hw : C.wires x = (C.gates.drop (j+1)).foldl stp
      (stp ((C.gates.take j).foldl stp x) C.gates[j]) := by
    show C.gates.foldl stp x = _
    conv_lhs => rw [← hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hW : ((C.gates.take j).foldl stp x).length = x.length + j := by
    rw [fold_length, List.length_take]
    omega
  obtain ⟨t, ht⟩ := fold_prefix (C.gates.drop (j+1)) (stp ((C.gates.take j).foldl stp x) C.gates[j])
  rw [hw, ht]
  have hv : ∀ i ∈ (C.gates[j]).inputs,
      (stp ((C.gates.take j).foldl stp x) C.gates[j] ++ t).getD i false
        = ((C.gates.take j).foldl stp x).getD i false := by
    intro i hi
    have hi' := hb i hi
    rw [getD_pre _ _ _ (by rw [stp_length]; omega), stp_getD_lt _ _ _ (by omega)]
  rw [List.map_congr_left hv]
  rw [getD_pre _ _ _ (by rw [stp_length]; omega), ← hW, stp_getD_len]

theorem gate_val' (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (z : Fin n → Bool)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires (List.ofFn z)).getD (n + j) false =
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map
          fun i => (C.wires (List.ofFn z)).getD i false) := by
  have hg : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  have h := gate_val C (List.ofFn z) j hj (by
    intro i hi
    rw [List.length_ofFn]
    exact hC.2.1 j hj i (by rw [hg]; exact hi))
  rw [List.length_ofFn] at h
  rw [hg]
  exact h

end PEqualNP.Outside.L_meta_2353

theorem PEqualNP.Outside.L_meta_2353 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List ℕ → Prop, T = (fun tt tL => ∀ Q : ℕ → List ℕ → Prop, (∀ (qm qt : ℕ), R qm qt → Q qt [qm]) → (∀ (qj qt : ℕ) (qL1 qL2 : List ℕ), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ∀ (top : ℕ) (L : List ℕ) (z : Fin n → Bool), T top L → (∀ m ∈ L, (C.wires (List.ofFn z)).getD (m) false = true) → (C.wires (List.ofFn z)).getD (top) false = true := by
  intro n C hC R hR T hT top L z hTL hL
  subst hR
  subst hT
  have key : ∀ a b : ℕ, Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) a b →
      (C.wires (List.ofFn z)).getD a false = true → (C.wires (List.ofFn z)).getD b false = true := by
    intro a b hab
    induction hab with
    | refl => exact id
    | tail _ hstep ih =>
      intro ha
      obtain ⟨_, rj, hrb, hrj, hor, hmem⟩ := hstep
      have hc := ih ha
      rw [hrb, PEqualNP.Outside.L_meta_2353.gate_val' n C hC z rj hrj, hor]
      simp only [PEqualNP.CircuitLowerBounds.GateOp.eval]
      rw [List.any_eq_true]
      exact ⟨true, List.mem_map.2 ⟨_, hmem, hc⟩, rfl⟩
  refine hTL (fun t L => (∀ m ∈ L, (C.wires (List.ofFn z)).getD m false = true) →
      (C.wires (List.ofFn z)).getD t false = true) ?_ ?_ hL
  · intro qm qt hq hm
    exact key qm qt hq (hm qm (by simp))
  · intro qj qt L1 L2 hqj hand hq ih1 ih2 hm
    apply key _ _ hq
    have h1 := ih1 (fun m hmm => hm m (List.mem_append_left _ hmm))
    have h2 := ih2 (fun m hmm => hm m (List.mem_append_right _ hmm))
    have hg : PEqualNP.MetaComplexity.NestedCover.gateAt C qj = C.gates[qj] := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hqj]
      rfl
    have hlen : (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.length = 2 := by
      rw [hg]; exact hC.2.2 _ (List.getElem_mem hqj)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen
    rw [hab] at h1 h2
    rw [PEqualNP.Outside.L_meta_2353.gate_val' n C hC z qj hqj, hand, hab]
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h1 h2
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil, h1, h2, id, Bool.and_true]
