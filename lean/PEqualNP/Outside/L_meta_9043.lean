import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9043

open PEqualNP.CircuitLowerBounds

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_prefix : ∀ (gs : List Gate) (w : List Bool),
    ∃ t, gs.foldl stepF w = w ++ t ∧ t.length = gs.length
  | [], w => ⟨[], by simp⟩
  | g :: gs, w => by
    obtain ⟨t, ht, hl⟩ := fold_prefix gs (stepF w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, ?_⟩
    · rw [List.foldl_cons, ht]; simp [stepF]
    · simp [hl]

theorem getD_mid (W t : List Bool) (v : Bool) :
    (W ++ [v] ++ t).getD W.length false = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, List.getElem?_append_right]

theorem getD_left (W t : List Bool) (v : Bool) (a : ℕ) (ha : a < W.length) :
    (W ++ [v] ++ t).getD a false = W.getD a false := by
  simp [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_left ha]

end PEqualNP.Outside.L_meta_9043

theorem PEqualNP.Outside.L_meta_9043 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x1 ≤ x2.output → x2.output < x1 + x2.size → (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x2.output - x1]? = Option.some x6 ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ (x7 : ℕ) (x8 : ℕ), x7 < x2.output ∧ x8 < x2.output ∧ ∀ (x9 : List Bool), x9.length = x1 → x2.eval x9 = ((x2.wires x9).getD x7 Bool.false || (x2.wires x9).getD x8 Bool.false) := by
  intro n C hAO hle hlt hex
  obtain ⟨g, hg, hop⟩ := hex
  obtain ⟨_hAOO, hRB, h2⟩ := hAO
  have hj : C.output - n < C.gates.length := by
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hlt; omega
  obtain ⟨hj', hgj⟩ := List.getElem?_eq_some_iff.mp hg
  have hgmem : g ∈ C.gates := by rw [← hgj]; exact List.getElem_mem hj'
  have hlen := h2 g hgmem
  have hab : ∃ a b, g.inputs = [a, b] := by
    match hh : g.inputs with
    | [a, b] => exact ⟨a, b, rfl⟩
    | [] => simp [hh] at hlen
    | [_] => simp [hh] at hlen
    | _ :: _ :: _ :: _ => simp [hh] at hlen
  obtain ⟨a, b, hab⟩ := hab
  have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - n) = g := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hg]
  have hRB' := hRB (C.output - n) hj
  rw [hgat, hab] at hRB'
  have ha : a < C.output := by
    have := hRB' a (by simp); omega
  have hb : b < C.output := by
    have := hRB' b (by simp); omega
  refine ⟨a, b, ha, hb, ?_⟩
  intro x hx
  have hw : C.wires x = C.gates.foldl PEqualNP.Outside.L_meta_9043.stepF x := rfl
  have hsplit : C.gates = C.gates.take (C.output - n) ++ g :: C.gates.drop (C.output - n + 1) := by
    have hd : C.gates.drop (C.output - n) = g :: C.gates.drop (C.output - n + 1) := by
      rw [List.drop_eq_getElem_cons hj', hgj]
    rw [← hd, List.take_append_drop]
  obtain ⟨t0, hW, hl0⟩ := PEqualNP.Outside.L_meta_9043.fold_prefix (C.gates.take (C.output - n)) x
  obtain ⟨t1, h1, _⟩ := PEqualNP.Outside.L_meta_9043.fold_prefix (C.gates.drop (C.output - n + 1))
    (PEqualNP.Outside.L_meta_9043.stepF ((C.gates.take (C.output - n)).foldl
      PEqualNP.Outside.L_meta_9043.stepF x) g)
  have hfold : C.gates.foldl PEqualNP.Outside.L_meta_9043.stepF x =
      (C.gates.drop (C.output - n + 1)).foldl PEqualNP.Outside.L_meta_9043.stepF
        (PEqualNP.Outside.L_meta_9043.stepF ((C.gates.take (C.output - n)).foldl
          PEqualNP.Outside.L_meta_9043.stepF x) g) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  generalize hWdef : (C.gates.take (C.output - n)).foldl PEqualNP.Outside.L_meta_9043.stepF x = W
    at hW h1 hfold
  have hWlen : W.length = C.output := by
    rw [hW]; simp [hl0, hx, List.length_take]; omega
  have hwires : C.wires x = W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)] ++ t1 := by
    rw [hw, hfold, h1]; rfl
  have heval : C.eval x = (C.wires x).getD C.output false := rfl
  rw [heval, hwires]
  rw [PEqualNP.Outside.L_meta_9043.getD_left W t1 _ a (by omega),
    PEqualNP.Outside.L_meta_9043.getD_left W t1 _ b (by omega)]
  rw [← hWlen, PEqualNP.Outside.L_meta_9043.getD_mid]
  simp [hop, hab, PEqualNP.CircuitLowerBounds.GateOp.eval]
