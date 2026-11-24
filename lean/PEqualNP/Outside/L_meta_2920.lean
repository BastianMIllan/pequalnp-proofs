import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2920

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, step]; omega

lemma keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma beyond (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [len]; omega)]
  rfl

lemma atGate (gs : List Gate) (w : List Bool) (k : ℕ) (g : Gate) (hk : gs[k]? = some g)
    (m : ℕ) (hm : m = w.length + k) :
    (gs.foldl step w).getD m false =
      g.op.eval (g.inputs.map fun i => if i < m then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w k m with
  | nil => simp at hk
  | cons h gs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      subst hm
      simp only [List.foldl_cons]
      rw [keep gs (step w h) _ (by simp [step])]
      have e1 : (step w h).getD (w.length + 0) false =
          h.op.eval (h.inputs.map fun i => w.getD i false) := by
        simp [step, List.getD_eq_getElem?_getD]
      rw [e1]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [keep gs (step w h) i (by simp [step]; omega)]
        simp only [step, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega : i < w.length)]
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      simp only [List.foldl_cons]
      exact ih (step w h) k hk m (by simp [step]; omega)

lemma boolId (op1 op2 : GateOp)
    (hop : (op1 = GateOp.and ∧ op2 = GateOp.or) ∨ (op1 = GateOp.or ∧ op2 = GateOp.and))
    (A B C Z : Bool) :
    op1.eval [op2.eval [A, op1.eval [B, C]], Z] =
        op1.eval [op2.eval [A, B], op1.eval [op2.eval [A, C], Z]] ∧
      op1.eval [op2.eval [A, op1.eval [B, C]], Z] =
        op1.eval [op1.eval [op2.eval [A, C], Z], op2.eval [A, B]] := by
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases A <;> cases B <;> cases C <;> cases Z <;> decide

lemma idxLt (gs : List Gate) (k : ℕ) (g : Gate) (h : gs[k]? = some g) : k < gs.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  simp at h

lemma main (gs : List Gate) (w : List Bool) (n j is iv iw a b c z : ℕ) (op1 op2 : GateOp)
    (hn : w.length = n)
    (hop : (op1 = GateOp.and ∧ op2 = GateOp.or) ∨ (op1 = GateOp.or ∧ op2 = GateOp.and))
    (hs : gs[is]? = some ⟨op2, [a, b]⟩) (hv : gs[iv]? = some ⟨op2, [a, c]⟩)
    (hw : gs[iw]? = some ⟨op1, [n + iv, z]⟩)
    (hj : gs[j]? = some ⟨op1, [n + is, n + iw]⟩ ∨ gs[j]? = some ⟨op1, [n + iw, n + is]⟩)
    (h1 : is < j) (h2 : iv < iw) (h3 : iw < j) (ha : a < n + is) (hb : b < n + is)
    (ha2 : a < n + iv) (hb2 : b < n + iv) (hc : c < n + iv) (hz : z < n + iw) (hz2 : z ≠ n + iv)
    (rv : ∀ k g, gs[k]? = some g → k ≠ iw → n + iv ∉ g.inputs)
    (rdw : ∀ k g, gs[k]? = some g → k ≠ j → n + iw ∉ g.inputs)
    (O N : List Bool) (hO : O = gs.foldl step w)
    (hN : N = (((gs.set iv ⟨op1, [b, c]⟩).set iw ⟨op2, [a, n + iv]⟩).set j
      ⟨op1, [n + iw, z]⟩).foldl step w) :
    ∀ i, N.getD i false = if i = n + iv then op1.eval [O.getD b false, O.getD c false]
      else if i = n + iw then op2.eval [O.getD a false, op1.eval [O.getD b false, O.getD c false]]
      else O.getD i false := by
  set gs' := ((gs.set iv ⟨op1, [b, c]⟩).set iw ⟨op2, [a, n + iv]⟩).set j ⟨op1, [n + iw, z]⟩
    with hgs'
  have lenEq : gs'.length = gs.length := by simp [gs']
  have ivL := idxLt gs iv _ hv
  have iwL := idxLt gs iw _ hw
  have jL : j < gs.length := by
    rcases hj with h | h
    · exact idxLt gs j _ h
    · exact idxLt gs j _ h
  have NG : ∀ k g, gs'[k]? = some g → N.getD (n + k) false =
      g.op.eval (g.inputs.map fun i => if i < n + k then N.getD i false else false) := by
    intro k g hk
    rw [hN]
    exact atGate gs' w k g hk (n + k) (by omega)
  have OG : ∀ k g, gs[k]? = some g → O.getD (n + k) false =
      g.op.eval (g.inputs.map fun i => if i < n + k then O.getD i false else false) := by
    intro k g hk
    rw [hO]
    exact atGate gs w k g hk (n + k) (by omega)
  have g'j : gs'[j]? = some ⟨op1, [n + iw, z]⟩ := by
    simp [gs', List.getElem?_set, jL]
  have g'iw : gs'[iw]? = some ⟨op2, [a, n + iv]⟩ := by
    rw [hgs', List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
  have g'iv : gs'[iv]? = some ⟨op1, [b, c]⟩ := by
    rw [hgs', List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by omega)]
  have g'o : ∀ k, k ≠ iv → k ≠ iw → k ≠ j → gs'[k]? = gs[k]? := by
    intro k k1 k2 k3
    simp [gs', List.getElem?_set, Ne.symm k1, Ne.symm k2, Ne.symm k3, k1, k2, k3]
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hlo : i < n
    · rw [if_neg (by omega), if_neg (by omega), hN, hO, keep _ _ _ (by omega),
        keep _ _ _ (by omega)]
    by_cases hhi : n + gs.length ≤ i
    · rw [if_neg (by omega), if_neg (by omega), hN, hO, beyond _ _ _ (by rw [lenEq]; omega),
        beyond _ _ _ (by omega)]
    obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
    have nOf : ∀ m, m < n + k → m ≠ n + iv → m ≠ n + iw → N.getD m false = O.getD m false := by
      intro m hm m1 m2
      rw [ih m hm, if_neg m1, if_neg m2]
    by_cases kv : k = iv
    · subst kv
      rw [if_pos rfl, NG _ _ g'iv]
      simp only [List.map_cons, List.map_nil, if_pos hb2, if_pos hc]
      rw [nOf b hb2 (by omega) (by omega), nOf c hc (by omega) (by omega)]
    by_cases kw : k = iw
    · subst kw
      rw [if_neg (by omega), if_pos rfl, NG _ _ g'iw]
      simp only [List.map_cons, List.map_nil, if_pos (by omega : a < n + k),
        if_pos (by omega : n + iv < n + k)]
      rw [nOf a (by omega) (by omega) (by omega), ih (n + iv) (by omega), if_pos rfl]
    by_cases kj : k = j
    · subst kj
      rw [if_neg (by omega), if_neg (by omega), NG _ _ g'j]
      simp only [List.map_cons, List.map_nil, if_pos (by omega : n + iw < n + k),
        if_pos (by omega : z < n + k)]
      rw [ih (n + iw) (by omega), if_neg (by omega), if_pos rfl,
        nOf z (by omega) hz2 (by omega)]
      have Os : O.getD (n + is) false = op2.eval [O.getD a false, O.getD b false] := by
        rw [OG _ _ hs]
        simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb]
      have Ov : O.getD (n + iv) false = op2.eval [O.getD a false, O.getD c false] := by
        rw [OG _ _ hv]
        simp only [List.map_cons, List.map_nil, if_pos ha2, if_pos hc]
      have Ow : O.getD (n + iw) false = op1.eval [O.getD (n + iv) false, O.getD z false] := by
        rw [OG _ _ hw]
        simp only [List.map_cons, List.map_nil, if_pos (by omega : n + iv < n + iw), if_pos hz]
      have bi := boolId op1 op2 hop (O.getD a false) (O.getD b false) (O.getD c false)
        (O.getD z false)
      rcases hj with hj | hj
      · rw [OG _ _ hj]
        simp only [List.map_cons, List.map_nil, if_pos (by omega : n + is < n + k),
          if_pos (by omega : n + iw < n + k)]
        rw [Os, Ow, Ov]
        exact bi.1
      · rw [OG _ _ hj]
        simp only [List.map_cons, List.map_nil, if_pos (by omega : n + is < n + k),
          if_pos (by omega : n + iw < n + k)]
        rw [Os, Ow, Ov]
        exact bi.2
    · rw [if_neg (by omega), if_neg (by omega)]
      have kL : k < gs.length := by omega
      obtain ⟨g, hg⟩ : ∃ g, gs[k]? = some g := ⟨gs[k], List.getElem?_eq_getElem kL⟩
      rw [NG _ _ (by rw [g'o k kv kw kj]; exact hg), OG _ _ hg]
      congr 1
      apply List.map_congr_left
      intro m hm
      split_ifs with hmk
      · exact nOf m hmk (fun e => rv k g hg kw (e ▸ hm)) (fun e => rdw k g hg kj (e ▸ hm))
      · rfl

end PEqualNP.Outside.L_meta_2920

theorem PEqualNP.Outside.L_meta_2920 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j is iv iw a b c z : ℕ)
    (op1 op2 : PEqualNP.CircuitLowerBounds.GateOp),
  ((op1 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ op2 = PEqualNP.CircuitLowerBounds.GateOp.or) ∨
    (op1 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ op2 = PEqualNP.CircuitLowerBounds.GateOp.and)) →
  C.gates[is]? = some { op := op2, inputs := [a, b] } →
  C.gates[iv]? = some { op := op2, inputs := [a, c] } →
  C.gates[iw]? = some { op := op1, inputs := [n + iv, z] } →
  (C.gates[j]? = some { op := op1, inputs := [n + is, n + iw] } ∨
    C.gates[j]? = some { op := op1, inputs := [n + iw, n + is] }) →
  is < j → iv < iw → iw < j →
  a < n + is → b < n + is → a < n + iv → b < n + iv → c < n + iv →
  z < n + iw → z ≠ n + iv →
  (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → k ≠ iw → n + iv ∉ g.inputs) →
  (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → k ≠ j → n + iw ∉ g.inputs) →
  C.output ≠ n + iv → C.output ≠ n + iw →
  PEqualNP.MetaComplexity.circuitFun n
      { gates := ((C.gates.set iv { op := op1, inputs := [b, c] }).set iw
            { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] },
        output := C.output } =
    PEqualNP.MetaComplexity.circuitFun n C ∧
  (((C.gates.set iv { op := op1, inputs := [b, c] }).set iw
      { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] }).length =
    C.gates.length := by
  intro n C j is iv iw a b c z op1 op2 hop hs hv hw hj h1 h2 h3 ha hb ha2 hb2 hc hz hz2 rv rdw o1 o2
  refine ⟨?_, by simp⟩
  funext x
  have key := PEqualNP.Outside.L_meta_2920.main C.gates (List.ofFn x) n j is iv iw a b c z op1 op2
    (by simp) hop hs hv hw hj h1 h2 h3 ha hb ha2 hb2 hc hz hz2 rv rdw _ _ rfl rfl C.output
  rw [if_neg o1, if_neg o2] at key
  exact key
