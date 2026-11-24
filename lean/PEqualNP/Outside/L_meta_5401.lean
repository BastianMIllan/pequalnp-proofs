import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5401

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma scan_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ p p' : List α, (∀ i < w.length + j, p.getD i d = p'.getD i d) →
      step p gs[j] = step p' gs[j]) :
    (scan step gs w).getD (w.length + j) d = step (scan step gs w) gs[j] := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan step gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_prefix step (gs[j] :: gs.drop (j + 1)) pre d i (by omega)
  have hres : (scan step gs w).getD (w.length + j) d = step pre gs[j] := by
    rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) (pre ++ [step pre gs[j]]) d (w.length + j) (by simp [hp])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp only [List.getD_cons_zero]
  rw [hres]
  exact hstep pre (scan step gs w) (fun i hi => (hpre i hi).symm)

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

lemma wires_eq_scan (C : Circuit) (x : List Bool) :
    C.wires x = scan boolStep C.gates x := rfl

lemma list_eq_two {l : List ℕ} (hl : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at hl ⊢

lemma gateAt_eq_getElem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

lemma ao2_gate_props {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.1 C.gates[j] hmem
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.2.2 C.gates[j] hmem
  have hin : (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    simpa [opnd] using list_eq_two hlen
  have hrb := hAO2.2.1 j hj
  have h0 : opnd C j 0 < n + j := hrb (opnd C j 0) (by rw [hin]; simp)
  have h1 : opnd C j 1 < n + j := hrb (opnd C j 1) (by rw [hin]; simp)
  exact ⟨hop, hin, h0, h1⟩

def wireVal (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wireVal_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_scan, scan_length, List.length_ofFn]

lemma wireVal_ge (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    wireVal n C w x = false := by
  rw [wireVal, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wireVal_length]; exact hw)]
  rfl

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wireVal n C i x = x ⟨i, hi⟩ := by
  rw [wireVal, wires_eq_scan, scan_prefix boolStep C.gates (List.ofFn x) false i (by simp [hi])]
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]

lemma wireVal_gate {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wireVal n C (n + j) x = boolStep (C.wires (List.ofFn x)) C.gates[j] := by
  rw [wireVal, wires_eq_scan]
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have h := scan_gate boolStep C.gates (List.ofFn x) false j hj (by
    intro q1 q2 hq
    simp only [boolStep]
    have hrb := hAO2.2.1 j hj
    have hcongr : C.gates[j].inputs.map (fun i => q1.getD i false) =
        C.gates[j].inputs.map (fun i => q2.getD i false) := by
      apply List.map_congr_left
      intro i hi
      apply hq
      rw [hlen]
      exact hrb i (by rw [gateAt_eq_getElem hj]; exact hi)
    rw [hcongr])
  simpa only [hlen] using h

lemma wireVal_or {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO2 x hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [boolStep, hop, hin, GateOp.eval, wireVal]

lemma wireVal_and {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO2 x hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [boolStep, hop, hin, GateOp.eval, wireVal]

lemma scan_bool_mono (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (lx ly : List Bool) (hlen : lx.length = ly.length)
    (hle : ∀ i, lx.getD i false = true → ly.getD i false = true) :
    (scan boolStep gs lx).length = (scan boolStep gs ly).length ∧
      ∀ w, (scan boolStep gs lx).getD w false = true → (scan boolStep gs ly).getD w false = true := by
  induction gs generalizing lx ly with
  | nil => exact ⟨hlen, hle⟩
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hAO g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or := fun g' hg' => hAO g' (by simp [hg'])
    have hstep : boolStep lx g = true → boolStep ly g = true := by
      intro h
      rcases hg with hop | hop
      · simp only [boolStep, hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply] at h ⊢
        intro i hi
        exact hle i (h i hi)
      · simp only [boolStep, hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply] at h ⊢
        rcases h with ⟨i, hi, hit⟩
        exact ⟨i, hi, hle i hit⟩
    have hlen' : (lx ++ [boolStep lx g]).length = (ly ++ [boolStep ly g]).length := by
      simp [hlen]
    have hle' : ∀ i, (lx ++ [boolStep lx g]).getD i false = true →
        (ly ++ [boolStep ly g]).getD i false = true := by
      intro i hi
      by_cases hil : i < lx.length
      · rw [List.getD_append _ _ _ _ hil] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact hle i hi
      · by_cases heq : i = lx.length
        · subst heq
          rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero] at hi
          rw [hlen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          exact hstep hi
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
          simp at hi
    exact ih hgs (lx ++ [boolStep lx g]) (ly ++ [boolStep ly g]) hlen' hle'

lemma wireVal_mono {n : ℕ} {C : Circuit} (hAO : AndOrOnly C) {x y : Fin n → Bool}
    (hxy : ∀ i : Fin n, x i = true → y i = true) (w : ℕ) :
    wireVal n C w x = true → wireVal n C w y = true := by
  have hle : ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
    intro i hi
    by_cases hin : i < n
    · rw [List.getD_eq_getElem _ _ (by simp [hin]), List.getElem_ofFn] at hi ⊢
      exact hxy ⟨i, hin⟩ hi
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
      simp at hi
  exact (scan_bool_mono C.gates hAO (List.ofFn x) (List.ofFn y) (by simp) hle).2 w
def tri {n : ℕ} (u v w : Fin n) : Fin n → Bool := fun i => decide (i = u ∨ i = v ∨ i = w)

lemma main_aux (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (t : ℕ)
    (b : Fin 2) (u v w : Fin n) (hAO2 : IsAO2 n C) (ht : t < C.gates.length)
    (hop : (gateAt C t).op = GateOp.and) (hBF : BelowF G C t) (hnadj : ¬ G.Adj u v)
    (h1 : wireVal n C (opnd C t b) (pairInput u v) = true)
    (h2 : wireVal n C (opnd C t (1 - b)) (pairInput w w) = true) :
    w ≠ u ∧ w ≠ v ∧ (G.Adj u w ∨ G.Adj v w) := by
  have hx1 : wireVal n C (opnd C t b) (tri u v w) = true := by
    refine wireVal_mono hAO2.1 ?_ _ h1
    intro i hi
    simp only [pairInput, tri, decide_eq_true_eq] at hi ⊢
    tauto
  have hx2 : wireVal n C (opnd C t (1 - b)) (tri u v w) = true := by
    refine wireVal_mono hAO2.1 ?_ _ h2
    intro i hi
    simp only [pairInput, tri, decide_eq_true_eq] at hi ⊢
    tauto
  have hand : (wireVal n C (opnd C t 0) (tri u v w) && wireVal n C (opnd C t 1) (tri u v w)) = true := by
    have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
    rcases hb with rfl | rfl
    · have e : (1 : Fin 2) - 0 = 1 := by decide
      rw [e] at hx2
      simp [hx1, hx2]
    · have e : (1 : Fin 2) - 1 = 0 := by decide
      rw [e] at hx2
      simp [hx1, hx2]
  have hT : PEqualNP.EdgeOwnership.gateVal n C t (tri u v w) = true := by
    show wireVal n C (n + t) (tri u v w) = true
    rw [wireVal_and hAO2 (tri u v w) ht hop]
    exact hand
  have hF := hBF (tri u v w) hT
  have hF2 : ∃ p q, G.Adj p q ∧ tri u v w p = true ∧ tri u v w q = true := by
    simpa [graphFun] using hF
  obtain ⟨p, q, hpq, hp, hq⟩ := hF2
  simp only [tri, decide_eq_true_eq] at hp hq
  rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq <;> rw [hp, hq] at hpq
  all_goals
    first
    | exact absurd hpq G.irrefl
    | exact absurd hpq hnadj
    | exact absurd hpq.symm hnadj
    | exact ⟨hpq.ne.symm, by intro h; subst h; exact hnadj hpq, Or.inl hpq⟩
    | exact ⟨hpq.ne, by intro h; subst h; exact hnadj hpq.symm, Or.inl hpq.symm⟩
    | exact ⟨by intro h; subst h; exact hnadj hpq.symm, hpq.ne.symm, Or.inr hpq⟩
    | exact ⟨by intro h; subst h; exact hnadj hpq, hpq.ne, Or.inr hpq.symm⟩

end PEqualNP.Outside.L_meta_5401

theorem PEqualNP.Outside.L_meta_5401 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (t : ℕ) (b : Fin 2) (u v w : Fin n), PEqualNP.TopForm.IsAO2 n C → t < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C t).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.BelowF G C t → u ≠ v → ¬ G.Adj u v → PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C t b) (PEqualNP.EdgeOwnership.pairInput u v) = true → PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C t (1 - b)) (PEqualNP.EdgeOwnership.pairInput w w) = true → w ≠ u ∧ w ≠ v ∧ (G.Adj u w ∨ G.Adj v w) := by
  intro n G _ C t b u v w hAO2 ht hop hBF _ hnadj h1 h2
  exact PEqualNP.Outside.L_meta_5401.main_aux n G C t b u v w hAO2 ht hop hBF hnadj h1 h2
