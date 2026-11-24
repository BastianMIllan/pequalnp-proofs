import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3452
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wf_append (A B : List Gate) (w : List Bool) : wf (A ++ B) w = wf B (wf A w) := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    rw [wf_cons, ih]
    simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [wf_cons, ih _ i (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

def sh (n k : ℕ) (w : ℕ) : ℕ := if w < n then w else w + k

def shg (n k : ℕ) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map (sh n k) }

theorem step (n k : ℕ) : ∀ (gs : List Gate) (w v : List Bool), n ≤ w.length →
    v.length = w.length + k →
    (∀ i, v.getD (sh n k i) false = w.getD i false) →
    ∀ i, (wf (gs.map (shg n k)) v).getD (sh n k i) false = (wf gs w).getD i false := by
  intro gs
  induction gs with
  | nil => intro w v _ _ h; simpa [wf] using h
  | cons g gs ih =>
    intro w v hn hl h
    rw [List.map_cons, wf_cons, wf_cons]
    have hv : (shg n k g).op.eval ((shg n k g).inputs.map fun j => v.getD j false)
        = g.op.eval (g.inputs.map fun j => w.getD j false) := by
      simp only [shg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h j
    rw [hv]
    apply ih
    · simp; omega
    · simp; omega
    · intro i
      rcases lt_trichotomy i w.length with hi | hi | hi
      · have hs : sh n k i < v.length := by
          unfold sh; split_ifs <;> omega
        rw [getD_snoc_lt _ _ _ hs, getD_snoc_lt _ _ _ hi]
        exact h i
      · have hs : sh n k i = v.length := by
          unfold sh; split_ifs <;> omega
        rw [hs, hi, getD_snoc_eq, getD_snoc_eq]
      · have hs : v.length < sh n k i := by
          unfold sh; split_ifs <;> omega
        rw [getD_snoc_gt _ _ _ hs, getD_snoc_gt _ _ _ hi]

end PEqualNP.Outside.L_meta_3452

open PEqualNP.Outside.L_meta_3452 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3452 : ∀ (n : ℕ) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin n → Bool), (∀ i < G0.length, ∀ w ∈ (G0.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w < n + i) → (∀ i : ℕ, ((⟨G0 ++ C.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map (fun w => if w < n then w else w + G0.length) } : PEqualNP.CircuitLowerBounds.Gate)), C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (if i < n then i else i + G0.length) false = (C.wires (List.ofFn x)).getD i false) ∧ (∀ i < G0.length, ((⟨G0 ++ C.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map (fun w => if w < n then w else w + G0.length) } : PEqualNP.CircuitLowerBounds.Gate)), C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (n + i) false = ((⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (n + i) false) := by
  intro n G0 C x _
  constructor
  · intro i
    show (wf (G0 ++ C.gates.map (shg n G0.length)) (List.ofFn x)).getD (sh n G0.length i) false
      = (wf C.gates (List.ofFn x)).getD i false
    rw [wf_append]
    apply step n G0.length C.gates (List.ofFn x) (wf G0 (List.ofFn x)) (by simp)
      (by rw [wf_len])
    intro j
    unfold sh
    split_ifs with hj
    · exact wf_keep G0 _ j (by simp; exact hj)
    · rw [List.getD_eq_default _ _ (by rw [wf_len]; simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  · intro i hi
    show (wf (G0 ++ C.gates.map (shg n G0.length)) (List.ofFn x)).getD (n + i) false
      = (wf G0 (List.ofFn x)).getD (n + i) false
    rw [wf_append]
    exact wf_keep _ _ _ (by rw [wf_len]; simp; omega)
