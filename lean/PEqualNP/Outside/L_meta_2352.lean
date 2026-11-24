import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2352

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gateAt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map fun i =>
          if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have hg : C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
  have h := foldl_step_gate C.gates (List.ofFn x) j _ hg
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

end PEqualNP.Outside.L_meta_2352

theorem PEqualNP.Outside.L_meta_2352 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ∀ (top : ℕ) (L : List (ℕ × ℕ)) (z : Fin n → Bool), T top L → (∀ gv ∈ L, (C.wires (List.ofFn z)).getD (gv.1) false = true) → (C.wires (List.ofFn z)).getD (top) false = true := by
  intro n C hC R hR T hT top L z hTL hL
  obtain ⟨_, hRB, hlen⟩ := hC
  -- truth climbs an OR-only path
  have hpath : ∀ a b : ℕ, R a b → (C.wires (List.ofFn z)).getD a false = true →
      (C.wires (List.ofFn z)).getD b false = true := by
    intro a b hab
    rw [hR] at hab
    induction hab with
    | refl => exact id
    | tail _ hst ih =>
      intro ha
      obtain ⟨hlt, rj, rfl, hrj, hop, hmem⟩ := hst
      rw [PEqualNP.Outside.L_meta_2352.wires_gateAt C z rj hrj, hop]
      change (List.map _ _).any id = true
      rw [List.any_eq_true]
      refine ⟨_, List.mem_map_of_mem hmem, ?_⟩
      simp only [hlt, ↓reduceIte, id]
      exact ih ha
  subst hT
  refine hTL (fun t l => (∀ gv ∈ l, (C.wires (List.ofFn z)).getD (gv.1) false = true) →
      (C.wires (List.ofFn z)).getD t false = true) ?_ ?_ hL
  · intro qv qt _ _ h
    exact h (qt, qv) (by simp)
  · intro qj qt qL1 qL2 hqj hop hR' h1 h2 h
    have ha := h1 (fun gv hg => h gv (List.mem_append_left _ hg))
    have hb := h2 (fun gv hg => h gv (List.mem_append_right _ hg))
    apply hpath _ _ hR'
    have hmem : PEqualNP.MetaComplexity.NestedCover.gateAt C qj ∈ C.gates := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hqj]
    have h2len := hlen _ hmem
    have hback := hRB qj hqj
    rw [PEqualNP.Outside.L_meta_2352.wires_gateAt C z qj hqj, hop]
    revert ha hb hback
    generalize (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs = l at h2len ⊢
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp h2len
    intro ha hb hback
    have hra : a < n + qj := hback a (by simp)
    have hrb : b < n + qj := hback b (by simp)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at ha hb
    simp only [List.getD_eq_getElem?_getD] at ha hb
    change ([a, b].map _).all id = true
    simp [hra, hrb, ha, hb]
