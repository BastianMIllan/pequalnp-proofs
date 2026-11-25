import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9039

open PEqualNP.CircuitLowerBounds

def F (x7 : Fin 10 → Bool) : Bool :=
  x7 0 && x7 1 || x7 1 && x7 2 || x7 2 && x7 3 || x7 3 && x7 4 || x7 4 && x7 0 ||
  x7 0 && x7 5 || x7 1 && x7 6 || x7 2 && x7 7 || x7 3 && x7 8 || x7 4 && x7 9 ||
  x7 5 && x7 7 || x7 7 && x7 9 || x7 9 && x7 6 || x7 6 && x7 8 || x7 8 && x7 5

def gv (x : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => x.getD i false)

theorem foldl_eq (x : List Bool) (gs : List Gate)
    (h : ∀ g ∈ gs, ∀ i ∈ g.inputs, i < x.length) : ∀ L : List Bool,
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (x ++ L)
      = x ++ L ++ gs.map (gv x) := by
  induction gs with
  | nil => intro L; simp
  | cons g gs ih =>
    intro L
    have hm : (g.inputs.map fun i => (x ++ L).getD i false) = g.inputs.map fun i => x.getD i false :=
      List.map_congr_left (fun i hi => List.getD_append _ _ _ _ (h g (by simp) i hi))
    simp only [List.foldl_cons, hm]
    rw [List.append_assoc, ih (fun g' hg' => h g' (by simp [hg'])) (L ++ _)]
    simp [gv]

theorem eval_eq (C : Circuit) (hout : 10 ≤ C.output)
    (hin : ∀ g ∈ C.gates, ∀ i ∈ g.inputs, i < 10) (x : Fin 10 → Bool) :
    C.eval (List.ofFn x) = ((C.gates.map (gv (List.ofFn x))).getD (C.output - 10) false) := by
  have h := foldl_eq (List.ofFn x) C.gates (by simpa using hin) []
  simp only [List.append_nil] at h
  unfold Circuit.eval Circuit.wires
  rw [h, List.getD_append_right _ _ _ _ (by simpa using hout)]
  simp

theorem mem_two (l : List ℕ) (hl : l.length ≤ 2) (i : ℕ) (hi : i ∈ l) :
    i = l.getD 0 0 ∨ i = l.getD 1 0 := by
  match l, hl with
  | [], _ => simp at hi
  | [u], _ => simp at hi; simp [hi]
  | [u, v], _ => simp at hi; rcases hi with hi | hi <;> simp [hi]

theorem getD_ofFn (y : Fin 10 → Bool) (i : ℕ) (hi : i < 10) :
    (List.ofFn y).getD i false = y ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

def y1 : Fin 10 → Bool := fun j => decide (j.val = 0) || decide (j.val = 1)
def y2 : Fin 10 → Bool := fun j => decide (j.val = 2) || decide (j.val = 3)
def y3 : Fin 10 → Bool := fun j => decide (j.val = 5) || decide (j.val = 7)
def y0 : Fin 10 → Bool := fun _ => false

theorem F1 : F y1 = true := by decide
theorem F2 : F y2 = true := by decide
theorem F3 : F y3 = true := by decide
theorem F0 : F y0 = false := by decide

theorem core (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hout : 10 ≤ C.output)
    (hin : ∀ g ∈ C.gates, ∀ i ∈ g.inputs, i < 10)
    (hall : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = F x) : False := by
  have key : ∀ y : Fin 10 → Bool, F y = true →
      (∀ g, C.gates[C.output - 10]? = some g → ∀ i ∈ g.inputs, ∀ h : i < 10, y ⟨i, h⟩ = false) →
      False := by
    intro y hy hz
    have e1 := hall y
    have e0 := hall y0
    rw [eval_eq C hout hin] at e1 e0
    rw [hy] at e1
    rw [F0] at e0
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at e1 e0
    cases hg : C.gates[C.output - 10]? with
    | none => simp [hg] at e1
    | some g =>
      simp only [hg, Option.map_some, Option.getD_some, gv] at e1 e0
      have hm : (g.inputs.map fun i => (List.ofFn y).getD i false)
          = g.inputs.map fun i => (List.ofFn y0).getD i false := by
        apply List.map_congr_left
        intro i hi
        have hgm : g ∈ C.gates := List.mem_of_getElem? hg
        have hi10 := hin g hgm i hi
        rw [getD_ofFn y i hi10, getD_ofFn y0 i hi10, hz g hg i hi hi10]
        rfl
      rw [hm, e0] at e1
      exact Bool.false_ne_true e1
  cases hg : C.gates[C.output - 10]? with
  | none =>
    exact key y1 F1 (fun g h => by rw [hg] at h; cases h)
  | some g =>
    have hgm : g ∈ C.gates := List.mem_of_getElem? hg
    have hlen := (hfan g hgm).2
    have h2 := mem_two g.inputs hlen
    have ha := fun i hi => hin g hgm i hi
    by_cases c1 : g.inputs.getD 0 0 ≠ 0 ∧ g.inputs.getD 0 0 ≠ 1 ∧
        g.inputs.getD 1 0 ≠ 0 ∧ g.inputs.getD 1 0 ≠ 1
    · refine key y1 F1 ?_
      intro g' hg' i hi h
      rw [hg] at hg'; cases hg'
      have := h2 i hi; simp only [y1, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    by_cases c2 : g.inputs.getD 0 0 ≠ 2 ∧ g.inputs.getD 0 0 ≠ 3 ∧
        g.inputs.getD 1 0 ≠ 2 ∧ g.inputs.getD 1 0 ≠ 3
    · refine key y2 F2 ?_
      intro g' hg' i hi h
      rw [hg] at hg'; cases hg'
      have := h2 i hi; simp only [y2, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    have c3 : g.inputs.getD 0 0 ≠ 5 ∧ g.inputs.getD 0 0 ≠ 7 ∧
        g.inputs.getD 1 0 ≠ 5 ∧ g.inputs.getD 1 0 ≠ 7 := by omega
    refine key y3 F3 ?_
    intro g' hg' i hi h
    rw [hg] at hg'; cases hg'
    have := h2 i hi; simp only [y3, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega

end PEqualNP.Outside.L_meta_9039

theorem PEqualNP.Outside.L_meta_9039 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (10 : ℕ) ≤ x1.output → (∀ x5 ∈ x1.gates, ∀ x7 ∈ x5.inputs, x7 < (10 : ℕ)) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x6) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C hfan _ hout hin
  by_contra hne
  replace hne : ∀ x, C.eval (List.ofFn x) = _ := fun x => by_contra fun h => hne ⟨x, h⟩
  exact PEqualNP.Outside.L_meta_9039.core C hfan hout hin hne
