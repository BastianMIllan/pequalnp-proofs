import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6454

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def clampGates : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => ⟨g.op, g.inputs.map (fun i => min i k)⟩ :: clampGates (k + 1) gs

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma clampGates_length (k : ℕ) (gs : List Gate) : (clampGates k gs).length = gs.length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih => simp [clampGates, ih]

lemma clampGates_fold (gs : List Gate) (k : ℕ) (w : List Bool) (hw : w.length = k) :
    (clampGates k gs).foldl step w = gs.foldl step w := by
  induction gs generalizing k w with
  | nil => rfl
  | cons g gs ih =>
    simp only [clampGates, List.foldl_cons]
    have hs : step w ⟨g.op, g.inputs.map (fun i => min i k)⟩ = step w g := by
      simp only [step, List.map_map]
      congr 3
      apply List.map_congr_left
      intro i _
      simp only [Function.comp]
      by_cases hik : i < k
      · rw [min_eq_left (le_of_lt hik)]
      · rw [min_eq_right (by omega), getD_ge_len w k (by omega), getD_ge_len w i (by omega)]
    rw [hs]
    apply ih (k + 1)
    simp [step, hw]

lemma clampGates_mem (gs : List Gate) (k : ℕ) :
    ∀ g ∈ clampGates k gs, ∃ g0 ∈ gs, g.op = g0.op ∧ g.inputs.length = g0.inputs.length := by
  induction gs generalizing k with
  | nil => intro g hg; simp [clampGates] at hg
  | cons g gs ih =>
    intro g' hg'
    simp only [clampGates, List.mem_cons] at hg'
    rcases hg' with h | h
    · exact ⟨g, by simp, by rw [h], by rw [h]; simp⟩
    · obtain ⟨g0, hg0, h1, h2⟩ := ih (k + 1) g' h
      exact ⟨g0, List.mem_cons_of_mem _ hg0, h1, h2⟩

lemma clampGates_bound (gs : List Gate) (k : ℕ) :
    ∀ (j : ℕ) (hj : j < (clampGates k gs).length),
      ∀ a ∈ ((clampGates k gs)[j]'hj).inputs, a ≤ k + j := by
  induction gs generalizing k with
  | nil => intro j hj; simp [clampGates] at hj
  | cons g gs ih =>
    intro j hj a ha
    cases j with
    | zero =>
      simp only [clampGates, List.getElem_cons_zero, List.mem_map] at ha
      obtain ⟨i, _, rfl⟩ := ha
      omega
    | succ j =>
      simp only [clampGates, List.getElem_cons_succ] at ha
      have hj' : j < (clampGates (k + 1) gs).length := by
        simp only [clampGates, List.length_cons] at hj; omega
      have := ih (k + 1) j hj' a ha
      omega

lemma fold_pad (n : ℕ) (w : List Bool) :
    (List.replicate n (⟨GateOp.or, []⟩ : Gate)).foldl step w = w ++ List.replicate n false := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons, ih]
    simp [step, GateOp.eval, List.replicate_succ]

lemma getD_append_rep (l : List Bool) (n i : ℕ) :
    (l ++ List.replicate n false).getD i false = l.getD i false := by
  by_cases hi : i < l.length
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  · rw [getD_ge_len l i (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_replicate]
    split_ifs <;> simp

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

end PEqualNP.Outside.L_meta_6454

open PEqualNP.Outside.L_meta_6454 in
theorem PEqualNP.Outside.L_meta_6454 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x3.size ≤ x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x6.size = x2 ∧ PEqualNP.MetaComplexity.Monotone2 x6 ∧ (∀ (x7 : Fin x6.gates.length), ∀ x8 ∈ (x6.gates.get x7).inputs, x8 ≤ x1 + ↑x7) ∧ ∀ (x7 : List Bool), x7.length = x1 → ∀ (x9 : ℕ), (x6.wires x7).getD x9 Bool.false = (x3.wires x7).getD x9 Bool.false := by
  intro x1 x2 x3 hmono hsize
  refine ⟨⟨clampGates x1 x3.gates ++
      List.replicate (x2 - x3.size) (⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ :
        PEqualNP.CircuitLowerBounds.Gate), x3.output⟩, ?_, ?_, ?_, ?_⟩
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append,
      clampGates_length, List.length_replicate]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hsize
    omega
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · obtain ⟨g0, hg0, h1, h2⟩ := clampGates_mem x3.gates x1 g h
      obtain ⟨ha, hb⟩ := hmono g0 hg0
      exact ⟨h1 ▸ ha, h2 ▸ hb⟩
    · rw [List.eq_of_mem_replicate h]
      simp
  · intro j a ha
    simp only [List.get_eq_getElem] at ha
    by_cases hj : j.val < (clampGates x1 x3.gates).length
    · rw [List.getElem_append_left hj] at ha
      exact clampGates_bound x3.gates x1 j.val hj a ha
    · rw [List.getElem_append_right (by omega)] at ha
      simp at ha
  · intro x hx i
    rw [wires_eq, wires_eq]
    simp only [List.foldl_append]
    rw [fold_pad, getD_append_rep, clampGates_fold x3.gates x1 x hx]
