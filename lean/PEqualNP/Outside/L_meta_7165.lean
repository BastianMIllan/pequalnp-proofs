import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7165

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Each gate that reads a wire not yet computed (such a wire reads false) is rewritten:
-- an AND gate becomes the constant false (an OR gate with no input), an OR gate drops those reads.

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

def fix (m : ℕ) : Gate → Gate
  | ⟨GateOp.and, ins⟩ =>
      if ins.all (fun i => decide (i < m)) then ⟨GateOp.and, ins⟩ else ⟨GateOp.or, []⟩
  | ⟨GateOp.or, ins⟩ => ⟨GateOp.or, ins.filter (fun i => decide (i < m))⟩
  | g => g

def fixL (n : ℕ) : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => fix (n + k) g :: fixL n (k + 1) gs

lemma fixL_length (n : ℕ) : ∀ (gs : List Gate) (k : ℕ), (fixL n k gs).length = gs.length := by
  intro gs
  induction gs with
  | nil => intro k; rfl
  | cons g gs ih => intro k; simp [fixL, ih]

lemma mem_fixL (n : ℕ) : ∀ (gs : List Gate) (k : ℕ) (g : Gate), g ∈ fixL n k gs →
    ∃ g' ∈ gs, ∃ m, g = fix m g' := by
  intro gs
  induction gs with
  | nil => intro k g h; simp [fixL] at h
  | cons a gs ih =>
    intro k g h
    simp only [fixL, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨a, List.mem_cons_self .., n + k, h⟩
    · obtain ⟨g', hg', m, hm⟩ := ih (k + 1) g h
      exact ⟨g', List.mem_cons_of_mem _ hg', m, hm⟩

lemma or_filter (f : ℕ → Bool) (m : ℕ) : ∀ (l : List ℕ), (∀ i ∈ l, ¬ i < m → f i = false) →
    ((l.filter (fun i => decide (i < m))).map f).any id = (l.map f).any id := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    have ih' := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    by_cases ha : a < m
    · simp only [List.filter_cons, ha, decide_true, ite_true, List.map_cons, List.any_cons, ih']
    · have hf := h a (List.mem_cons_self ..) ha
      simp only [List.filter_cons, ha, decide_false, Bool.false_eq_true, ite_false,
        List.map_cons, List.any_cons, ih', hf, id, Bool.false_or]

lemma gate_eq (w : List Bool) (m : ℕ) (hw : w.length = m) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (fix m g).op.eval ((fix m g).inputs.map fun i => w.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, ins⟩ := g
  simp only at hg
  rcases hg with rfl | rfl
  · by_cases h : ins.all (fun i => decide (i < m)) = true
    · simp only [fix, h, ite_true]
    · simp only [fix, h, Bool.false_eq_true, ite_false]
      simp only [List.all_eq_true, decide_eq_true_eq, not_forall] at h
      obtain ⟨i, hi, hlt⟩ := h
      have hd : w.getD i false = false := List.getD_eq_default _ _ (by omega)
      symm
      show (ins.map fun i => w.getD i false).all id = ([].map fun i => w.getD i false).any id
      simp only [List.map_nil, List.any_nil]
      rw [List.all_eq_false]
      exact ⟨w.getD i false, List.mem_map.2 ⟨i, hi, rfl⟩, by simp only [id]; rw [hd]; decide⟩
  · show ((ins.filter (fun i => decide (i < m))).map fun i => w.getD i false).any id
      = (ins.map fun i => w.getD i false).any id
    apply or_filter
    intro i _ hi
    exact List.getD_eq_default _ _ (by omega)

lemma fold_eq (n : ℕ) : ∀ (gs : List Gate) (k : ℕ) (w : List Bool), w.length = n + k →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (fixL n k gs).foldl stepW w = gs.foldl stepW w := by
  intro gs
  induction gs with
  | nil => intro k w _ _; rfl
  | cons g gs ih =>
    intro k w hw hops
    simp only [fixL, List.foldl_cons]
    have hs : stepW w (fix (n + k) g) = stepW w g := by
      unfold stepW
      rw [gate_eq w (n + k) hw g (hops g (List.mem_cons_self ..))]
    rw [hs]
    apply ih (k + 1)
    · simp [stepW, hw]; omega
    · intro g' hg'; exact hops g' (List.mem_cons_of_mem _ hg')

lemma fix_inputs (m : ℕ) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i ∈ (fix m g).inputs, i < m := by
  obtain ⟨op, ins⟩ := g
  simp only at hg
  rcases hg with rfl | rfl
  · by_cases h : ins.all (fun i => decide (i < m)) = true
    · simp only [fix, h, ite_true]
      simp only [List.all_eq_true, decide_eq_true_eq] at h
      exact h
    · simp [fix, h]
  · intro i hi
    simp only [fix, List.mem_filter, decide_eq_true_eq] at hi
    exact hi.2

lemma fix_mono (m : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (fix m g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (fix m g).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨h1, h2⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  rcases h1 with rfl | rfl
  · by_cases h : ins.all (fun i => decide (i < m)) = true
    · simp only [fix, h, ite_true]
      exact ⟨by simp, h2⟩
    · simp [fix, h]
  · simp only [fix]
    exact ⟨by simp, le_trans (List.length_filter_le _ _) h2⟩

lemma reads (n : ℕ) : ∀ (gs : List Gate) (k j : ℕ), j < gs.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ i ∈ ((fixL n k gs).getD j ⟨GateOp.or, []⟩).inputs, i < n + k + j := by
  intro gs
  induction gs with
  | nil => intro k j hj; simp at hj
  | cons g gs ih =>
    intro k j hj hops i hi
    cases j with
    | zero =>
      simp only [fixL, List.getD_cons_zero] at hi
      have := fix_inputs (n + k) g (hops g (List.mem_cons_self ..)) i hi
      omega
    | succ j =>
      simp only [fixL, List.getD_cons_succ] at hi
      have := ih (k + 1) j (by simp at hj; omega)
        (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg')) i hi
      omega

theorem main (n : ℕ) (C : Circuit) (hC : Monotone2 C) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  refine ⟨⟨fixL n 0 C.gates, C.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', m, rfl⟩ := mem_fixL n C.gates 0 g hg
    exact fix_mono m g' (hC g' hg')
  · intro j hj i hi
    have hj' : j < C.gates.length := by
      have : j < (fixL n 0 C.gates).length := hj
      rwa [fixL_length] at this
    have := reads n C.gates 0 j hj' hops i hi
    omega
  · show (fixL n 0 C.gates).length ≤ C.gates.length
    rw [fixL_length]
  · intro x
    unfold Circuit.eval
    rw [wires_eq, wires_eq]
    show ((fixL n 0 C.gates).foldl stepW (List.ofFn x)).getD C.output false = _
    rw [fold_eq n C.gates 0 (List.ofFn x) (by simp) hops]

end PEqualNP.Outside.L_meta_7165

theorem PEqualNP.Outside.L_meta_7165 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x4 ∧ x4.size ≤ x2.size ∧ ∀ (x5 : Fin x1 → Bool), x4.eval (List.ofFn x5) = x2.eval (List.ofFn x5) := by
  intro n C hC
  exact PEqualNP.Outside.L_meta_7165.main n C hC
