import Mathlib
import PEqualNP.Defs

-- The wire sets of a monotone circuit: wire n holds the points where wire n is true;
-- the gate wires are intersections or unions of two earlier wires by the fold argument.
namespace PEqualNP.Outside.L_meta_5845

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem run_keeps (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem run_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (earlier : ∀ i ∈ gs[j].inputs, i < w.length + j) :
    (run gs w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run gs w).getD i false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero] at earlier ⊢
      change (run gs (step w g)).getD w.length false = _
      rw [run_keeps _ _ _ (by simp [step]), step, List.getD_append_right _ _ _ _ (Nat.le_refl _),
        Nat.sub_self]
      change g.op.eval (g.inputs.map fun i => w.getD i false) = _
      congr 1
      apply List.map_congr_left
      intro i hi
      exact (run_keeps _ _ _ (earlier i hi)).symm
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have len : (step w g).length + j = w.length + (j + 1) := by simp [step]; omega
      have earlier' : ∀ i ∈ gs[j].inputs, i < (step w g).length + j := by
        simpa only [List.getElem_cons_succ, len] using earlier
      change (run gs (step w g)).getD (w.length + (j + 1)) false = _
      rw [← len]
      exact ih (step w g) j hj' earlier'

theorem raw_wire {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

end PEqualNP.Outside.L_meta_5845

open PEqualNP.Outside.L_meta_5845 in
theorem PEqualNP.Outside.L_meta_5845 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Type) (x4 : x3 → Fin x1 → Bool), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x7 → ∃ (x9 : ℕ) (x10 : ℕ), x7.inputs = [x9, x10] ∧ x9 < x10 ∧ x10 < x1 + x6) → ∃ (x7 : ℕ → Set x3), (∀ (x8 : Fin x1), x7 ↑x8 = {x9 : x3 | x4 x9 x8 = Bool.true}) ∧ (∀ x8 < x2.size, ∃ (x10 : ℕ) (x11 : ℕ), x10 < x11 ∧ x11 < x1 + x8 ∧ (x7 (x1 + x8) = x7 x10 ∩ x7 x11 ∨ x7 (x1 + x8) = x7 x10 ∪ x7 x11)) ∧ ∀ (x8 : x3), x8 ∈ x7 x2.output ↔ PEqualNP.MetaComplexity.circuitFun x1 x2 (x4 x8) = Bool.true := by
  intro n C X f hmono hord
  refine ⟨fun k => {x | (run C.gates (List.ofFn (f x))).getD k false = true}, ?_, ?_, ?_⟩
  · intro i
    ext x
    simp only [Set.mem_setOf_eq]
    rw [run_keeps _ _ _ (by simp), raw_wire]
  · intro g hg
    have hg' : g < C.gates.length := hg
    obtain ⟨a, b, hin, hab, hb⟩ := hord g C.gates[g] (List.getElem?_eq_getElem hg')
    refine ⟨a, b, hab, hb, ?_⟩
    have key : ∀ x : X, (run C.gates (List.ofFn (f x))).getD (n + g) false =
        C.gates[g].op.eval [(run C.gates (List.ofFn (f x))).getD a false,
          (run C.gates (List.ofFn (f x))).getD b false] := by
      intro x
      have h := run_gate C.gates (List.ofFn (f x)) g hg' (by
        intro i hi
        rw [hin] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        simp only [List.length_ofFn]
        omega)
      rw [List.length_ofFn] at h
      rw [h, hin]
      rfl
    have hop := (hmono C.gates[g] (List.getElem_mem hg')).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hop | hop
    · left
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, key x, hop, PEqualNP.CircuitLowerBounds.GateOp.eval]
      simp
    · right
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_union, key x, hop, PEqualNP.CircuitLowerBounds.GateOp.eval]
      simp
  · intro x
    rfl
