import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7756

open PEqualNP.CircuitLowerBounds

def toGate (t : Bool × ℕ × ℕ) : Gate :=
  ⟨if t.1 = true then GateOp.or else GateOp.and, [t.2.1, t.2.2]⟩

def stepN (x9 : List ℕ) (x10 : Bool × ℕ × ℕ) : List ℕ :=
  x9 ++ [if x10.1 = true then x9.getD x10.2.1 0 ||| x9.getD x10.2.2 0
    else x9.getD x10.2.1 0 &&& x9.getD x10.2.2 0]

theorem getD_map_testBit (w : List ℕ) (i k : ℕ) :
    (w.map (fun n => n.testBit k)).getD i false = (w.getD i 0).testBit k := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp

theorem opt_testBit (o : Option ℕ) (k : ℕ) :
    (Option.map (fun n => n.testBit k) o).getD false = (o.getD 0).testBit k := by
  cases o <;> simp

theorem fold_sim (k : ℕ) : ∀ (ts : List (Bool × ℕ × ℕ)) (w : List ℕ),
    (ts.map toGate).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w.map (fun n => n.testBit k)) = (ts.foldl stepN w).map (fun n => n.testBit k)
  | [], _ => rfl
  | t :: ts, w => by
    simp only [List.map_cons, List.foldl_cons]
    rw [← fold_sim k ts (stepN w t)]
    congr 1
    obtain ⟨o, a, b⟩ := t
    cases o <;> simp [stepN, toGate, GateOp.eval, getD_map_testBit, opt_testBit, Nat.testBit_or, Nat.testBit_and]

theorem fold_length : ∀ (ts : List (Bool × ℕ × ℕ)) (w : List ℕ),
    (ts.foldl stepN w).length = w.length + ts.length
  | [], _ => by simp
  | t :: ts, w => by
    simp only [List.foldl_cons]
    rw [fold_length ts (stepN w t)]
    simp [stepN]
    omega

theorem getLastD_eq (l : List ℕ) (n : ℕ) (h : l.length = n + 1) :
    l.getLastD 0 = l.getD n 0 := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD, h]
  simp

end PEqualNP.Outside.L_meta_7756

open PEqualNP.Outside.L_meta_7756 in
theorem PEqualNP.Outside.L_meta_7756 : ∀ (x1 : List (Bool × ℕ × ℕ)), ∀ x2 ∈ x1.head?, x2 ∈ [(Bool.false, (0 : ℕ), (13 : ℕ)), (Bool.true, (0 : ℕ), (1 : ℕ)), (Bool.true, (0 : ℕ), (13 : ℕ)), (Bool.true, (2 : ℕ), (13 : ℕ))] → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size = x1.length ∧ (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x5.gates.head? = Option.some x6 ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x6.inputs = [(0 : ℕ), (13 : ℕ)] ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x6.inputs ∈ [[(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(2 : ℕ), (13 : ℕ)]])) ∧ ∀ (x6 : List ℕ) (x7 : ℕ), x6.length = (26 : ℕ) → x5.eval (List.map (fun (x9 : ℕ) => x9.testBit x7) x6) = ((List.foldl (fun (x9 : List ℕ) (x10 : Bool × ℕ × ℕ) => x9 ++ [if x10.1 = Bool.true then x9.getD x10.2.1 (0 : ℕ) ||| x9.getD x10.2.2 (0 : ℕ) else x9.getD x10.2.1 (0 : ℕ) &&& x9.getD x10.2.2 (0 : ℕ)]) x6 x1).getLastD (0 : ℕ)).testBit x7 := by
  intro x1 x2 hx2 hmem
  obtain ⟨t, ts, rfl⟩ : ∃ t ts, x1 = t :: ts := by
    cases x1 with
    | nil => simp at hx2
    | cons t ts => exact ⟨t, ts, rfl⟩
  have ht : t = x2 := by simpa using hx2
  rw [ht]
  refine ⟨⟨(x2 :: ts).map toGate, 26 + ts.length⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨u, -, rfl⟩ := hg
    refine ⟨?_, by simp [toGate]⟩
    simp only [toGate]
    split <;> simp
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · refine ⟨toGate x2, rfl, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl <;> simp [toGate]
  · intro x6 x7 hlen
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    rw [fold_sim x7 (x2 :: ts) x6, getD_map_testBit]
    congr 1
    symm
    apply getLastD_eq
    show (List.foldl stepN x6 (x2 :: ts)).length = _
    rw [fold_length, hlen]
    simp
    omega
