import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3306

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

-- swap the two operands of an AND gate unless they are already in the order (x4, x3)
def fixIn (x3 x4 : Finset ℕ) (op : GateOp) (l : List ℕ) : List ℕ :=
  match op, l with
  | GateOp.and, [p, q] => if p ∈ x4 ∧ q ∈ x3 then [p, q] else [q, p]
  | _, l => l

def fixG (x3 x4 : Finset ℕ) (g : Gate) : Gate := ⟨g.op, fixIn x3 x4 g.op g.inputs⟩

def fixC (x3 x4 : Finset ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (fixG x3 x4), C.output⟩

theorem fixIn_perm (x3 x4 : Finset ℕ) (op : GateOp) (l : List ℕ) :
    (fixIn x3 x4 op l).Perm l := by
  unfold fixIn
  split
  · split_ifs
    · exact List.Perm.refl _
    · exact List.Perm.swap _ _ _
  · exact List.Perm.refl _

theorem fixIn_eval (x3 x4 : Finset ℕ) (op : GateOp) (l : List ℕ) (f : ℕ → Bool) :
    op.eval ((fixIn x3 x4 op l).map f) = op.eval (l.map f) := by
  unfold fixIn
  split
  · split_ifs
    · rfl
    · simp [GateOp.eval, Bool.and_comm]
  · rfl

theorem fixIn_or (x3 x4 : Finset ℕ) (l : List ℕ) : fixIn x3 x4 GateOp.or l = l := by
  unfold fixIn
  split
  · rename_i h
    cases h
  · rfl

theorem foldl_fix (x3 x4 : Finset ℕ) (gs : List Gate) (w : List Bool) :
    (gs.map (fixG x3 x4)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    congr 2
    simp only [fixG]
    rw [fixIn_eval]

theorem gateAt_fix (x3 x4 : Finset ℕ) (C : Circuit) (j : ℕ) :
    gateAt (fixC x3 x4 C) j = fixG x3 x4 (gateAt C j) := by
  unfold gateAt fixC
  simp only
  have hd : (⟨GateOp.or, []⟩ : Gate) = fixG x3 x4 ⟨GateOp.or, []⟩ := by
    simp [fixG, fixIn_or]
  rw [hd, List.getD_map]
  rw [← hd]

theorem main (n : ℕ) (C : Circuit) (x3 x4 : Finset ℕ) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hand : ∀ x6 < C.gates.length, (gateAt C x6).op = GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ),
      (gateAt C x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) :
    ∃ (x7 : Circuit), PEqualNP.TopForm.IsAO2 n x7 ∧ x7.size = C.size ∧
      PEqualNP.MetaComplexity.circuitFun n x7 = PEqualNP.MetaComplexity.circuitFun n C ∧
      (∀ (x8 : ℕ), (gateAt x7 x8).op = (gateAt C x8).op) ∧
      (∀ (x8 : ℕ), (gateAt C x8).op = GateOp.or → gateAt x7 x8 = gateAt C x8) ∧
      ∀ x8 < x7.gates.length, (gateAt x7 x8).op = GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ),
        (gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x4 ∧ x12 ∈ x3 := by
  obtain ⟨hAO, hRB, hlen⟩ := hC
  refine ⟨fixC x3 x4 C, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [fixC, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact hAO g0 hg0
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa [fixC] using hj
    rw [gateAt_fix] at hi
    have hi' : i ∈ (gateAt C j).inputs := (fixIn_perm x3 x4 _ _).subset hi
    exact hRB j hj' i hi'
  · intro g hg
    simp only [fixC, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    simp only [fixG]
    rw [(fixIn_perm x3 x4 _ _).length_eq]
    exact hlen g0 hg0
  · simp [fixC, Circuit.size]
  · funext x
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, Circuit.wires]
    simp only [fixC]
    rw [foldl_fix]
  · intro j
    rw [gateAt_fix]
    rfl
  · intro j hj
    rw [gateAt_fix]
    simp only [fixG, hj, fixIn_or]
    rw [← hj]
  · intro j hj hop
    have hj' : j < C.gates.length := by simpa [fixC] using hj
    rw [gateAt_fix] at hop ⊢
    have hop' : (gateAt C j).op = GateOp.and := hop
    obtain ⟨p, q, hin, hmem⟩ := hand j hj' hop'
    simp only [fixG, hop', hin, fixIn]
    by_cases h : p ∈ x4 ∧ q ∈ x3
    · rw [if_pos h]
      exact ⟨p, q, rfl, h.1, h.2⟩
    · rw [if_neg h]
      rcases hmem with h1 | h1
      · exact ⟨q, p, rfl, h1.2, h1.1⟩
      · exact absurd h1 h

end PEqualNP.Outside.L_meta_3306

theorem PEqualNP.Outside.L_meta_3306 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x4 ∧ x12 ∈ x3 := by
  intro x1 x2 x3 x4 hC hand
  exact PEqualNP.Outside.L_meta_3306.main x1 x2 x3 x4 hC hand
