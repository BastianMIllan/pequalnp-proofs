import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3417

open PEqualNP.CircuitLowerBounds

-- the star with center 0 and leaves 1, 2
def gx : SimpleGraph (Fin 3) := PEqualNP.EdgeOwnership.edgeGraph 3 [(0, 1), (0, 2)]

instance : DecidableRel gx.Adj := fun a b =>
  inferInstanceAs (Decidable ((PEqualNP.EdgeOwnership.edgeGraph 3 [(0, 1), (0, 2)]).Adj a b))

-- L = x1 OR x2, A = x0 AND L, core g = A AND L, A2 = x0 AND L, output (g OR A2) OR A;
-- L and A are read by output gates outside the cone of the core
def cx : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 3] },
      { op := GateOp.and, inputs := [4, 3] }, { op := GateOp.and, inputs := [0, 3] },
      { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.or, inputs := [7, 4] }],
    output := 8 }

def sx : Fin 3 → Bool := fun i => decide (i = 0)

theorem hD : (PEqualNP.Core.maximalCores gx cx).biUnion (PEqualNP.TopForm.gammaE gx cx)
    = {s(0, 1), s(0, 2)} := by decide

theorem hcoverT : PEqualNP.MetaComplexity.NestedCover.IsMinCover gx {0} := by
  refine ⟨?_, ?_⟩
  · intro v w hvw
    simp only [Finset.coe_singleton, Set.mem_singleton_iff]
    revert v w
    decide
  · intro T hT
    by_contra hlt
    have hlt2 : T.card < 1 := by
      have := not_le.mp hlt
      rwa [Finset.card_singleton] at this
    have h0 : T = ∅ := Finset.card_eq_zero.mp (by omega)
    have hadj : gx.Adj 0 1 := by decide
    have := hT hadj
    simp [h0] at this

theorem hcover : PEqualNP.MetaComplexity.NestedCover.IsMinCover
    (gx.deleteEdges
      (((PEqualNP.Core.maximalCores gx cx).biUnion
        (PEqualNP.TopForm.gammaE gx cx) : Finset (Sym2 (Fin 3))) :
          Set (Sym2 (Fin 3)))) ∅ := by
  rw [hD]
  refine ⟨?_, fun T _ => by simp⟩
  intro v w hvw
  exfalso
  rw [SimpleGraph.deleteEdges_adj] at hvw
  obtain ⟨h1, h2⟩ := hvw
  apply h2
  revert v w
  decide

theorem hU0 : (((PEqualNP.Core.maximalCores gx cx).biUnion (PEqualNP.Core.coneSet 3 cx)).filter
    (fun w => w ∈ PEqualNP.Core.maximalCores gx cx ∨
      ((PEqualNP.TopForm.readers 3 cx w).filter (fun k => PEqualNP.Core.InOutputCone 3 cx k)) ⊆
        (PEqualNP.Core.maximalCores gx cx).biUnion (PEqualNP.Core.coneSet 3 cx))).card = 1 := by
  decide

theorem hmc : (PEqualNP.Core.maximalCores gx cx).card = 1 := by decide

end PEqualNP.Outside.L_meta_3417

open PEqualNP.Outside.L_meta_3417 in
theorem PEqualNP.Outside.L_meta_3417 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (PEqualNP.Core.maximalCores G C).card + T'.card) := by
  intro h
  have key := h 3 gx cx sx {0} ∅
    (by decide) (by decide) (by decide) (by funext x; revert x; decide) (by decide) hcoverT hcover
  rw [hD, hU0, hmc] at key
  revert key
  decide
