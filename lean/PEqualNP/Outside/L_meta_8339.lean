import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8339

open PEqualNP.CircuitLowerBounds

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def clamp (j : ℕ) : Fin 40 := ⟨min j 39, by omega⟩

def conv (g : Gate) : Gate :=
  { op := if isAnd g.op = true then GateOp.and else GateOp.or,
    inputs := List.map Fin.val ((g.inputs[0]?.map clamp).toList ++ (g.inputs[1]?.map clamp).toList) }

theorem getD_clamp (w : List Bool) (j : ℕ) (hw : w.length ≤ 39) :
    w.getD (min j 39) false = w.getD j false := by
  by_cases h : j ≤ 39
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem inputs_conv (l : List ℕ) (hl : l.length ≤ 2) :
    List.map Fin.val ((l[0]?.map clamp).toList ++ (l[1]?.map clamp).toList) =
      l.map (fun j => min j 39) := by
  match l, hl with
  | [], _ => rfl
  | [a], _ => rfl
  | [a, b], _ => rfl
  | a :: b :: c :: t, h => simp at h

theorem eval_conv (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : List Bool) (hw : w.length ≤ 39) :
    (conv g).op.eval ((conv g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  have h2 : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hg.1
  have hop : (conv g).op = g.op := by
    rcases h2 with h | h <;> simp [conv, isAnd, h]
  rw [hop]
  congr 1
  simp only [conv]
  rw [inputs_conv _ hg.2, List.map_map]
  apply List.map_congr_left
  intro j _
  exact getD_clamp w j hw

theorem fold_conv : ∀ (gs : List Gate),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    ∀ w : List Bool, w.length + gs.length ≤ 39 →
      (gs.map conv).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w =
        gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  | [], _, w, _ => rfl
  | g :: gs, h, w, hl => by
    simp only [List.map_cons, List.foldl_cons]
    have hl' : w.length + 1 + gs.length ≤ 39 := by simp at hl; omega
    rw [eval_conv g (h g (by simp)) w (by omega)]
    apply fold_conv gs (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    simp; omega

end PEqualNP.Outside.L_meta_8339

theorem PEqualNP.Outside.L_meta_8339 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (25 : ℕ) →       ∃ (x4 : Fin (26 : ℕ)) (x5 : Fin ↑x4 → Bool) (x6 : Fin ↑x4 → Option (Fin (40 : ℕ)) × Option (Fin (40 : ℕ))),         have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.ofFn fun (x7 : Fin ↑x4) => { op := if x5 x7 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := List.map Fin.val ((x6 x7).1.toList ++ (x6 x7).2.toList) : PEqualNP.CircuitLowerBounds.Gate }, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit };         ∀ (x8 : Fin (14 : ℕ) → Bool), x7.wires (List.ofFn x8) = x1.wires (List.ofFn x8) := by
  intro x1 hM hs
  obtain ⟨gs, o⟩ := x1
  have hle : gs.length ≤ 25 := hs
  have hlen : gs.length < 26 := by omega
  refine ⟨⟨gs.length, hlen⟩,
    fun i => PEqualNP.Outside.L_meta_8339.isAnd (gs.get ⟨i.val, i.isLt⟩).op,
    fun i => ((gs.get ⟨i.val, i.isLt⟩).inputs[0]?.map PEqualNP.Outside.L_meta_8339.clamp,
      (gs.get ⟨i.val, i.isLt⟩).inputs[1]?.map PEqualNP.Outside.L_meta_8339.clamp), ?_⟩
  dsimp only
  intro x8
  unfold PEqualNP.CircuitLowerBounds.Circuit.wires
  rw [← PEqualNP.Outside.L_meta_8339.fold_conv gs hM (List.ofFn x8) (by simp; omega)]
  congr 1
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp [PEqualNP.Outside.L_meta_8339.conv]
