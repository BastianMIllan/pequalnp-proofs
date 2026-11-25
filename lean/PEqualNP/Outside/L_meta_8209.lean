import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_8209

def slots : List Nat := [2, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

lemma slots_lt : ∀ x ∈ slots, x < 21 := by decide

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def front : List Gate := [
  ⟨GateOp.or, [9, 10]⟩,
  ⟨GateOp.or, [14, 20]⟩,
  ⟨GateOp.or, [21, 22]⟩,
  ⟨GateOp.and, [0, 23]⟩,
  ⟨GateOp.or, [9, 11]⟩,
  ⟨GateOp.or, [12, 16]⟩,
  ⟨GateOp.or, [25, 26]⟩,
  ⟨GateOp.and, [1, 27]⟩,
  ⟨GateOp.or, [9, 15]⟩,
  ⟨GateOp.or, [17, 18]⟩,
  ⟨GateOp.or, [29, 30]⟩,
  ⟨GateOp.and, [6, 31]⟩,
  ⟨GateOp.or, [24, 28]⟩,
  ⟨GateOp.or, [33, 32]⟩]

def rename (i : Nat) : Nat :=
  if h : i < slots.length then slots[i] else 35 + (i - slots.length)

def renamed (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩

def sel (v : List Bool) : List Bool := slots.map (fun j => v.getD j false)

lemma runLen (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons a gs ih => simp [ih, step]; omega

lemma readLeft (xs ys : List Bool) {i : Nat} (h : i < xs.length) :
    (xs ++ ys).getD i false = xs.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma readRight (xs ys : List Bool) (i : Nat) :
    (xs ++ ys).getD (xs.length + i) false = ys.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right xs.length i)]

lemma read (v pre tail : List Bool) (hp : pre.length = 35)
    (hf : ∀ j, j < 21 → pre.getD j false = v.getD j false) (i : Nat) :
    (pre ++ tail).getD (rename i) false = (sel v ++ tail).getD i false := by
  unfold rename
  split
  next h =>
    have hs : slots[i]'h < 21 := slots_lt _ (List.getElem_mem h)
    have hl : i < (sel v).length := by simpa [sel] using h
    rw [readLeft pre tail (i := slots[i]'h) (by omega), hf _ hs,
      readLeft (sel v) tail (i := i) hl]
    simp [sel, List.getD_eq_getElem?_getD, h]
  next h =>
    have hi : i = (sel v).length + (i - slots.length) := by simp [sel]; omega
    rw [← hp, readRight]
    exact ((readRight (sel v) tail (i - slots.length)).symm.trans
      (congrArg (fun k => (sel v ++ tail).getD k false) hi.symm))

lemma run (v pre : List Bool) (hp : pre.length = 35)
    (hf : ∀ j, j < 21 → pre.getD j false = v.getD j false)
    (gs : List Gate) (t : List Bool) :
    ∃ u : List Bool, (gs.map renamed).foldl step (pre ++ t) = pre ++ u ∧
      gs.foldl step (sel v ++ t) = sel v ++ u := by
  induction gs generalizing t with
  | nil => exact ⟨t, rfl, rfl⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => (sel v ++ t).getD i false)
    have hv : (g.inputs.map rename).map (fun i => (pre ++ t).getD i false) =
        g.inputs.map (fun i => (sel v ++ t).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact read v pre t hp hf i
    simpa only [List.map_cons, List.foldl_cons, step, renamed, hv, List.append_assoc, b]
      using ih (t ++ [b])

def combo (C : Circuit) : Circuit :=
  ⟨front ++ C.gates.map renamed ++ [⟨GateOp.or, [rename C.output, 34]⟩],
   35 + C.size⟩

lemma keep (gs : List Gate) (w : List Bool) {i : Nat} (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact readLeft _ _ hi

lemma endOR (w : List Bool) (a b : Nat) :
    (step w ⟨GateOp.or, [a,b]⟩).getD w.length false =
      (w.getD a false || w.getD b false) := by
  simp [step, GateOp.eval]

lemma comboEval (C : Circuit) (v : List Bool) (hvl : v.length = 21) :
    (combo C).eval v = (C.eval (sel v) || (front.foldl step v).getD 34 false) := by
  let pre := front.foldl step v
  have hp : pre.length = 35 := by
    change (front.foldl step v).length = 35
    rw [runLen, hvl]
    rfl
  have hf (j : Nat) (hj : j < 21) : pre.getD j false = v.getD j false := by
    change (front.foldl step v).getD j false = v.getD j false
    exact keep _ _ (by omega)
  obtain ⟨u, hu, hv⟩ := run v pre hp hf C.gates []
  simp only [List.append_nil] at hu hv
  have hlen : (pre ++ u).length = 35 + C.size := by
    rw [← hu, runLen, List.length_map, hp]; rfl
  have hr : (pre ++ u).getD (rename C.output) false = C.eval (sel v) := by
    rw [read v pre u hp hf, ← hv]; rfl
  change ((front ++ C.gates.map renamed ++ [(⟨GateOp.or, [rename C.output, 34]⟩ : Gate)]).foldl step v).getD
    (35 + C.size) false = _
  rw [List.foldl_append, List.foldl_append]
  change (step ((C.gates.map renamed).foldl step pre) ⟨GateOp.or, [rename C.output, 34]⟩).getD (35 + C.size) false = _
  rw [hu, ← hlen]
  rw [endOR, hr, readLeft pre u (i := 34) (by omega)]

lemma filt4 : List.filter (fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ), (13 : ℕ)])) (List.finRange (26 : ℕ)) =
    [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] := by decide

lemma filt1 : List.filter (fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 ∉ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (9 : ℕ), (10 : ℕ), (13 : ℕ), (14 : ℕ)])) (List.finRange (26 : ℕ)) =
    [5, 6, 7, 8, 11, 12, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] := by decide

lemma selEq (x5 : Fin 26 → Bool) :
    sel (List.map x5 [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]) =
      List.map x5 [5, 6, 7, 8, 11, 12, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] := rfl

lemma frontEq (x5 : Fin 26 → Bool) :
    (front.foldl step (List.map x5 [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25])).getD 34 false =
      (x5 2 && (x5 14 || x5 15 || (x5 19 || x5 25)) || x5 4 && (x5 14 || x5 16 || (x5 17 || x5 21)) || x5 10 && (x5 14 || x5 20 || (x5 22 || x5 23))) := by
  simp [front, step, GateOp.eval]

end PEqualNP.Outside.L_meta_8209

open PEqualNP.Outside.L_meta_8209

theorem PEqualNP.Outside.L_meta_8209 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.output < (17 : ℕ) + x1.size → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.output < (21 : ℕ) + x4.size ∧ x4.size ≤ x1.size + (15 : ℕ) ∧ ∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (List.map x5 (List.filter (fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ), (13 : ℕ)])) (List.finRange (26 : ℕ)))) = (x1.eval (List.map x5 (List.filter (fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 ∉ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (9 : ℕ), (10 : ℕ), (13 : ℕ), (14 : ℕ)])) (List.finRange (26 : ℕ)))) || (x5 (2 : Fin (26 : ℕ)) && (x5 (14 : Fin (26 : ℕ)) || x5 (15 : Fin (26 : ℕ)) || (x5 (19 : Fin (26 : ℕ)) || x5 (25 : Fin (26 : ℕ)))) || x5 (4 : Fin (26 : ℕ)) && (x5 (14 : Fin (26 : ℕ)) || x5 (16 : Fin (26 : ℕ)) || (x5 (17 : Fin (26 : ℕ)) || x5 (21 : Fin (26 : ℕ)))) || x5 (10 : Fin (26 : ℕ)) && (x5 (14 : Fin (26 : ℕ)) || x5 (20 : Fin (26 : ℕ)) || (x5 (22 : Fin (26 : ℕ)) || x5 (23 : Fin (26 : ℕ)))))) := by
  intro C hm _
  refine ⟨combo C, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [combo, List.mem_append, List.mem_singleton, List.mem_map] at hg
    rcases hg with (hg | ⟨g, h, rfl⟩) | rfl
    · have good : ∀ g ∈ front, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
          g.inputs.length ≤ 2 := by
        intro a ha
        simp only [front, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      exact good g hg
    · simpa [renamed] using hm g h
    · simp
  · simp [combo, Circuit.size, front]; omega
  · simp [combo, Circuit.size, front]
  · intro x5
    rw [filt4, filt1, comboEval C _ (by simp), selEq, frontEq]
