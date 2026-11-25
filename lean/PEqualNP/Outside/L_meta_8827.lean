import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8827

open PEqualNP.CircuitLowerBounds

def relab (n : ℕ) (p : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  if h : i < n then ((p ⟨i, h⟩ : Fin n) : ℕ) else i

theorem relab_lt (n : ℕ) (p : Equiv.Perm (Fin n)) (i : ℕ) (h : i < n) : relab n p i < n := by
  unfold relab
  rw [dif_pos h]
  exact (p ⟨i, h⟩).isLt

theorem relab_ge (n : ℕ) (p : Equiv.Perm (Fin n)) (i : ℕ) (h : n ≤ i) : relab n p i = i := by
  unfold relab
  rw [dif_neg (by omega)]

def newGate (n : ℕ) (p : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (relab n p)⟩

theorem getD_append_one (w : List Bool) (b : Bool) (j : ℕ) :
    (w ++ [b]).getD j false = if j < w.length then w.getD j false else if j = w.length then b else false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_append_right (by omega)]
    have : j - w.length ≠ 0 := by omega
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem step (n : ℕ) (p : Equiv.Perm (Fin n)) (gs : List Gate) :
    ∀ (w5 w2 : List Bool), w5.length = w2.length → n ≤ w2.length →
      (∀ i, w5.getD (relab n p i) false = w2.getD i false) →
      (run (gs.map (newGate n p)) w5).length = (run gs w2).length ∧
      n ≤ (run gs w2).length ∧
      ∀ i, (run (gs.map (newGate n p)) w5).getD (relab n p i) false = (run gs w2).getD i false := by
  induction gs with
  | nil =>
    intro w5 w2 hl hn hq
    exact ⟨hl, hn, hq⟩
  | cons g gs ih =>
    intro w5 w2 hl hn hq
    rw [List.map_cons]
    refine ih (w5 ++ [(newGate n p g).op.eval ((newGate n p g).inputs.map fun i => w5.getD i false)])
      (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)]) ?_ ?_ ?_
    · simp [hl]
    · simp; omega
    · have hval : (newGate n p g).op.eval ((newGate n p g).inputs.map fun i => w5.getD i false)
          = g.op.eval (g.inputs.map fun i => w2.getD i false) := by
        simp only [newGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact hq i
      intro i
      rw [hval, getD_append_one, getD_append_one]
      by_cases hi : i < n
      · have h1 : relab n p i < w5.length := by have := relab_lt n p i hi; omega
        have h2 : i < w2.length := by omega
        rw [if_pos h1, if_pos h2]
        exact hq i
      · rw [relab_ge n p i (by omega), hl]
        have hqi := hq i
        rw [relab_ge n p i (by omega)] at hqi
        split_ifs <;> first | rfl | exact hqi

end PEqualNP.Outside.L_meta_8827

theorem PEqualNP.Outside.L_meta_8827 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : Equiv.Perm (Fin x1)), ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size = x2.size ∧ ∀ (x6 : ℕ) (x7 : Fin x1 → Bool), x1 ≤ x6 → (x5.wires (List.ofFn x7)).getD x6 Bool.false = (x2.wires (List.ofFn (x7 ∘ ⇑x4))).getD x6 Bool.false := by
  intro n C hC p
  refine ⟨⟨C.gates.map (PEqualNP.Outside.L_meta_8827.newGate n p), C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    obtain ⟨h1, h2⟩ := hC g0 hg0
    exact ⟨h1, by simpa [PEqualNP.Outside.L_meta_8827.newGate] using h2⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro i x hi
    have key0 := (PEqualNP.Outside.L_meta_8827.step n p C.gates (List.ofFn x) (List.ofFn (x ∘ ⇑p))
      (by simp) (by simp) (by
        intro j
        by_cases hj : j < n
        · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
          have h1 := PEqualNP.Outside.L_meta_8827.relab_lt n p j hj
          rw [List.getElem?_ofFn, List.getElem?_ofFn]
          simp only [List.ofFnNthVal, dif_pos h1, dif_pos hj, Option.getD_some]
          simp [PEqualNP.Outside.L_meta_8827.relab, hj]
        · rw [PEqualNP.Outside.L_meta_8827.relab_ge n p j (by omega)]
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)])).2.2 i
    rw [PEqualNP.Outside.L_meta_8827.relab_ge n p i hi] at key0
    exact key0
