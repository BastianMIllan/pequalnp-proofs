import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2860

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem early (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hi' : i < (step w g).length := by simp [step]; omega
    rw [List.foldl_cons, ih (step w g) hi']
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem gate_val (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ j < gs.length, ∀ k ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, k < w.length + j) :
    (gs.foldl step w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map
        fun k => (gs.foldl step w).getD k false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      have hin : ∀ k ∈ g.inputs, k < w.length := by
        intro k hk
        have := hrb 0 (by simp) k (by simpa using hk)
        simpa using this
      rw [List.foldl_cons, Nat.add_zero, early gs (step w g) _ (by simp [step])]
      simp only [List.getD_cons_zero]
      have e1 : (step w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [step, List.getD_eq_getElem?_getD]
      rw [e1]
      congr 1
      apply List.map_congr_left
      intro k hk
      rw [early gs (step w g) k (by simp [step]; have := hin k hk; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left (hin k hk)]
    | succ j =>
      have hlen : (step w g).length = w.length + 1 := by simp [step]
      have key := ih (step w g) j (by simp at hj; omega) (by
        intro j' hj' k hk
        have := hrb (j' + 1) (by simp; omega) k (by simpa using hk)
        rw [hlen]; omega)
      rw [List.foldl_cons, show w.length + (j + 1) = (step w g).length + j by rw [hlen]; omega,
        key]
      simp

theorem wire_char (D : Circuit) (n : ℕ) (y : List Bool) (hy : y.length = n)
    (hrb : ReadsBack n D) (i : ℕ) :
    (D.wires y).getD i false =
      if i < n then y.getD i false
      else if i < n + D.gates.length then
        (gateAt D (i - n)).op.eval ((gateAt D (i - n)).inputs.map
          fun k => (D.wires y).getD k false)
      else false := by
  have hw : D.wires y = D.gates.foldl step y := rfl
  rw [hw]
  split_ifs with h1 h2
  · exact early _ _ _ (by omega)
  · have := gate_val D.gates y (i - n) (by omega) (by
      intro j hj k hk
      have := hrb j hj k hk
      omega)
    have e : y.length + (i - n) = i := by omega
    rw [e] at this
    rw [this]
    rfl
  · apply List.getD_eq_default
    rw [len_fold]; omega

theorem getD_set (l : List Gate) (i j : ℕ) (g d : Gate) (hi : i < l.length) :
    (l.set i g).getD j d = if i = j then g else l.getD j d := by
  by_cases h : i = j
  · subst h; simp [List.getD_eq_getElem?_getD, hi]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne h, h]

theorem core (n : ℕ) (C C' : Circuit) (m u v z a b : ℕ)
    (hC' : C' = ⟨(C.gates.set (v - n) ⟨GateOp.and, [a, b]⟩).set m ⟨GateOp.or, [z, v]⟩,
      C.output⟩)
    (hrb : ReadsBack n C) (hm : m < C.gates.length) (hnu : n ≤ u) (huv : u < v)
    (hvm : v < n + m)
    (hmop : (gateAt C m).op = GateOp.and) (hmin : (gateAt C m).inputs = [u, v])
    (huop : (gateAt C (u - n)).op = GateOp.or) (huin : (gateAt C (u - n)).inputs = [z, a])
    (hvop : (gateAt C (v - n)).op = GateOp.or) (hvin : (gateAt C (v - n)).inputs = [z, b])
    (hnot : ∀ j < C.gates.length, j ≠ m → v ∉ (gateAt C j).inputs)
    (hout : C.output ≠ v) :
    ReadsBack n C' ∧ C'.size = C.size ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hlen' : C'.gates.length = C.gates.length := by subst hC'; simp
  have hout' : C'.output = C.output := by subst hC'; rfl
  have hga : ∀ j, gateAt C' j = if m = j then ⟨GateOp.or, [z, v]⟩ else
      if v - n = j then ⟨GateOp.and, [a, b]⟩ else gateAt C j := by
    intro j
    subst hC'
    simp only [gateAt]
    rw [getD_set _ _ _ _ _ (by simp; omega), getD_set _ _ _ _ _ (by omega)]
  have hz : z < u := by
    have := hrb (u - n) (by omega) z (by rw [huin]; simp); omega
  have ha : a < u := by
    have := hrb (u - n) (by omega) a (by rw [huin]; simp); omega
  have hb : b < v := by
    have := hrb (v - n) (by omega) b (by rw [hvin]; simp); omega
  have hrb' : ReadsBack n C' := by
    intro j hj k hk
    rw [hlen'] at hj
    rw [hga] at hk
    split_ifs at hk with h3 h4
    · simp at hk; omega
    · simp at hk; omega
    · exact hrb j hj k hk
  refine ⟨hrb', by simp [Circuit.size, hlen'], ?_⟩
  intro x
  have hy : (List.ofFn x).length = n := by simp
  have claim : ∀ i, i ≠ v →
      (C'.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn x)).getD i false := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hiv
      rw [wire_char C' n _ hy hrb' i, wire_char C n _ hy hrb i, hlen']
      split_ifs with h1 h2
      · rfl
      · rw [hga]
        split_ifs with h3 h4
        · have hW'v : (C'.wires (List.ofFn x)).getD v false =
              ((C'.wires (List.ofFn x)).getD a false &&
                (C'.wires (List.ofFn x)).getD b false) := by
            rw [wire_char C' n _ hy hrb' v, if_neg (by omega), if_pos (by rw [hlen']; omega),
              hga, if_neg (by omega), if_pos rfl]
            simp [GateOp.eval]
          have hWu : (C.wires (List.ofFn x)).getD u false =
              ((C.wires (List.ofFn x)).getD z false ||
                (C.wires (List.ofFn x)).getD a false) := by
            rw [wire_char C n _ hy hrb u, if_neg (by omega), if_pos (by omega), huop, huin]
            simp [GateOp.eval]
          have hWv : (C.wires (List.ofFn x)).getD v false =
              ((C.wires (List.ofFn x)).getD z false ||
                (C.wires (List.ofFn x)).getD b false) := by
            rw [wire_char C n _ hy hrb v, if_neg (by omega), if_pos (by omega), hvop, hvin]
            simp [GateOp.eval]
          rw [← h3, hmop, hmin]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false]
          rw [hW'v, hWu, hWv, ih z (by omega) (by omega), ih a (by omega) (by omega),
            ih b (by omega) (by omega)]
          cases (C.wires (List.ofFn x)).getD z false <;>
            cases (C.wires (List.ofFn x)).getD a false <;>
            cases (C.wires (List.ofFn x)).getD b false <;> rfl
        · exfalso; omega
        · congr 1
          apply List.map_congr_left
          intro k hk
          have hk1 := hrb (i - n) (by omega) k hk
          have hk2 : k ≠ v := by
            intro hkv
            exact hnot (i - n) (by omega) (fun e => h3 e.symm) (hkv ▸ hk)
          exact ih k (by omega) hk2
      · rfl
  simp only [Circuit.eval, hout']
  exact claim _ hout

end PEqualNP.Outside.L_meta_2860

theorem PEqualNP.Outside.L_meta_2860 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m u v z a b : ℕ), PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → m < C.gates.length → n ≤ u → u < v → v < n + m → (PEqualNP.MetaComplexity.NestedCover.gateAt C m).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs = [u, v] → (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - n)).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - n)).inputs = [z, a] → (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - n)).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - n)).inputs = [z, b] → (∀ j < C.gates.length, j ≠ m → v ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs) → C.output ≠ v → PEqualNP.MetaComplexity.NestedCover.ReadsBack n (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ ∀ x : Fin n → Bool, (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro n C m u v z a b hrb hm hnu huv hvm hmop hmin huop huin hvop hvin hnot hout
  exact PEqualNP.Outside.L_meta_2860.core n C _ m u v z a b rfl hrb hm hnu huv hvm hmop hmin
    huop huin hvop hvin hnot hout
