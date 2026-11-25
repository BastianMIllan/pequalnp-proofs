import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7171

open PEqualNP.CircuitLowerBounds

def fd {α : Type} (st : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [st w g]) w

theorem fd_snoc {α : Type} (st : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    fd st (gs ++ [g]) w = fd st gs w ++ [st (fd st gs w) g] := by
  simp [fd, List.foldl_append]

theorem fd_len {α : Type} (st : List α → Gate → α) (gs : List Gate) :
    ∀ w : List α, (fd st gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [fd]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [st w g])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem fd_keep {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (w : List α) (i : ℕ), i < w.length → (fd st gs w).getD i d = w.getD i d := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [st w g]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem fd_take {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k i : ℕ) (hi : i < X.length + k) (hk : k ≤ gs.length) :
    (fd st gs X).getD i d = (fd st (gs.take k) X).getD i d := by
  have h1 : fd st gs X = fd st (gs.drop k) (fd st (gs.take k) X) := by
    unfold fd
    rw [← List.foldl_append, List.take_append_drop]
  rw [h1]
  exact fd_keep st d _ _ i (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; exact hi)

def stB (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem agree_snoc (a b : List Bool) (v : Bool) (hl : a.length = b.length)
    (h : ∀ i, i ≠ 4 → a.getD i false = b.getD i false) :
    ∀ i, i ≠ 4 → (a ++ [v]).getD i false = (b ++ [v]).getD i false := by
  intro i hi
  by_cases hia : i < a.length
  · have hib : i < b.length := hl ▸ hia
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hia,
      List.getElem?_append_left hib]
    have := h i hi
    simpa only [List.getD_eq_getElem?_getD] using this
  · have hia' : a.length ≤ i := by omega
    have hib' : b.length ≤ i := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hia',
      List.getElem?_append_right hib', hl]

theorem main (C : Circuit) (x y : Fin 9 → Bool) (ho : C.output ≠ 4)
    (hxy : ∀ i : Fin 9, i ≠ 4 → x i = y i)
    (hg : ∀ (m : ℕ) (hm : m < C.gates.length), 4 ∈ (C.gates.get ⟨m, hm⟩).inputs →
      (C.gates.get ⟨m, hm⟩).op = GateOp.or ∧ ∃ j ∈ (C.gates.get ⟨m, hm⟩).inputs, j ≠ 4 ∧
        j < 9 + m ∧ (C.wires (List.ofFn x)).getD j false = true) :
    C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
  simp only [List.get_eq_getElem] at hg
  have inv : ∀ m, m ≤ C.gates.length → ∀ i, i ≠ 4 →
      (fd stB (C.gates.take m) (List.ofFn x)).getD i false =
      (fd stB (C.gates.take m) (List.ofFn y)).getD i false := by
    intro m
    induction m with
    | zero =>
      intro _ i hi
      simp only [List.take_zero, fd, List.foldl_nil]
      by_cases h9 : i < 9
      · have hne : (⟨i, h9⟩ : Fin 9) ≠ 4 := by
          intro h
          apply hi
          have := congrArg Fin.val h
          simpa using this
        have hx := hxy ⟨i, h9⟩ hne
        have hlx : i < (List.ofFn x).length := by simpa using h9
        have hly : i < (List.ofFn y).length := by simpa using h9
        rw [List.getD_eq_getElem _ _ hlx, List.getD_eq_getElem _ _ hly, List.getElem_ofFn,
          List.getElem_ofFn]
        exact hx
      · have h9' : 9 ≤ i := by omega
        rw [List.getD_eq_default _ _ (by simpa using h9'),
          List.getD_eq_default _ _ (by simpa using h9')]
    | succ m ih =>
      intro hm i hi
      have hm' : m < C.gates.length := hm
      have ih' := ih (Nat.le_of_lt hm')
      rw [List.take_succ_eq_append_getElem hm', fd_snoc, fd_snoc]
      have hlx : (fd stB (C.gates.take m) (List.ofFn x)).length = 9 + m := by
        rw [fd_len, List.length_take, List.length_ofFn, Nat.min_eq_left (Nat.le_of_lt hm')]
      have hly : (fd stB (C.gates.take m) (List.ofFn y)).length = 9 + m := by
        rw [fd_len, List.length_take, List.length_ofFn, Nat.min_eq_left (Nat.le_of_lt hm')]
      have hv : stB (fd stB (C.gates.take m) (List.ofFn x)) C.gates[m] =
          stB (fd stB (C.gates.take m) (List.ofFn y)) C.gates[m] := by
        by_cases h4 : 4 ∈ C.gates[m].inputs
        · obtain ⟨hor, j, hj, hj4, hjlt, hjv⟩ := hg m hm' h4
          have hwx : (fd stB (C.gates.take m) (List.ofFn x)).getD j false = true := by
            rw [← fd_take stB false C.gates (List.ofFn x) m j (by simpa using hjlt)
              (Nat.le_of_lt hm')]
            exact hjv
          have hwy : (fd stB (C.gates.take m) (List.ofFn y)).getD j false = true := by
            rw [← ih' j hj4]
            exact hwx
          have key : ∀ w : List Bool, w.getD j false = true → stB w C.gates[m] = true := by
            intro w hw
            simp only [stB, hor, GateOp.eval, List.any_map, List.any_eq_true]
            exact ⟨j, hj, by simpa using hw⟩
          rw [key _ hwx, key _ hwy]
        · simp only [stB]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact ih' a (fun h => h4 (h ▸ ha))
      rw [hv]
      exact agree_snoc _ _ _ (hlx.trans hly.symm) ih' i hi
  have hfin := inv C.gates.length le_rfl C.output ho
  rw [List.take_length] at hfin
  exact hfin

end PEqualNP.Outside.L_meta_7171

theorem PEqualNP.Outside.L_meta_7171 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (9 : ℕ) → Bool),   x1.output ≠ (4 : ℕ) →     (∀ (x5 : Fin (9 : ℕ)), x5 ≠ (4 : Fin (9 : ℕ)) → x2 x5 = x3 x5) →       (∀ (x6 : Fin x1.size),           have x7 : PEqualNP.CircuitLowerBounds.Gate := x1.gates.get x6;           (4 : ℕ) ∈ x7.inputs → x7.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ x9 ∈ x7.inputs, x9 ≠ (4 : ℕ) ∧ x9 < (9 : ℕ) + ↑x6 ∧ (x1.wires (List.ofFn x2)).getD x9 Bool.false = Bool.true) →         PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x2 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x3 := by
  intro x1 x2 x3 h1 h2 h3
  exact PEqualNP.Outside.L_meta_7171.main x1 x2 x3 h1 h2 (fun m hm h4 => h3 ⟨m, hm⟩ h4)
