import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8604

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Agree (k : ℕ) (W W' : List Bool) : Prop :=
  W.length = W'.length ∧ ∀ i, i ≠ k → W.getD i false = W'.getD i false

theorem len_fold (gs : List Gate) : ∀ w : List Bool, (gs.foldl stp w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons]
    rw [ih]
    simp [stp]
    omega

theorem pre_fold (gs : List Gate) : ∀ w : List Bool, ∃ T, gs.foldl stp w = w ++ T := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons]
    obtain ⟨T, hT⟩ := ih (stp w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ T, ?_⟩
    rw [hT]
    unfold stp
    simp

theorem getD_pre (L T : List Bool) (i : ℕ) (h : i < L.length) :
    (L ++ T).getD i false = L.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc (L : List Bool) (a : Bool) (i : ℕ) :
    (L ++ [a]).getD i false = if i < L.length then L.getD i false else if i = L.length then a else false := by
  split_ifs with h1 h2
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · subst h2; simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default]; simp; omega

theorem agree_snoc {k : ℕ} {W W' : List Bool} (a : Bool) (h : Agree k W W') :
    Agree k (W ++ [a]) (W' ++ [a]) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  rw [getD_snoc, getD_snoc, h.1, h.2 i hi]

theorem agree_last (W : List Bool) (a b : Bool) : Agree W.length (W ++ [a]) (W ++ [b]) := by
  refine ⟨by simp, fun i hi => ?_⟩
  rw [getD_snoc, getD_snoc]
  simp [hi]

theorem and_eval_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem agree_stp {k : ℕ} {V V' : List Bool} {g g' : Gate} (h : Agree k V V')
    (hv : g.op.eval (g.inputs.map fun i => V.getD i false) =
      g'.op.eval (g'.inputs.map fun i => V'.getD i false)) : Agree k (stp V g) (stp V' g') := by
  unfold stp
  rw [hv]
  exact agree_snoc _ h

theorem agree_fold (k : ℕ) : ∀ (gs : List Gate) (W W' : List Bool), Agree k W W' →
    (∀ g ∈ gs, k ∉ g.inputs) → Agree k (gs.foldl stp W) (gs.foldl stp W')
  | [], W, W', h, _ => h
  | g :: gs, W, W', h, hg => by
    simp only [List.foldl_cons]
    apply agree_fold k gs _ _ _ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    have heq : (g.inputs.map fun i => W.getD i false) = (g.inputs.map fun i => W'.getD i false) := by
      apply List.map_congr_left
      intro i hi
      apply h.2 i
      intro e
      subst e
      exact hg g (by simp) hi
    unfold stp
    rw [heq]
    exact agree_snoc _ h

theorem main (n : ℕ) (g2 g3 g4 : List Gate) (a5 a6 : List ℕ) (k7 o : ℕ)
    (hp : a6.Perm [n + g2.length, k7]) (h7 : k7 < n + g2.length)
    (h5 : ∀ i ∈ a5, i < n + g2.length) (ho : o ≠ n + g2.length)
    (h34 : ∀ g ∈ g3 ++ g4, n + g2.length ∉ g.inputs) (x : Fin n → Bool) :
    Circuit.eval ⟨g2 ++ (⟨GateOp.and, a5.take 1 ++ [k7]⟩ : Gate) ::
        (g3 ++ (⟨GateOp.and, (n + g2.length) :: a5.drop 1⟩ : Gate) :: g4), o⟩ (List.ofFn x) =
      Circuit.eval ⟨g2 ++ (⟨GateOp.and, a5⟩ : Gate) :: (g3 ++ (⟨GateOp.and, a6⟩ : Gate) :: g4), o⟩
        (List.ofFn x) := by
  show ((g2 ++ (⟨GateOp.and, a5.take 1 ++ [k7]⟩ : Gate) ::
        (g3 ++ (⟨GateOp.and, (n + g2.length) :: a5.drop 1⟩ : Gate) :: g4)).foldl stp
          (List.ofFn x)).getD o false =
      ((g2 ++ (⟨GateOp.and, a5⟩ : Gate) :: (g3 ++ (⟨GateOp.and, a6⟩ : Gate) :: g4)).foldl stp
          (List.ofFn x)).getD o false
  simp only [List.foldl_append, List.foldl_cons]
  generalize hk : n + g2.length = k at *
  generalize hW0 : g2.foldl stp (List.ofFn x) = W0
  have hlen : W0.length = k := by rw [← hW0, len_fold, List.length_ofFn, hk]
  have h3 : ∀ g ∈ g3, k ∉ g.inputs := fun g hg => h34 g (List.mem_append_left _ hg)
  have h4 : ∀ g ∈ g4, k ∉ g.inputs := fun g hg => h34 g (List.mem_append_right _ hg)
  have hU : Agree k (stp W0 ⟨GateOp.and, a5.take 1 ++ [k7]⟩) (stp W0 ⟨GateOp.and, a5⟩) := by
    unfold stp
    rw [← hlen]
    exact agree_last _ _ _
  have hV := agree_fold k g3 _ _ hU h3
  obtain ⟨T, hT⟩ := pre_fold g3 (stp W0 ⟨GateOp.and, a5.take 1 ++ [k7]⟩)
  obtain ⟨T', hT'⟩ := pre_fold g3 (stp W0 ⟨GateOp.and, a5⟩)
  have e1 : ∀ i, i < k → (stp W0 ⟨GateOp.and, a5.take 1 ++ [k7]⟩ ++ T).getD i false = W0.getD i false := by
    intro i hi
    unfold stp
    rw [List.append_assoc, getD_pre _ _ _ (by omega)]
  have e2 : ∀ i, i < k → (stp W0 ⟨GateOp.and, a5⟩ ++ T').getD i false = W0.getD i false := by
    intro i hi
    unfold stp
    rw [List.append_assoc, getD_pre _ _ _ (by omega)]
  have e1k : (stp W0 ⟨GateOp.and, a5.take 1 ++ [k7]⟩ ++ T).getD k false =
      GateOp.and.eval ((a5.take 1 ++ [k7]).map fun i => W0.getD i false) := by
    unfold stp
    rw [getD_pre _ _ _ (by simp; omega), getD_snoc, if_neg (by omega), if_pos hlen.symm]
  have e2k : (stp W0 ⟨GateOp.and, a5⟩ ++ T').getD k false =
      GateOp.and.eval (a5.map fun i => W0.getD i false) := by
    unfold stp
    rw [getD_pre _ _ _ (by simp; omega), getD_snoc, if_neg (by omega), if_pos hlen.symm]
  have hB : GateOp.and.eval ((k :: a5.drop 1).map fun i =>
        (g3.foldl stp (stp W0 ⟨GateOp.and, a5.take 1 ++ [k7]⟩)).getD i false) =
      GateOp.and.eval (a6.map fun i => (g3.foldl stp (stp W0 ⟨GateOp.and, a5⟩)).getD i false) := by
    rw [hT, hT']
    have hd : ∀ i ∈ a5.drop 1, i < k := fun i hi => h5 i (List.mem_of_mem_drop hi)
    have ht : ∀ i ∈ a5.take 1, i < k := fun i hi => h5 i (List.mem_of_mem_take hi)
    have hsplit : ∀ i, i ∈ a5 ↔ i ∈ a5.take 1 ∨ i ∈ a5.drop 1 := by
      intro i
      conv_lhs => rw [← List.take_append_drop 1 a5]
      exact List.mem_append
    apply Bool.eq_iff_iff.mpr
    rw [and_eval_iff, and_eval_iff]
    have hK1 : (stp W0 ⟨GateOp.and, a5.take 1 ++ [k7]⟩ ++ T).getD k false = true ↔
        ∀ i ∈ a5.take 1 ++ [k7], W0.getD i false = true := by rw [e1k, and_eval_iff]
    have hK2 : (stp W0 ⟨GateOp.and, a5⟩ ++ T').getD k false = true ↔
        ∀ i ∈ a5, W0.getD i false = true := by rw [e2k, and_eval_iff]
    constructor
    · intro hall i hi
      rw [hp.mem_iff] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h | h
      · rw [h, hK2]
        intro j hj
        have hA := hK1.1 (hall k (by simp))
        rcases (hsplit j).1 hj with hj' | hj'
        · exact hA j (List.mem_append_left _ hj')
        · rw [← e1 j (hd j hj')]
          exact hall j (List.mem_cons_of_mem _ hj')
      · rw [h, e2 _ h7]
        exact hK1.1 (hall k (by simp)) k7 (by simp)
    · intro hall i hi
      have hK := hK2.1 (hall k (hp.mem_iff.2 (by simp)))
      have h7' := hall k7 (hp.mem_iff.2 (by simp))
      rw [e2 _ h7] at h7'
      rcases List.mem_cons.1 hi with h | h
      · rw [h, hK1]
        intro j hj
        rcases List.mem_append.1 hj with hj' | hj'
        · exact hK j ((hsplit j).2 (Or.inl hj'))
        · rw [List.mem_singleton.1 hj']
          exact h7'
      · rw [e1 i (hd i h)]
        exact hK i ((hsplit i).2 (Or.inr h))
  have hX := agree_stp (g := ⟨GateOp.and, k :: a5.drop 1⟩) (g' := ⟨GateOp.and, a6⟩) hV hB
  have hY := agree_fold k g4 _ _ hX h4
  exact hY.2 o ho

end PEqualNP.Outside.L_meta_8604

theorem PEqualNP.Outside.L_meta_8604 : ∀ (x1 : ℕ) (x2 x3 x4 : List PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : List ℕ) (x7 x8 : ℕ),   have x9 : ℕ := x1 + x2.length;   have x10 : List ℕ → List ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun (x10 x11 : List ℕ) => { gates := x2 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := x10 : PEqualNP.CircuitLowerBounds.Gate } :: (x3 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := x11 : PEqualNP.CircuitLowerBounds.Gate } :: x4), output := x8 : PEqualNP.CircuitLowerBounds.Circuit };   x6.Perm [x9, x7] → x7 < x9 → (∀ x13 ∈ x5, x13 < x9) → x8 ≠ x9 → (∀ x15 ∈ x3 ++ x4, x9 ∉ x15.inputs) → PEqualNP.MetaComplexity.circuitFun x1 (x10 (List.take (1 : ℕ) x5 ++ [x7]) (x9 :: List.drop (1 : ℕ) x5)) = PEqualNP.MetaComplexity.circuitFun x1 (x10 x5 x6) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 hp h7 h5 h8 h34
  funext x
  exact PEqualNP.Outside.L_meta_8604.main x1 x2 x3 x4 x5 x6 x7 x8 hp h7 h5 h8 h34 x
