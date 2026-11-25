import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7585

open PEqualNP.CircuitLowerBounds

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (k : ℕ) :
    (List.ofFn f).getD k false = if h : k < n then f ⟨k, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : k < n <;> simp [h]

theorem getD_append_singleton {α : Type*} (l : List α) (a d : α) (w : ℕ) :
    (l ++ [a]).getD w d = if w < l.length then l.getD w d else if w = l.length then a else d := by
  by_cases h1 : w < l.length
  · simp only [h1, ↓reduceIte]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left h1,
      ← List.getD_eq_getElem _ _ h1]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : w = l.length
    · subst h2
      simp only [↓reduceIte]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
      simp
    · simp only [h2, ↓reduceIte]
      rw [List.getD_eq_default _ _ (by simp; omega)]

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_prefix (gs : List Gate) (w : List Bool) :
    ∃ rest, gs.foldl F w = w ++ rest := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨r, hr⟩ := ih (F w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ r, ?_⟩
    rw [List.foldl_cons, hr]
    simp [F]

theorem fold_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl F w).getD i false = w.getD i false := by
  obtain ⟨r, hr⟩ := fold_prefix gs w
  rw [hr, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hi,
    ← List.getD_eq_getElem _ _ hi]

theorem gate_agree (g : Gate) (v : ℕ) (Sv : ℕ → Prop)
    (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hbad : v ∈ List.take (bif g.op.eval [false] then 1 else 2) g.inputs →
      g.op = GateOp.or ∧ ∃ s, Sv s ∧ s ∈ g.inputs)
    (w w' : List Bool)
    (hS : ∀ s, Sv s → w.getD s false = true ∧ w'.getD s false = true)
    (hag : ∀ i, i ≠ v → w.getD i false = w'.getD i false) :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hfan
  simp only at hop hlen hbad ⊢
  by_cases hv : v ∈ List.take (bif op.eval [false] then 1 else 2) ins
  · obtain ⟨rfl, s, hs, hsin⟩ := hbad hv
    have h1 := (hS s hs).1
    have h2 := (hS s hs).2
    simp only [GateOp.eval]
    rw [List.any_eq_true.mpr ⟨w.getD s false, List.mem_map.mpr ⟨s, hsin, rfl⟩, by simpa using h1⟩,
      List.any_eq_true.mpr ⟨w'.getD s false, List.mem_map.mpr ⟨s, hsin, rfl⟩, by simpa using h2⟩]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · have hk : (bif GateOp.and.eval [false] then 1 else 2) = 2 := by decide
      rw [hk, List.take_of_length_le hlen] at hv
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hag i (fun h => hv (h ▸ hi))
    · have hk : (bif GateOp.or.eval [false] then 1 else 2) = 2 := by decide
      rw [hk, List.take_of_length_le hlen] at hv
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hag i (fun h => hv (h ▸ hi))
    · have hk : (bif GateOp.not.eval [false] then 1 else 2) = 1 := by decide
      rw [hk] at hv
      cases ins with
      | nil => simp [GateOp.eval]
      | cons j t =>
        have hj : j ≠ v := fun h => hv (by simp [h])
        simp only [GateOp.eval, List.map_cons, List.headD_cons, hag j hj]

theorem wires_agree (gs : List Gate) (v : ℕ) (Sv : ℕ → Prop)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hbad : ∀ g ∈ gs, v ∈ List.take (bif g.op.eval [false] then 1 else 2) g.inputs →
      g.op = GateOp.or ∧ ∃ s, Sv s ∧ s ∈ g.inputs)
    (w w' : List Bool) (hlen : w.length = w'.length)
    (hS : ∀ s, Sv s → w.getD s false = true ∧ w'.getD s false = true)
    (hag : ∀ i, i ≠ v → w.getD i false = w'.getD i false) :
    ∀ i, i ≠ v → (gs.foldl F w).getD i false = (gs.foldl F w').getD i false := by
  induction gs generalizing w w' with
  | nil => simpa using hag
  | cons g gs ih =>
    have hga := gate_agree g v Sv (hfan g (by simp)) (hbad g (by simp)) w w' hS hag
    simp only [List.foldl_cons]
    apply ih (fun g' h => hfan g' (by simp [h])) (fun g' h => hbad g' (by simp [h]))
    · simp [F, hlen]
    · intro s hs
      have h1 := (hS s hs).1
      have h2 := (hS s hs).2
      have hs1 : s < w.length := by
        by_contra hc
        rw [List.getD_eq_default _ _ (by omega)] at h1
        exact Bool.false_ne_true h1
      have hs2 : s < w'.length := by omega
      simp only [F, getD_append_singleton, hs1, hs2, ↓reduceIte]
      exact ⟨h1, h2⟩
    · intro i hi
      simp only [F, getD_append_singleton, hlen, hga]
      split_ifs
      · rw [← hlen] at *
        exact hag i hi
      · rfl
      · rfl

end PEqualNP.Outside.L_meta_7585

theorem PEqualNP.Outside.L_meta_7585 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin x1), x2.Adj x5 x6 → PEqualNP.MetaComplexity.FanInTwo x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∃ x10 ∈ x4.gates, ↑x5 ∈ List.take (bif x10.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x10.inputs := by
  intro n G _ C v u hvu hfan hfun
  by_contra hcon
  push_neg at hcon
  have hW : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x := fun x => congrFun hfun x
  have hwires : ∀ x : List Bool, C.wires x = C.gates.foldl PEqualNP.Outside.L_meta_7585.F x := fun x => rfl
  have hout : C.output ≠ (v : ℕ) := by
    intro ho
    have h1 := hW (fun i => decide (i = v))
    have h2 : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (fun i => decide (i = v)) = false := by
      unfold PEqualNP.MetaComplexity.NestedCover.graphFun
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      constructor
      · rintro ⟨a, ha, _⟩
        simp at ha
      · rintro ⟨a, b, hab, ha, hb⟩
        simp only [decide_eq_true_eq] at ha hb
        subst ha
        subst hb
        exact G.irrefl hab
    rw [h2] at h1
    have h3 : C.eval (List.ofFn (fun i => decide (i = v))) = true := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [hwires, ho, PEqualNP.Outside.L_meta_7585.fold_keep _ _ _ (by simp), PEqualNP.Outside.L_meta_7585.ofFn_getD]
      simp
    rw [h3] at h1
    exact absurd h1 (by decide)
  set x0 : Fin n → Bool := fun i => decide (i = u) with hx0
  set x1 : Fin n → Bool := fun i => decide (i = u ∨ i = v) with hx1
  have hf0 : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x0 = false := by
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    constructor
    · rintro ⟨a, ha, _⟩
      simp at ha
    · rintro ⟨a, b, hab, ha, hb⟩
      simp only [hx0, decide_eq_true_eq] at ha hb
      subst ha
      subst hb
      exact G.irrefl hab
  have hf1 : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x1 = true := by
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨v, u, hvu, by simp [hx1], by simp [hx1]⟩
  have hagree := PEqualNP.Outside.L_meta_7585.wires_agree C.gates (v : ℕ) (fun _ => False) hfan
    (fun g hg hv => absurd hv (hcon g hg))
    (List.ofFn x0) (List.ofFn x1) (by simp)
    (fun s hs => hs.elim)
    (by
      intro i hi
      simp only [PEqualNP.Outside.L_meta_7585.ofFn_getD, hx0, hx1]
      split_ifs with h
      · have : (⟨i, h⟩ : Fin n) ≠ v := fun e => hi (by rw [← e])
        simp [this]
      · rfl)
    C.output hout
  have e0 := hW x0
  have e1 := hW x1
  rw [hf0] at e0
  rw [hf1] at e1
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval at e0 e1
  rw [hwires] at e0 e1
  rw [hagree, e1] at e0
  exact absurd e0 (by decide)
