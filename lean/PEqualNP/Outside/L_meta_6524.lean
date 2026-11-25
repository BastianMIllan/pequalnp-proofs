import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6524

open PEqualNP.CircuitLowerBounds

def wm (p q : Equiv.Perm (Fin 13)) (w : ℕ) : ℕ :=
  if h : w < 13 then ((p.symm ⟨w, h⟩ : Fin 13) : ℕ)
  else if h2 : w < 26 then 13 + ((q.symm ⟨w - 13, by omega⟩ : Fin 13) : ℕ)
  else w - 1

lemma wm_lt (p q : Equiv.Perm (Fin 13)) (w : ℕ) (hw : w ≠ 26) (k : ℕ) (hk : 26 ≤ k)
    (h : w < k + 1) : wm p q w < k := by
  unfold wm
  split
  · have := (p.symm ⟨w, by assumption⟩).2; omega
  · split
    · have := (q.symm ⟨w - 13, by omega⟩).2; omega
    · omega

lemma wm_ge (p q : Equiv.Perm (Fin 13)) (w : ℕ) (hw : 26 < w) : wm p q w = w - 1 := by
  unfold wm
  rw [dif_neg (by omega), dif_neg (by omega)]

def absorb (x2 : Bool) : GateOp → Bool
  | GateOp.and => !x2
  | GateOp.or => x2
  | _ => false

def tg (p q : Equiv.Perm (Fin 13)) (x2 : Bool) (g : Gate) : Gate :=
  if 26 ∈ g.inputs ∧ absorb x2 g.op = true then
    ⟨if x2 then GateOp.and else GateOp.or, []⟩
  else ⟨g.op, (g.inputs.filter (fun i => i != 26)).map (wm p q)⟩

lemma all_filt (p q : Equiv.Perm (Fin 13)) (f f' : ℕ → Bool)
    (hf : ∀ i, i ≠ 26 → f' (wm p q i) = f i) (h26 : f 26 = true) (l : List ℕ) :
    (((l.filter (fun i => i != 26)).map (wm p q)).map f').all id = (l.map f).all id := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : a = 26
    · subst ha; simp_all
    · simp_all [List.filter_cons]

lemma any_filt (p q : Equiv.Perm (Fin 13)) (f f' : ℕ → Bool)
    (hf : ∀ i, i ≠ 26 → f' (wm p q i) = f i) (h26 : f 26 = false) (l : List ℕ) :
    (((l.filter (fun i => i != 26)).map (wm p q)).map f').any id = (l.map f).any id := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : a = 26
    · subst ha; simp_all
    · simp_all [List.filter_cons]

lemma map_filt (p q : Equiv.Perm (Fin 13)) (f f' : ℕ → Bool)
    (hf : ∀ i, i ≠ 26 → f' (wm p q i) = f i) (l : List ℕ) (h : 26 ∉ l) :
    ((l.filter (fun i => i != 26)).map (wm p q)).map f' = l.map f := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a ≠ 26 := fun e => h (by simp [e])
    have hl : 26 ∉ l := fun e => h (by simp [e])
    simp [List.filter_cons, ha, ih hl, hf a ha]

lemma gate_eval (p q : Equiv.Perm (Fin 13)) (x2 : Bool) (f f' : ℕ → Bool)
    (hf : ∀ i, i ≠ 26 → f' (wm p q i) = f i) (h26 : f 26 = x2) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (tg p q x2 g).op.eval ((tg p q x2 g).inputs.map f') = g.op.eval (g.inputs.map f) := by
  rcases g with ⟨op, ins⟩
  simp only at hop
  by_cases hm : 26 ∈ ins
  · rcases hop with h | h <;> subst h <;> cases x2
    · simp only [tg, absorb, hm, Bool.not_false, and_self, if_true]
      simp only [GateOp.eval, List.map_nil, List.any_nil, Bool.false_eq_true, ite_false]
      symm
      rw [Bool.eq_false_iff]
      intro hc
      simp only [List.all_eq_true, List.mem_map, id] at hc
      have := hc (f 26) ⟨26, hm, rfl⟩
      simp [h26] at this
    · simp only [tg, absorb, Bool.not_true, Bool.false_eq_true, and_false, ite_false]
      simp only [GateOp.eval]
      exact all_filt p q f f' hf h26 ins
    · simp only [tg, absorb, Bool.false_eq_true, and_false, ite_false]
      simp only [GateOp.eval]
      exact any_filt p q f f' hf h26 ins
    · simp only [tg, absorb, hm, and_self, if_true]
      simp only [GateOp.eval, List.map_nil, List.all_nil]
      symm
      simp only [List.any_eq_true, List.mem_map, id]
      exact ⟨f 26, ⟨26, hm, rfl⟩, h26⟩
  · simp only [tg, hm, false_and, ite_false]
    rw [map_filt p q f f' hf ins hm]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (p q : Equiv.Perm (Fin 13)) (x2 : Bool) (W W' : List Bool) : Prop :=
  27 ≤ W.length ∧ W'.length + 1 = W.length ∧ W.getD 26 false = x2 ∧
    ∀ w : ℕ, w ≠ 26 → W'.getD (wm p q w) false = W.getD w false

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

lemma rel_step (p q : Equiv.Perm (Fin 13)) (x2 : Bool) (W W' : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : Rel p q x2 W W') : Rel p q x2 (step W g) (step W' (tg p q x2 g)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hv : (tg p q x2 g).op.eval ((tg p q x2 g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) :=
    gate_eval p q x2 (fun i => W.getD i false) (fun i => W'.getD i false) h4 h3 g hop
  refine ⟨by simp [step] <;> omega, by simp [step] <;> omega, ?_, ?_⟩
  · simp only [step]
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h3
  intro w hw
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hlt | heq | hgt
  · have hl : wm p q w < W'.length := wm_lt p q w hw W'.length (by omega) (by omega)
    rw [List.getD_append _ _ _ _ hl, List.getD_append _ _ _ _ hlt]
    exact h4 w hw
  · have he : wm p q w = W'.length := by rw [wm_ge p q w (by omega)]; omega
    rw [he, heq, getD_snoc_eq, getD_snoc_eq]
  · have hge : wm p q w = w - 1 := wm_ge p q w (by omega)
    rw [hge, List.getD_eq_default _ _ (by simp <;> omega),
      List.getD_eq_default _ _ (by simp <;> omega)]

lemma rel_fold (p q : Equiv.Perm (Fin 13)) (x2 : Bool) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ W W' : List Bool, Rel p q x2 W W' →
      Rel p q x2 (gs.foldl step W) ((gs.map (tg p q x2)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih (fun g' hg' => hgs g' (by simp [hg'])) _ _
      (rel_step p q x2 W W' g (hgs g (by simp)) h)

lemma rel_init (p q : Equiv.Perm (Fin 13)) (x2 : Bool) (x9 x10 : Fin 13 → Bool) :
    Rel p q x2 (List.ofFn (x9 ∘ ⇑p.symm) ++ List.ofFn (x10 ∘ ⇑q.symm) ++ [x2])
      (List.ofFn x9 ++ List.ofFn x10) := by
  refine ⟨by simp, by simp, ?_, ?_⟩
  · rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  intro w hw
  unfold wm
  split
  · rename_i h
    rw [List.getD_append _ _ _ _ (by simp <;> omega), List.getD_append _ _ _ _ (by simp <;> omega),
      List.getD_append _ _ _ _ (by simp <;> omega)]
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp <;> omega)]
    rw [List.getElem_ofFn, List.getElem_ofFn]
    simp
  · split
    · rename_i h h2
      rw [List.getD_append_right _ _ _ _ (by simp <;> omega),
        List.getD_append _ _ _ _ (by simp <;> omega),
        List.getD_append_right _ _ _ _ (by simp <;> omega)]
      rw [List.getD_eq_getElem _ _ (by simp <;> omega), List.getD_eq_getElem _ _ (by simp <;> omega)]
      rw [List.getElem_ofFn, List.getElem_ofFn]
      simp
    · rename_i h h2
      rw [List.getD_eq_default _ _ (by simp <;> omega), List.getD_eq_default _ _ (by simp <;> omega)]

end PEqualNP.Outside.L_meta_6524

theorem PEqualNP.Outside.L_meta_6524 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool) (x3 x4 : Equiv.Perm (Fin (13 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x6 : Fin x1.gates.length), ∀ x7 ∈ (x1.gates.get x6).inputs, x7 < (27 : ℕ) + ↑x6) → x1.output ≠ (26 : ℕ) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ (∀ (x9 : Fin x8.gates.length), ∀ x10 ∈ (x8.gates.get x9).inputs, x10 < (26 : ℕ) + ↑x9) ∧ x8.size ≤ x1.size ∧ ∀ (x9 x10 : Fin (13 : ℕ) → Bool), x8.eval (List.ofFn x9 ++ List.ofFn x10) = x1.eval (List.ofFn (x9 ∘ ⇑(Equiv.symm x3)) ++ List.ofFn (x10 ∘ ⇑(Equiv.symm x4)) ++ [x2]) := by
  intro x1 x2 x3 x4 hmono hord hout
  have hops : ∀ g ∈ x1.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have := (hmono g hg).1
    simpa using this
  refine ⟨⟨x1.gates.map (PEqualNP.Outside.L_meta_6524.tg x3 x4 x2),
    PEqualNP.Outside.L_meta_6524.wm x3 x4 x1.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have hm := hmono g0 hg0
    unfold PEqualNP.Outside.L_meta_6524.tg
    split
    · refine ⟨?_, by simp⟩
      split <;> simp
    · refine ⟨hm.1, ?_⟩
      simp only [List.length_map]
      exact le_trans (List.length_filter_le _ _) hm.2
  · intro x9 x10 hx10
    have hl : (x9 : ℕ) < x1.gates.length := by
      have := x9.2; simpa using this
    have hget : (List.map (PEqualNP.Outside.L_meta_6524.tg x3 x4 x2) x1.gates).get x9
        = PEqualNP.Outside.L_meta_6524.tg x3 x4 x2 (x1.gates.get ⟨x9, hl⟩) := by
      simp
    rw [hget] at hx10
    unfold PEqualNP.Outside.L_meta_6524.tg at hx10
    split at hx10
    · simp at hx10
    · simp only [List.mem_map, List.mem_filter] at hx10
      obtain ⟨i, ⟨hi, hi26⟩, rfl⟩ := hx10
      have hi' : i < 27 + (x9 : ℕ) := hord ⟨x9, hl⟩ i hi
      simp only [bne_iff_ne, ne_eq] at hi26
      exact PEqualNP.Outside.L_meta_6524.wm_lt x3 x4 i hi26 (26 + x9) (by omega) (by omega)
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x9 x10
    have h := (PEqualNP.Outside.L_meta_6524.rel_fold x3 x4 x2 x1.gates hops _ _
      (PEqualNP.Outside.L_meta_6524.rel_init x3 x4 x2 x9 x10)).2.2.2 x1.output hout
    exact h
