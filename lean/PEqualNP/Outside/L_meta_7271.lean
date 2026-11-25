import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7271

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

theorem fold_len (gs : List Gate) : ∀ w : List Bool, (gs.foldl stp w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; simp [ih, stp]; omega

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def sh (f i : ℕ) : ℕ := if i < f then i else i - 1

def tr (f : ℕ) (g : Gate) : Gate :=
  if isAnd g.op = true ∧ f ∈ g.inputs then ⟨GateOp.or, []⟩
  else ⟨g.op, (g.inputs.filter fun i => decide (i ≠ f)).map (sh f)⟩

theorem getsh (f : ℕ) (P : List Bool) (i : ℕ) (hi : i ≠ f) :
    (P.eraseIdx f).getD (sh f i) false = P.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
  rcases lt_or_gt_of_ne hi with h | h
  · have e : sh f i = i := if_pos h
    rw [e, if_pos h]
  · have e : sh f i = i - 1 := if_neg (by omega)
    rw [e, if_neg (by omega)]
    congr 2
    omega

theorem any_drop (P : List Bool) (f : ℕ) (hf : P.getD f false = false) (ins : List ℕ) :
    ((ins.filter fun i => decide (i ≠ f)).map fun i => P.getD i false).any id
      = (ins.map fun i => P.getD i false).any id := by
  induction ins with
  | nil => rfl
  | cons a t ih =>
    rw [List.filter_cons]
    by_cases h : a = f
    · subst h
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
      rw [ih]
      simp only [List.map_cons, List.any_cons, hf, id, Bool.false_or]
    · simp only [ne_eq, h, not_false_eq_true, decide_true, if_true, List.map_cons, List.any_cons]
      rw [ih]

theorem val (f : ℕ) (P : List Bool) (hf : P.getD f false = false) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (tr f g).op.eval ((tr f g).inputs.map fun i => (P.eraseIdx f).getD i false)
      = g.op.eval (g.inputs.map fun i => P.getD i false) := by
  obtain ⟨op, ins⟩ := g
  have hmap : ((ins.filter fun i => decide (i ≠ f)).map (sh f)).map
      (fun i => (P.eraseIdx f).getD i false)
      = (ins.filter fun i => decide (i ≠ f)).map fun i => P.getD i false := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    have : i ≠ f := by simpa using (List.mem_filter.1 hi).2
    simp only [Function.comp]
    exact getsh f P i this
  rcases hg with h | h
  · simp only at h
    subst h
    by_cases hm : f ∈ ins
    · have e : tr f ⟨GateOp.and, ins⟩ = ⟨GateOp.or, []⟩ := by simp [tr, isAnd, hm]
      rw [e]
      simp only [GateOp.eval, List.map_nil, List.any_nil]
      symm
      rw [Bool.eq_false_iff]
      intro hc
      rw [List.all_eq_true] at hc
      have := hc (P.getD f false) (List.mem_map.2 ⟨f, hm, rfl⟩)
      rw [id, hf] at this
      exact Bool.false_ne_true this
    · have e : tr f ⟨GateOp.and, ins⟩
          = ⟨GateOp.and, (ins.filter fun i => decide (i ≠ f)).map (sh f)⟩ := by
        simp [tr, isAnd, hm]
      rw [e]
      simp only
      rw [hmap]
      have hfil : (ins.filter fun i => decide (i ≠ f)) = ins := by
        rw [List.filter_eq_self]
        intro a ha
        have : a ≠ f := fun h => hm (h ▸ ha)
        simpa using this
      rw [hfil]
  · simp only at h
    subst h
    have e : tr f ⟨GateOp.or, ins⟩
        = ⟨GateOp.or, (ins.filter fun i => decide (i ≠ f)).map (sh f)⟩ := by
      simp [tr, isAnd]
    rw [e]
    simp only [GateOp.eval]
    rw [hmap, any_drop P f hf ins]

theorem fold_rel (f : ℕ) (B : List Gate) (hB : ∀ g ∈ B, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ P : List Bool, f < P.length → P.getD f false = false →
      (B.map (tr f)).foldl stp (P.eraseIdx f) = (B.foldl stp P).eraseIdx f ∧
      (B.foldl stp P).getD f false = false := by
  induction B with
  | nil => intro P _ h; exact ⟨rfl, h⟩
  | cons g B ih =>
    intro P hl hf
    have hg := hB g (by simp)
    have hB' : ∀ g ∈ B, g.op = GateOp.and ∨ g.op = GateOp.or := fun g' hg' => hB g' (by simp [hg'])
    have e1 : stp (P.eraseIdx f) (tr f g) = (stp P g).eraseIdx f := by
      unfold stp
      rw [List.eraseIdx_append_of_lt_length hl, val f P hf g hg]
    have hl2 : f < (stp P g).length := by simp [stp]; omega
    have hf2 : (stp P g).getD f false = false := by
      unfold stp
      rw [List.getD_append _ _ _ _ hl]; exact hf
    obtain ⟨r1, r2⟩ := ih hB' (stp P g) hl2 hf2
    refine ⟨?_, r2⟩
    simp only [List.map_cons, List.foldl_cons]
    rw [e1, r1]

def Le (P Q : List Bool) : Prop := P.length = Q.length ∧ ∀ i, P.getD i false = true → Q.getD i false = true

theorem getD_snoc {α : Type} (l : List α) (x d : α) (i : ℕ) :
    (l ++ [x]).getD i d = if i < l.length then l.getD i d else if i = l.length then x else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem fold_le (B : List Gate) (hB : ∀ g ∈ B, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ P Q : List Bool, Le P Q → Le (B.foldl stp P) (B.foldl stp Q) := by
  induction B with
  | nil => intro P Q h; exact h
  | cons g B ih =>
    intro P Q h
    have hg := hB g (by simp)
    have hB' : ∀ g ∈ B, g.op = GateOp.and ∨ g.op = GateOp.or := fun g' hg' => hB g' (by simp [hg'])
    apply ih hB'
    obtain ⟨hl, hi⟩ := h
    refine ⟨by simp [stp, hl], ?_⟩
    intro i
    unfold stp
    rw [getD_snoc, getD_snoc, hl]
    split_ifs with h1 h2
    · exact hi i
    · obtain ⟨op, ins⟩ := g
      rcases hg with e | e <;> simp only at e <;> subst e
      · simp only [GateOp.eval, List.all_eq_true, List.mem_map]
        intro H x hx
        obtain ⟨a, ha, rfl⟩ := hx
        exact hi a (H _ ⟨a, ha, rfl⟩)
      · simp only [GateOp.eval, List.any_eq_true, List.mem_map]
        intro H
        obtain ⟨x, ⟨a, ha, rfl⟩, hx⟩ := H
        exact ⟨_, ⟨a, ha, rfl⟩, hi a hx⟩
    · intro h; exact h

end PEqualNP.Outside.L_meta_7271

open PEqualNP.Outside.L_meta_7271 in
theorem PEqualNP.Outside.L_meta_7271 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ),   PEqualNP.TopForm.IsAO2 x1 x2 →     x3 < x2.size →       have x6 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2.gates.set x3 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit };       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 ∧ x7.size < x2.size ∧ ∀ (x8 : List Bool), x8.length = x1 → x7.eval x8 = x6.eval x8 ∧ (x7.eval x8 = Bool.true → x2.eval x8 = Bool.true) := by
  intro n C k hAO hk
  dsimp only
  obtain ⟨hand, hrb, hlen⟩ := hAO
  have hgs : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := hand
  have hk' : k < C.gates.length := hk
  set gs := C.gates with hgsdef
  set A := gs.take k with hA
  set B := gs.drop (k + 1) with hB
  set f := n + k with hf
  have hAlen : A.length = k := by simp [hA]; omega
  have hsplit : gs = A ++ gs[k] :: B := by
    rw [hA, hB, ← List.drop_eq_getElem_cons hk', List.take_append_drop]
  have hset : gs.set k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
      = A ++ (⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ : PEqualNP.CircuitLowerBounds.Gate) :: B := by
    conv_lhs => rw [hsplit]
    rw [List.set_append_right _ _ (by omega), hAlen, Nat.sub_self, List.set_cons_zero]
  have hAsub : ∀ g ∈ A, g ∈ gs := fun g hg => List.mem_of_mem_take hg
  have hBsub : ∀ g ∈ B, g ∈ gs := fun g hg => List.mem_of_mem_drop hg
  have hBao : ∀ g ∈ B, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g hg => hgs g (hBsub g hg)
  refine ⟨⟨A ++ B.map (tr f), if C.output = f then n + gs.length else sh f C.output⟩, ?_, ?_, ?_, ?_⟩
  · -- Monotone2
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · have h1 := hgs g (hAsub g hg)
      have h2 := hlen g (hAsub g hg)
      refine ⟨?_, by omega⟩
      rcases h1 with e | e <;> rw [e] <;> simp
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
      have h1 := hgs g' (hBsub g' hg')
      have h2 := hlen g' (hBsub g' hg')
      unfold tr
      split_ifs
      · simp
      · refine ⟨?_, ?_⟩
        · rcases h1 with e | e <;> rw [e] <;> simp
        · simp only [List.length_map]
          have := List.length_filter_le (fun i => decide (i ≠ f)) g'.inputs
          omega
  · -- ReadsBack
    intro j hj i hi
    have hgl : C.gates.length = gs.length := by rw [hgsdef]
    have hBl : B.length = gs.length - (k + 1) := by simp [hB]
    have hCs : C.size = gs.length := hgl
    simp only [List.length_append, List.length_map] at hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    simp only at hi
    rw [List.getD_eq_getElem _ _ (by simp; omega)] at hi
    by_cases hjk : j < k
    · rw [List.getElem_append_left (by omega)] at hi
      have hjA : A[j] = gs[j] := by simp [hA]
      rw [hjA] at hi
      have := hrb j (by omega) i
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt at this
      rw [List.getD_eq_getElem _ _ (by omega)] at this
      exact this hi
    · rw [List.getElem_append_right (by omega)] at hi
      simp only [List.getElem_map] at hi
      have hjB : B[j - A.length]'(by simp [hB]; omega) = gs[j + 1]'(by omega) := by
        simp only [hB, List.getElem_drop]
        congr 1; omega
      rw [hjB] at hi
      have hrj := hrb (j + 1) (by omega)
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hrj
      rw [List.getD_eq_getElem _ _ (by omega)] at hrj
      unfold tr at hi
      split_ifs at hi
      · simp at hi
      · simp only at hi
        obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi
        have hne : i0 ≠ f := by simpa using (List.mem_filter.1 hi0).2
        have hlt := hrj i0 (List.mem_filter.1 hi0).1
        unfold sh
        split_ifs <;> omega
  · -- size
    show (A ++ B.map (tr f)).length < gs.length
    simp only [List.length_append, List.length_map, hAlen, hB, List.length_drop]
    omega
  · intro x hx
    have hV : (A.foldl stp x).length = f := by rw [fold_len, hx, hAlen]
    set V := A.foldl stp x with hVdef
    have hP0 : stp V ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = V ++ [false] := by
      simp [stp, PEqualNP.CircuitLowerBounds.GateOp.eval]
    have hQ0 : (V ++ [false]).eraseIdx f = V := by
      rw [List.eraseIdx_append_of_length_le (by omega), hV, Nat.sub_self]; simp
    obtain ⟨R1, R2⟩ := fold_rel f B hBao (V ++ [false]) (by simp; omega)
      (by rw [getD_snoc]; simp [hV])
    rw [hQ0] at R1
    have e6 : ∀ o, PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨gs.set k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, o⟩ x
        = (B.foldl stp (V ++ [false])).getD o false := by
      intro o
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [wires_eq]
      simp only
      rw [hset, List.foldl_append, List.foldl_cons, ← hVdef, hP0]
    have e7 : ∀ o, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨A ++ B.map (tr f), o⟩ x
        = ((B.foldl stp (V ++ [false])).eraseIdx f).getD o false := by
      intro o
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [wires_eq]
      simp only
      rw [List.foldl_append, ← hVdef, R1]
    have e2 : PEqualNP.CircuitLowerBounds.Circuit.eval C x
        = (B.foldl stp (V ++ [gs[k].op.eval (gs[k].inputs.map fun i => V.getD i false)])).getD C.output false := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [wires_eq]
      rw [← hgsdef]
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons, ← hVdef]
      rfl
    have heq : PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨A ++ B.map (tr f), if C.output = f then n + gs.length else sh f C.output⟩ x
        = PEqualNP.CircuitLowerBounds.Circuit.eval
          ⟨gs.set k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, C.output⟩ x := by
      rw [e7, e6]
      split_ifs with ho
      · rw [ho, R2]
        apply List.getD_eq_default
        rw [List.length_eraseIdx, fold_len]
        simp only [List.length_append, List.length_singleton, hV]
        have : gs.length = k + 1 + B.length := by
          rw [hB, List.length_drop]; omega
        split_ifs <;> omega
      · exact getsh f _ _ ho
    refine ⟨heq, ?_⟩
    intro h7
    rw [heq, e6] at h7
    rw [e2]
    have hle := fold_le B hBao (V ++ [false]) (V ++ [gs[k].op.eval (gs[k].inputs.map fun i => V.getD i false)])
      ⟨by simp, by
        intro i hi
        rw [getD_snoc] at hi ⊢
        split_ifs at hi ⊢
        all_goals first | exact hi | simp at hi⟩
    exact hle.2 _ h7
