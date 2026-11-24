import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2772

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem len_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, step, Nat.add_comm, Nat.add_left_comm]

theorem keepWire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_last (w : List Bool) (a : Bool) : (w ++ [a]).getD w.length false = a := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

theorem step_mono (w w' : List Bool) (g g' : Gate) (hl : w.length = w'.length)
    (hw : ∀ i, w'.getD i false = true → w.getD i false = true)
    (hg : g'.op.eval (g'.inputs.map fun i => w'.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    ∀ i, (step w' g').getD i false = true → (step w g).getD i false = true := by
  intro i hi
  rcases lt_trichotomy i w.length with h | h | h
  · have h' : i < w'.length := hl ▸ h
    have hw' := hw i
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left h,
      List.getElem?_append_left h'] at hi hw' ⊢
    exact hw' hi
  · unfold step at hi ⊢
    rw [h, getD_last]
    rw [h, hl, getD_last] at hi
    exact hg hi
  · unfold step at hi
    rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact absurd hi (by simp)

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (F F' : ℕ → Bool) (h : ∀ i, F' i = true → F i = true) :
    op.eval (l.map F') = true → op.eval (l.map F) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map]
    intro H a ha
    obtain ⟨i, hi, rfl⟩ := ha
    simp only [id]
    exact h i (by simpa using H (F' i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map]
    rintro ⟨a, ⟨i, hi, rfl⟩, ha⟩
    exact ⟨F i, ⟨i, hi, rfl⟩, by simpa using h i (by simpa using ha)⟩

theorem fold_mono (gs : List Gate) (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, w.length = w'.length →
      (∀ i, w'.getD i false = true → w.getD i false = true) →
      ∀ i, (gs.foldl step w').getD i false = true → (gs.foldl step w).getD i false = true := by
  induction gs with
  | nil => intro w w' _ hw i hi; exact hw i hi
  | cons g gs ih =>
    intro w w' hl hw
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg')) (step w g) (step w' g)
      (by simp [step, hl])
      (step_mono w w' g g hl hw (eval_mono g.op (hops g (by simp)) g.inputs _ _ hw))

theorem set_mono (gs : List Gate) (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w : List Bool) (j : ℕ) (g' : Gate) (hj : j < gs.length),
      (g'.op.eval (g'.inputs.map fun i => ((gs.take j).foldl step w).getD i false) = true →
        (gs[j]).op.eval ((gs[j]).inputs.map fun i => ((gs.take j).foldl step w).getD i false) = true) →
      ∀ i, ((gs.set j g').foldl step w).getD i false = true → (gs.foldl step w).getD i false = true := by
  induction gs with
  | nil => intro w j g' hj; simp at hj
  | cons g0 rest ih =>
    intro w j g' hj H
    have hops' : ∀ g ∈ rest, g.op = GateOp.and ∨ g.op = GateOp.or :=
      fun g hg => hops g (List.mem_cons_of_mem _ hg)
    cases j with
    | zero =>
      simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at H
      intro i hi
      simp only [List.set_cons_zero, List.foldl_cons] at hi ⊢
      exact fold_mono rest hops' (step w g0) (step w g') (by simp [step])
        (step_mono w w g0 g' rfl (fun _ h => h) H) i hi
    | succ j =>
      simp only [List.take_succ_cons, List.foldl_cons, List.getElem_cons_succ] at H
      intro i hi
      simp only [List.set_cons_succ, List.foldl_cons] at hi ⊢
      exact ih hops' (step w g0) j g' (by simp at hj; omega) H i hi

theorem prefix_read (gs : List Gate) (w : List Bool) (j i : ℕ) (hj : j ≤ gs.length)
    (hi : i < w.length + j) :
    ((gs.take j).foldl step w).getD i false = (gs.foldl step w).getD i false := by
  conv_rhs => rw [← List.take_append_drop j gs]
  rw [List.foldl_append, keepWire (gs.drop j) ((gs.take j).foldl step w) i
    (by rw [len_fold, List.length_take, Nat.min_eq_left hj]; exact hi)]

theorem set_mono_rev (gs : List Gate) (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w : List Bool) (j : ℕ) (g' : Gate) (hj : j < gs.length),
      ((gs[j]).op.eval ((gs[j]).inputs.map fun i => ((gs.take j).foldl step w).getD i false) = true →
        g'.op.eval (g'.inputs.map fun i => ((gs.take j).foldl step w).getD i false) = true) →
      ∀ i, (gs.foldl step w).getD i false = true → ((gs.set j g').foldl step w).getD i false = true := by
  induction gs with
  | nil => intro w j g' hj; simp at hj
  | cons g0 rest ih =>
    intro w j g' hj H
    have hops' : ∀ g ∈ rest, g.op = GateOp.and ∨ g.op = GateOp.or :=
      fun g hg => hops g (List.mem_cons_of_mem _ hg)
    cases j with
    | zero =>
      simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at H
      intro i hi
      simp only [List.set_cons_zero, List.foldl_cons] at hi ⊢
      exact fold_mono rest hops' (step w g') (step w g0) (by simp [step])
        (step_mono w w g' g0 rfl (fun _ h => h) H) i hi
    | succ j =>
      simp only [List.take_succ_cons, List.foldl_cons, List.getElem_cons_succ] at H
      intro i hi
      simp only [List.set_cons_succ, List.foldl_cons] at hi ⊢
      exact ih hops' (step w g0) j g' (by simp at hj; omega) H i hi

theorem gate_le (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (u v b c d : ℕ)
    (F : ℕ → Bool) (hb : b < 2) (hc : [u, v].getD b 0 = c) (key : F d = true → F c = true) :
    op.eval (([u, v].set b d).map F) = true → op.eval ([u, v].map F) = true := by
  rcases hop with rfl | rfl <;> rcases b with _ | _ | b
  all_goals first
    | omega
    | (simp only [List.getD_cons_zero, List.getD_cons_succ] at hc
       subst hc
       simp only [List.set_cons_zero, List.set_cons_succ, List.map_cons, List.map_nil,
         GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id,
         Bool.and_true, Bool.or_false, Bool.and_eq_true, Bool.or_eq_true]
       tauto)

theorem gate_ge (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (u v b c d : ℕ)
    (F : ℕ → Bool) (hb : b < 2) (hc : [u, v].getD b 0 = c) (key : F c = true → F d = true) :
    op.eval ([u, v].map F) = true → op.eval (([u, v].set b d).map F) = true := by
  rcases hop with rfl | rfl <;> rcases b with _ | _ | b
  all_goals first
    | omega
    | (simp only [List.getD_cons_zero, List.getD_cons_succ] at hc
       subst hc
       simp only [List.set_cons_zero, List.set_cons_succ, List.map_cons, List.map_nil,
         GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id,
         Bool.and_true, Bool.or_false, Bool.and_eq_true, Bool.or_eq_true]
       tauto)

theorem gateAt_self (gs : List Gate) (g : ℕ) (hg : g < gs.length) (g' : Gate) (o : ℕ) :
    gateAt ⟨gs.set g g', o⟩ g = g' := by
  simp [gateAt, List.getD_eq_getElem?_getD, hg]

theorem gateAt_ne (gs : List Gate) (g j : ℕ) (h : j ≠ g) (g' : Gate) (o : ℕ) :
    gateAt ⟨gs.set g g', o⟩ j = gateAt ⟨gs, o⟩ j := by
  simp [gateAt, List.getD_eq_getElem?_getD, Ne.symm h]

theorem core (n : ℕ) (C : Circuit) (g b w w' : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hb : b < 2)
    (hc : (gateAt C g).inputs.getD b 0 = w) (hd : w' < n + g)
    (hww : ∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, w⟩ (List.ofFn x) = true →
      Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true)
    (hwf : ∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true →
      circuitFun n C x = true)
    (g' : Gate) (hg' : g' = ⟨(gateAt C g).op, (gateAt C g).inputs.set b w'⟩)
    (C' : Circuit) (hC' : C' = ⟨C.gates.set g g', C.output⟩) :
    PEqualNP.TopForm.IsAO2 n C' ∧ circuitFun n C' = circuitFun n C ∧ C'.size = C.size := by
  obtain ⟨hops, _, hlen2⟩ := hAO
  have hGmem : C.gates[g] = gateAt C g := by
    simp [gateAt, List.getD_eq_getElem?_getD, hg]
  have hGin : gateAt C g ∈ C.gates := hGmem ▸ List.getElem_mem hg
  have hops' : ∀ x ∈ C'.gates, x.op = GateOp.and ∨ x.op = GateOp.or := by
    intro x hx
    rw [hC'] at hx
    rcases List.mem_or_eq_of_mem_set hx with h | h
    · exact hops x h
    · rw [h, hg']; exact hops (gateAt C g) hGin
  have hlen : (gateAt C g).inputs.length = 2 := hlen2 _ hGin
  obtain ⟨u, v, huv⟩ := List.length_eq_two.mp hlen
  have hcmem : w ∈ (gateAt C g).inputs := by
    rw [← hc, huv]
    rcases b with _ | _ | b
    · simp
    · simp
    · omega
  have hclt : w < n + g := hRB g hg w hcmem
  have hc2 : [u, v].getD b 0 = w := by rw [← huv]; exact hc
  have hopg := hops _ hGin
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨hops', ?_, ?_⟩
    · intro j hj i hi
      have hj' : j < C.gates.length := by rw [hC'] at hj; simpa using hj
      by_cases hjg : j = g
      · subst hjg
        rw [hC', gateAt_self _ _ hg, hg'] at hi
        rcases List.mem_or_eq_of_mem_set hi with h | h
        · exact hRB j hj' i h
        · rw [h]; exact hd
      · rw [hC', gateAt_ne _ _ _ hjg] at hi
        exact hRB j hj' i hi
    · intro x hx
      rw [hC'] at hx
      rcases List.mem_or_eq_of_mem_set hx with h | h
      · exact hlen2 x h
      · rw [h, hg']; simp [List.length_set, hlen]
  · funext x
    have pw : ((C.gates.take g).foldl step (List.ofFn x)).getD w false =
        Circuit.eval ⟨C.gates, w⟩ (List.ofFn x) := by
      unfold Circuit.eval; rw [wires_eq]
      exact prefix_read _ _ _ _ hg.le (by simpa using hclt)
    have pw' : ((C.gates.take g).foldl step (List.ofFn x)).getD w' false =
        Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) := by
      unfold Circuit.eval; rw [wires_eq]
      exact prefix_read _ _ _ _ hg.le (by simpa using hd)
    cases hf : circuitFun n C x with
    | true =>
      have hx : C.eval (List.ofFn x) = true := hf
      show C'.eval (List.ofFn x) = true
      unfold Circuit.eval at hx ⊢
      rw [wires_eq] at hx ⊢
      rw [hC']
      refine set_mono_rev C.gates hops (List.ofFn x) g g' hg ?_ C.output hx
      rw [hGmem, hg']
      simp only
      rw [huv]
      exact gate_ge _ hopg u v b w w' _ hb hc2 (by rw [pw, pw']; exact hww x)
    | false =>
      cases h' : circuitFun n C' x with
      | false => rfl
      | true =>
        exfalso
        have hx : C'.eval (List.ofFn x) = true := h'
        unfold Circuit.eval at hx
        rw [wires_eq] at hx
        rw [hC'] at hx
        have key : g'.op.eval (g'.inputs.map fun i =>
            ((C.gates.take g).foldl step (List.ofFn x)).getD i false) = true →
            (C.gates[g]).op.eval ((C.gates[g]).inputs.map fun i =>
              ((C.gates.take g).foldl step (List.ofFn x)).getD i false) = true := by
          rw [hGmem, hg']
          simp only
          rw [huv]
          refine gate_le _ hopg u v b w w' _ hb hc2 ?_
          rw [pw']
          intro h3
          have h4 := hwf x h3
          rw [hf] at h4; exact absurd h4 (by simp)
        have h5 := set_mono C.gates hops (List.ofFn x) g g' hg key C.output hx
        have h2 : circuitFun n C x = true := by
          show C.eval (List.ofFn x) = true
          unfold Circuit.eval; rw [wires_eq]; exact h5
        rw [hf] at h2; exact absurd h2 (by simp)
  · rw [hC']; simp [Circuit.size, List.length_set]

end PEqualNP.Outside.L_meta_2772

theorem PEqualNP.Outside.L_meta_2772 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b w w' : ℕ),
  (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = w ∧ w' < n + g ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w⟩ (List.ofFn x) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true) ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true →
    PEqualNP.MetaComplexity.circuitFun n C x = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧
  PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ∧
  (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size := by
  intro n C g b w w' h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact PEqualNP.Outside.L_meta_2772.core n C g b w w' h1 h2 h3 h4 h5 h6 h7 h8 _ rfl _ rfl
