import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2852

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

theorem ofFn_mono {n : ℕ} (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
  intro i hi
  by_cases h : i < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h] at hi ⊢
    simpa using hxy ⟨i, h⟩ (by simpa using hi)
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact absurd hi (by simp)

theorem fun_mono (n : ℕ) (C : Circuit) (hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  intro hx
  unfold circuitFun Circuit.eval at *
  rw [wires_eq] at *
  exact fold_mono C.gates hops (List.ofFn y) (List.ofFn x) (by simp) (ofFn_mono x y hxy) C.output hx

theorem exists_min {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : f x = true) :
    ∃ y : Fin n → Bool, (∀ i, y i = true → x i = true) ∧ f y = true ∧
      ∀ z : Fin n → Bool, (∀ i, z i = true → y i = true) → z ≠ y → f z = false := by
  classical
  let S := Finset.univ.filter (fun y : Fin n → Bool => (∀ i, y i = true → x i = true) ∧ f y = true)
  have hxS : x ∈ S := by simp [S, hx]
  obtain ⟨y, hyS, hmin⟩ := S.exists_min_image
    (fun y => (Finset.univ.filter (fun i => y i = true)).card) ⟨x, hxS⟩
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hyS
  refine ⟨y, hyS.1, hyS.2, ?_⟩
  intro z hzy hne
  by_contra hfz
  have hfz' : f z = true := by simpa using hfz
  have hzS : z ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun i hi => hyS.1 i (hzy i hi), hfz'⟩
  have hle := hmin z hzS
  have hsub : Finset.univ.filter (fun i => z i = true) ⊆ Finset.univ.filter (fun i => y i = true) := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hzy i
  have hne' : Finset.univ.filter (fun i => z i = true) ≠ Finset.univ.filter (fun i => y i = true) := by
    intro heq
    apply hne
    funext i
    have := congrArg (fun s => i ∈ s) heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    cases hz : z i <;> cases hy : y i <;> simp_all
  have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne'⟩)
  omega

theorem gateAt_self (gs : List Gate) (g : ℕ) (hg : g < gs.length) (g' : Gate) (o : ℕ) :
    gateAt ⟨gs.set g g', o⟩ g = g' := by
  simp [gateAt, List.getD_eq_getElem?_getD, hg]

theorem gateAt_ne (gs : List Gate) (g j : ℕ) (h : j ≠ g) (g' : Gate) (o : ℕ) :
    gateAt ⟨gs.set g g', o⟩ j = gateAt ⟨gs, o⟩ j := by
  simp [gateAt, List.getD_eq_getElem?_getD, Ne.symm h]

theorem core (n : ℕ) (C : Circuit) (g b c d : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hb : b < 2)
    (hc : (gateAt C g).inputs.getD b 0 = c) (hd : d < n + g)
    (hdc : ∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, d⟩ (List.ofFn x) = true →
      Circuit.eval ⟨C.gates, c⟩ (List.ofFn x) = true)
    (g' : Gate) (hg' : g' = ⟨(gateAt C g).op, (gateAt C g).inputs.set b d⟩)
    (C' : Circuit) (hC' : C' = ⟨C.gates.set g g', C.output⟩) :
    PEqualNP.TopForm.IsAO2 n C' ∧ C'.size = C.size ∧
      (∀ x : Fin n → Bool, circuitFun n C' x = true → circuitFun n C x = true) ∧
      (circuitFun n C' = circuitFun n C ↔
        (∀ x : Fin n → Bool, (circuitFun n C x = true ∧ ∀ y : Fin n → Bool,
          (∀ i, y i = true → x i = true) → y ≠ x → circuitFun n C y = false) →
          circuitFun n C' x = true)) := by
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
  have hle : ∀ x : Fin n → Bool, circuitFun n C' x = true → circuitFun n C x = true := by
    intro x hx
    unfold circuitFun Circuit.eval at *
    rw [wires_eq] at *
    rw [hC'] at hx
    refine set_mono C.gates hops (List.ofFn x) g g' hg ?_ C.output hx
    rw [hGmem]
    have key : ((C.gates.take g).foldl step (List.ofFn x)).getD d false = true →
        ((C.gates.take g).foldl step (List.ofFn x)).getD c false = true := by
      have hcmem : c ∈ (gateAt C g).inputs := by
        rw [← hc, huv]
        rcases b with _ | _ | b
        · simp
        · simp
        · omega
      have hclt : c < n + g := hRB g hg c hcmem
      rw [prefix_read _ _ _ _ hg.le (by simpa using hd),
        prefix_read _ _ _ _ hg.le (by simpa using hclt)]
      exact hdc x
    rw [hg']
    simp only
    rw [huv] at hc ⊢
    rcases hops _ hGin with hop | hop <;> rw [hop] <;>
    rcases b with _ | _ | b
    all_goals first
      | omega
      | (simp only [List.getD_cons_zero, List.getD_cons_succ] at hc
         subst hc
         simp only [List.set_cons_zero, List.set_cons_succ, List.map_cons, List.map_nil,
           GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id,
           Bool.and_true, Bool.or_false, Bool.and_eq_true, Bool.or_eq_true]
         tauto)
  refine ⟨?_, ?_, hle, ?_⟩
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
  · rw [hC']; simp [Circuit.size, List.length_set]
  · constructor
    · intro heq x hx
      rw [heq]; exact hx.1
    · intro H
      funext x
      cases h' : circuitFun n C' x with
      | true => exact (hle x h').symm
      | false =>
        cases hf : circuitFun n C x with
        | false => rfl
        | true =>
          obtain ⟨y, hyx, hfy, hmin⟩ := exists_min (circuitFun n C) x hf
          have hy' := H y ⟨hfy, fun z hz hne => hmin z hz hne⟩
          have := fun_mono n C' hops' y x hyx hy'
          rw [h'] at this
          exact absurd this (by simp)

end PEqualNP.Outside.L_meta_2852

theorem PEqualNP.Outside.L_meta_2852 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b c d : ℕ), (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = c ∧ d < n + g ∧ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, d⟩ (List.ofFn x) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, c⟩ (List.ofFn x) = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true → PEqualNP.MetaComplexity.circuitFun n C x = true) ∧ (PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ↔ (∀ x : Fin n → Bool, (PEqualNP.MetaComplexity.circuitFun n C x = true ∧ ∀ y : Fin n → Bool, (∀ i, y i = true → x i = true) → y ≠ x → PEqualNP.MetaComplexity.circuitFun n C y = false) → PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true)) := by
  intro n C g b c d h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact PEqualNP.Outside.L_meta_2852.core n C g b c d h1 h2 h3 h4 h5 h6 h7 _ rfl _ rfl
