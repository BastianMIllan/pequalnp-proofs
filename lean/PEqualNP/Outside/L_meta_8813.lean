import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8813

open PEqualNP.CircuitLowerBounds

def F (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl F x := rfl

theorem fold_len (gs : List Gate) (w : List Bool) : (gs.foldl F w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [F, List.length_append, List.length_cons, List.length_nil]
    omega

def dl (w i : ℕ) : ℕ := if i < w then i else i - 1

def rg (w : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (dl w)⟩

theorem F_rg (Q Q' : List Bool) (w : ℕ) (g : Gate)
    (h : ∀ i ∈ g.inputs, Q'.getD (dl w i) false = Q.getD i false) :
    (rg w g).op.eval ((rg w g).inputs.map fun i => Q'.getD i false)
      = g.op.eval (g.inputs.map fun i => Q.getD i false) := by
  simp only [rg, List.map_map]
  exact congrArg _ (List.map_congr_left fun i hi => h i hi)

theorem stageA (w : ℕ) (A : List Gate) (hA : ∀ g ∈ A, w ∉ g.inputs) :
    ∀ Q : List Bool, Q.length + A.length ≤ w → (A.map (rg w)).foldl F Q = A.foldl F Q := by
  induction A with
  | nil => intro Q _; rfl
  | cons g A ih =>
    intro Q hQ
    simp only [List.map_cons, List.foldl_cons]
    have hg := hA g (by simp)
    have hF : F Q (rg w g) = F Q g := by
      unfold F
      rw [F_rg Q Q w g]
      intro i hi
      have hne : i ≠ w := fun h => hg (h ▸ hi)
      simp only [List.length_cons] at hQ
      by_cases hiw : i < w
      · simp [dl, hiw]
      · simp only [dl, hiw, ite_false]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    rw [hF]
    apply ih (fun g' hg' => hA g' (by simp [hg']))
    simp only [F, List.length_append, List.length_cons, List.length_nil, List.length_cons] at hQ ⊢
    omega

theorem key (P M : List Bool) (v : Bool) (w : ℕ) (hP : P.length = w) (i : ℕ) (hi : i ≠ w) :
    (P ++ M).getD (dl w i) false = (P ++ v :: M).getD i false := by
  by_cases hiw : i < w
  · simp only [dl, hiw, ite_true]
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  · simp only [dl, hiw, ite_false]
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hP]
    obtain ⟨k, hk⟩ : ∃ k, i - w = k + 1 := ⟨i - w - 1, by omega⟩
    rw [hk, List.getD_cons_succ]
    congr 1
    omega

theorem stageB (w : ℕ) (P : List Bool) (v : Bool) (hP : P.length = w) (B : List Gate)
    (hB : ∀ g ∈ B, w ∉ g.inputs) :
    ∀ M : List Bool, ∀ i, i ≠ w →
      ((B.map (rg w)).foldl F (P ++ M)).getD (dl w i) false = (B.foldl F (P ++ v :: M)).getD i false := by
  induction B with
  | nil => intro M i hi; exact key P M v w hP i hi
  | cons g B ih =>
    intro M i hi
    simp only [List.map_cons, List.foldl_cons]
    have hg := hB g (by simp)
    have h1 : F (P ++ M) (rg w g) = P ++ (M ++ [g.op.eval (g.inputs.map fun i => (P ++ v :: M).getD i false)]) := by
      unfold F
      rw [F_rg (P ++ v :: M) (P ++ M) w g, List.append_assoc]
      intro i hi
      exact key P M v w hP i (fun h => hg (h ▸ hi))
    have h2 : F (P ++ v :: M) g = P ++ v :: (M ++ [g.op.eval (g.inputs.map fun i => (P ++ v :: M).getD i false)]) := by
      unfold F
      simp
    rw [h1, h2]
    exact ih (fun g' hg' => hB g' (by simp [hg'])) _ i hi

theorem del_getD (n j : ℕ) (gs : List Gate) (hj : j < gs.length)
    (hw : ∀ g ∈ gs, n + j ∉ g.inputs) (x : List Bool) (hx : x.length = n)
    (i : ℕ) (hi : i ≠ n + j) :
    (((gs.eraseIdx j).map (rg (n + j))).foldl F x).getD (dl (n + j) i) false
      = (gs.foldl F x).getD i false := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [List.drop_eq_getElem_cons hj]
  have herase : gs.eraseIdx j = gs.take j ++ gs.drop (j + 1) := List.eraseIdx_eq_take_drop_succ gs j
  rw [herase, List.map_append, List.foldl_append]
  conv_rhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [stageA (n + j) (gs.take j) (fun g hg => hw g (List.mem_of_mem_take hg)) x
    (by rw [hx, List.length_take]; omega)]
  have hP : (List.foldl F x (gs.take j)).length = n + j := by
    rw [fold_len, hx, List.length_take]; omega
  have := stageB (n + j) (List.foldl F x (gs.take j))
    (gs[j].op.eval (gs[j].inputs.map fun i => (List.foldl F x (gs.take j)).getD i false)) hP
    (gs.drop (j + 1)) (fun g hg => hw g (List.mem_of_mem_drop hg)) [] i hi
  simpa [F] using this

theorem indep (k : ℕ) (gs : List Gate) (hk : ∀ g ∈ gs, k ∉ g.inputs) :
    ∀ Q Q' : List Bool, Q.length = Q'.length → (∀ i, i ≠ k → Q.getD i false = Q'.getD i false) →
      ∀ i, i ≠ k → (gs.foldl F Q).getD i false = (gs.foldl F Q').getD i false := by
  induction gs with
  | nil => intro Q Q' _ h i hi; exact h i hi
  | cons g gs ih =>
    intro Q Q' hl h i hi
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hk g' (by simp [hg']))
    · simp [F, hl]
    · intro i' hi'
      have hv : g.op.eval (g.inputs.map fun i => Q.getD i false)
          = g.op.eval (g.inputs.map fun i => Q'.getD i false) := by
        apply congrArg
        apply List.map_congr_left
        intro j hj
        exact h j (fun e => hk g (by simp) (e ▸ hj))
      unfold F
      rw [hv]
      by_cases hlt : i' < Q.length
      · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
        exact h i' hi'
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    · exact hi

def RB (n : ℕ) (gs : List Gate) : Prop := ∀ p (hp : p < gs.length), ∀ i ∈ gs[p].inputs, i < n + p

theorem rb_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : RB n C.gates := by
  intro p hp i hi
  have hR := h.2.1 p hp i
  apply hR
  have : C.gates.getD p ⟨GateOp.or, []⟩ = C.gates[p] := List.getD_eq_getElem _ _ hp
  show i ∈ (C.gates.getD p ⟨GateOp.or, []⟩).inputs
  rw [this]; exact hi

theorem ao2_of (n : ℕ) (C : Circuit) (hA : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hR : RB n C.gates) (hL : ∀ g ∈ C.gates, g.inputs.length = 2) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨hA, ?_, hL⟩
  intro p hp i hi
  have : C.gates.getD p ⟨GateOp.or, []⟩ = C.gates[p] := List.getD_eq_getElem _ _ hp
  change i ∈ (C.gates.getD p ⟨GateOp.or, []⟩).inputs at hi
  rw [this] at hi
  exact hR p hp i hi

theorem rb_del (n j : ℕ) (gs : List Gate) (hj : j < gs.length) (hR : RB n gs)
    (hw : ∀ g ∈ gs, n + j ∉ g.inputs) : RB n ((gs.eraseIdx j).map (rg (n + j))) := by
  intro p hp i hi
  simp only [List.getElem_map, rg] at hi
  obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi
  rw [List.getElem_eraseIdx] at hi0
  have hlen : (gs.eraseIdx j).length = gs.length - 1 := List.length_eraseIdx_of_lt hj
  simp only [List.length_map] at hp
  split_ifs at hi0 with hpj
  · have := hR p (by omega) i0 hi0
    simp only [dl]
    split_ifs <;> omega
  · have := hR (p + 1) (by omega) i0 hi0
    have hne : i0 ≠ n + j := fun e => hw _ (List.getElem_mem _) (e ▸ hi0)
    simp only [dl]
    split_ifs <;> omega

theorem main (n : ℕ) : ∀ s (C : Circuit), C.gates.length = s → PEqualNP.TopForm.IsAO2 n C →
    (∀ x5 : Fin n, ∃ (x6 x7 : Fin n → Bool), (∀ x8, x8 ≠ x5 → x6 x8 = x7 x8) ∧
      PEqualNP.MetaComplexity.circuitFun n C x6 ≠ PEqualNP.MetaComplexity.circuitFun n C x7) →
    ∃ D : Circuit, D.size ≤ C.size ∧ PEqualNP.TopForm.IsAO2 n D ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧
      ∀ k < n + D.size, k ≠ D.output → k ∈ D.gates.flatMap Gate.inputs := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro C hs hao hrel
    by_cases hdel : ∃ j < C.gates.length, n + j ≠ C.output ∧ ∀ g ∈ C.gates, n + j ∉ g.inputs
    · obtain ⟨j, hj, ho, hw⟩ := hdel
      let C' : Circuit := ⟨(C.gates.eraseIdx j).map (rg (n + j)), dl (n + j) C.output⟩
      have hfun : PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.circuitFun n C := by
        funext x
        unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval
        rw [wires_eq, wires_eq]
        exact del_getD n j C.gates hj hw (List.ofFn x) (by simp) C.output (fun e => ho e.symm)
      have hao' : PEqualNP.TopForm.IsAO2 n C' := by
        apply ao2_of
        · intro g hg
          obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
          exact hao.1 g0 (List.mem_of_mem_eraseIdx hg0)
        · exact rb_del n j C.gates hj (rb_of n C hao) hw
        · intro g hg
          obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
          have := hao.2.2 g0 (List.mem_of_mem_eraseIdx hg0)
          simpa [rg] using this
      have hlen : C'.gates.length = s - 1 := by
        simp only [C', List.length_map, List.length_eraseIdx_of_lt hj, hs]
      obtain ⟨D, h1, h2, h3, h4⟩ := ih (s - 1) (by omega) C' hlen hao' (by
        intro x5
        obtain ⟨x6, x7, h, hne⟩ := hrel x5
        exact ⟨x6, x7, h, by rw [hfun]; exact hne⟩)
      refine ⟨D, ?_, h2, by rw [h3, hfun], h4⟩
      have : C'.size = s - 1 := hlen
      unfold Circuit.size at this h1 ⊢
      omega
    · refine ⟨C, le_refl _, hao, rfl, ?_⟩
      intro k hk hko
      by_contra hnot
      have hk' : ∀ g ∈ C.gates, k ∉ g.inputs := fun g hg hkg => hnot (List.mem_flatMap.2 ⟨g, hg, hkg⟩)
      by_cases hkn : k < n
      · obtain ⟨x6, x7, h, hne⟩ := hrel ⟨k, hkn⟩
        apply hne
        unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval
        rw [wires_eq, wires_eq]
        apply indep k C.gates hk' _ _ (by simp) _ C.output (Ne.symm hko)
        intro i hi
        by_cases hin : i < n
        · rw [List.getD_eq_getElem _ _ (by simpa using hin), List.getD_eq_getElem _ _ (by simpa using hin),
            List.getElem_ofFn, List.getElem_ofFn]
          exact h ⟨i, hin⟩ (fun e => hi (congrArg Fin.val e))
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      · apply hdel
        refine ⟨k - n, ?_, ?_, ?_⟩
        · unfold Circuit.size at hk
          omega
        · rw [show n + (k - n) = k by omega]
          exact hko
        · rw [show n + (k - n) = k by omega]
          exact hk'

theorem relevant (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1))
    (hm : ∀ a : Fin x1, (a, x3 a) ∈ x2) (f : (Fin (x1 + x1) → Bool) → Bool)
    (hf : ∀ z, f z = decide (∃ (a b : Fin x1), (a, b) ∈ x2 ∧ z (Fin.castAdd x1 a) = true ∧
      z (Fin.natAdd x1 b) = true)) :
    ∀ k : Fin (x1 + x1), ∃ (x6 x7 : Fin (x1 + x1) → Bool), (∀ x8, x8 ≠ k → x6 x8 = x7 x8) ∧
      f x6 ≠ f x7 := by
  intro k
  by_cases hk : k.val < x1
  · let a : Fin x1 := ⟨k.val, hk⟩
    refine ⟨fun z => decide (z = Fin.castAdd x1 a ∨ z = Fin.natAdd x1 (x3 a)),
      fun z => decide (z = Fin.natAdd x1 (x3 a)), ?_, ?_⟩
    · intro z hz
      have : z ≠ Fin.castAdd x1 a := by
        intro e; apply hz; rw [e]; ext; simp [a]
      simp [this]
    · rw [hf, hf]
      have e1 : (∃ (a' b : Fin x1), (a', b) ∈ x2 ∧
          decide (Fin.castAdd x1 a' = Fin.castAdd x1 a ∨ Fin.castAdd x1 a' = Fin.natAdd x1 (x3 a)) = true ∧
          decide (Fin.natAdd x1 b = Fin.castAdd x1 a ∨ Fin.natAdd x1 b = Fin.natAdd x1 (x3 a)) = true) :=
        ⟨a, x3 a, hm a, by simp, by simp⟩
      have e2 : ¬ (∃ (a' b : Fin x1), (a', b) ∈ x2 ∧
          decide (Fin.castAdd x1 a' = Fin.natAdd x1 (x3 a)) = true ∧
          decide (Fin.natAdd x1 b = Fin.natAdd x1 (x3 a)) = true) := by
        rintro ⟨a', b, _, h1, _⟩
        simp only [decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at h1
        omega
      simp only [decide_eq_true_iff.mpr e1, decide_eq_false e2]
      decide
  · let b : Fin x1 := ⟨k.val - x1, by omega⟩
    refine ⟨fun z => decide (z = Fin.castAdd x1 (x3.symm b) ∨ z = Fin.natAdd x1 b),
      fun z => decide (z = Fin.castAdd x1 (x3.symm b)), ?_, ?_⟩
    · intro z hz
      have : z ≠ Fin.natAdd x1 b := by
        intro e; apply hz; rw [e]; ext; simp [b]; omega
      show decide (z = _ ∨ z = Fin.natAdd x1 b) = decide (z = _)
      simp only [this, or_false]
    · rw [hf, hf]
      have e1 : (∃ (a' b' : Fin x1), (a', b') ∈ x2 ∧
          decide (Fin.castAdd x1 a' = Fin.castAdd x1 (x3.symm b) ∨ Fin.castAdd x1 a' = Fin.natAdd x1 b) = true ∧
          decide (Fin.natAdd x1 b' = Fin.castAdd x1 (x3.symm b) ∨ Fin.natAdd x1 b' = Fin.natAdd x1 b) = true) :=
        ⟨x3.symm b, b, by simpa using hm (x3.symm b), by simp, by simp⟩
      have e2 : ¬ (∃ (a' b' : Fin x1), (a', b') ∈ x2 ∧
          decide (Fin.castAdd x1 a' = Fin.castAdd x1 (x3.symm b)) = true ∧
          decide (Fin.natAdd x1 b' = Fin.castAdd x1 (x3.symm b)) = true) := by
        rintro ⟨a', b', _, _, h2⟩
        simp only [decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at h2
        omega
      simp only [decide_eq_true_iff.mpr e1, decide_eq_false e2]
      decide

end PEqualNP.Outside.L_meta_8813

theorem PEqualNP.Outside.L_meta_8813 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x1 → (∀ (x6 : Fin x1), (x6, x3 x6) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x8 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1), (x9, x10) ∈ x2 ∧ x8 (Fin.castAdd x1 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x9.size ≤ x4.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x1) x9 ∧ (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x9 x10 = PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10) ∧ (x9.output :: List.flatMap (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => x10.inputs) x9.gates).toFinset.card = (2 : ℕ) * x1 + x9.size := by
  intro x1 x2 x3 C hpos hm hao hf
  have hrel := PEqualNP.Outside.L_meta_8813.relevant x1 x2 x3 hm _ hf
  obtain ⟨D, h1, h2, h3, h4⟩ := PEqualNP.Outside.L_meta_8813.main (x1 + x1) C.gates.length C rfl hao hrel
  refine ⟨D, h1, h2, fun z => by rw [h3], ?_⟩
  -- the output is a wire: otherwise the function would be constantly false
  have hout : D.output < x1 + x1 + D.size := by
    by_contra hno
    obtain ⟨x6, x7, _, hne⟩ := hrel ⟨0, by omega⟩
    apply hne
    rw [← h3]
    unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [PEqualNP.Outside.L_meta_8813.wires_eq, PEqualNP.Outside.L_meta_8813.wires_eq]
    rw [List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_8813.fold_len]; simp; unfold PEqualNP.CircuitLowerBounds.Circuit.size at hno; omega),
      List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_8813.fold_len]; simp; unfold PEqualNP.CircuitLowerBounds.Circuit.size at hno; omega)]
  have hrb := PEqualNP.Outside.L_meta_8813.rb_of _ D h2
  have heq : (D.output :: List.flatMap (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.inputs) D.gates).toFinset
      = Finset.range (x1 + x1 + D.size) := by
    ext k
    simp only [List.mem_toFinset, List.mem_cons, Finset.mem_range]
    constructor
    · rintro (rfl | hk)
      · exact hout
      · obtain ⟨g, hg, hkg⟩ := List.mem_flatMap.1 hk
        obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hg
        have := hrb p hp k hkg
        unfold PEqualNP.CircuitLowerBounds.Circuit.size
        omega
    · intro hk
      by_cases hko : k = D.output
      · exact Or.inl hko
      · exact Or.inr (h4 k hk hko)
  rw [heq, Finset.card_range]
  omega
