import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1945

open PEqualNP.CircuitLowerBounds

theorem le_foldr_max (l : List ℕ) : ∀ x ∈ l, x ≤ l.foldr max 0 := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons a t ih =>
    intro x hx
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih x h) (le_max_right _ _)

theorem gate_ge (g : Gate) (d : List ℕ) (i : ℕ) (hi : i ∈ g.inputs) :
    d.getD i 0 ≤ g.lineDegree d := by
  unfold Gate.lineDegree
  split_ifs
  · exact List.le_sum_of_mem (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · exact le_foldr_max _ _ (List.mem_map.mpr ⟨i, hi, rfl⟩)

theorem getD_snoc_lt {α : Type} (l : List α) (a d : α) (i : ℕ) (h : i < l.length) :
    (l ++ [a]).getD i d = l.getD i d := List.getD_append _ _ _ _ h

theorem getD_snoc_eq {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp

theorem getD_snoc_gt {α : Type} (l : List α) (a d : α) (i : ℕ) (h : l.length < i) :
    (l ++ [a]).getD i d = d := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  obtain ⟨k, hk⟩ : ∃ k, i - l.length = k + 1 := ⟨i - l.length - 1, by omega⟩
  rw [hk]; simp

theorem fold_dep (gs : List Gate) : ∀ (d : List ℕ) (w w2 : List Bool), d.length = w.length →
    w.length = w2.length →
    (∀ i, d.getD i 0 = 0 → w.getD i false = w2.getD i false) →
    ∀ i, (gs.foldl (fun d g => d ++ [g.lineDegree d]) d).getD i 0 = 0 →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD i false := by
  induction gs with
  | nil => intro d w w2 _ _ h i hi; exact h i hi
  | cons g t ih =>
    intro d w w2 h1 h2 h i hi
    simp only [List.foldl_cons] at hi ⊢
    refine ih _ _ _ (by simp [h1]) (by simp [h2]) ?_ i hi
    intro k hk
    rcases lt_trichotomy k d.length with h3 | h3 | h3
    · rw [getD_snoc_lt d _ 0 k h3] at hk
      rw [getD_snoc_lt w _ false k (by omega), getD_snoc_lt w2 _ false k (by omega)]
      exact h k hk
    · subst h3
      rw [getD_snoc_eq] at hk
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro j hj
      apply h
      have := gate_ge g d j hj
      omega
    · rw [getD_snoc_gt w _ false k (by omega), getD_snoc_gt w2 _ false k (by omega)]

theorem fold_pos2 (gs : List Gate) : ∀ (k : ℕ) (dP dL : List ℕ), dP.length = k → dL.length = k →
    (∀ i < k, 0 < dP.getD i 0 ∨ 0 < dL.getD i 0) →
    (∀ j < gs.length, ∃ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < k + j) →
    ∀ i < k + gs.length, 0 < (gs.foldl (fun d g => d ++ [g.lineDegree d]) dP).getD i 0 ∨
      0 < (gs.foldl (fun d g => d ++ [g.lineDegree d]) dL).getD i 0 := by
  induction gs with
  | nil => intro k dP dL _ _ h _ i hi; exact h i (by simpa using hi)
  | cons g t ih =>
    intro k dP dL hP hL h hr i hi
    simp only [List.foldl_cons]
    have hr0 := hr 0 (by simp)
    obtain ⟨a, ha, hak⟩ := hr0
    simp only [List.getD_cons_zero] at ha
    refine ih (k + 1) _ _ (by simp [hP]) (by simp [hL]) ?_ ?_ i (by simp at hi; omega)
    · intro i2 hi2
      rcases Nat.lt_or_ge i2 k with h3 | h3
      · rw [getD_snoc_lt dP _ 0 i2 (by omega), getD_snoc_lt dL _ 0 i2 (by omega)]
        exact h i2 h3
      · have h4 : i2 = k := by omega
        subst h4
        have e1 : (dP ++ [g.lineDegree dP]).getD i2 0 = g.lineDegree dP := by
          rw [← hP]; exact getD_snoc_eq _ _ _
        have e2 : (dL ++ [g.lineDegree dL]).getD i2 0 = g.lineDegree dL := by
          rw [← hL]; exact getD_snoc_eq _ _ _
        rw [e1, e2]
        rcases h a (by omega) with h5 | h5
        · left; exact lt_of_lt_of_le h5 (gate_ge g dP a ha)
        · right; exact lt_of_lt_of_le h5 (gate_ge g dL a ha)
    · intro j hj
      obtain ⟨b, hb, hbk⟩ := hr (j + 1) (by simp; omega)
      refine ⟨b, ?_, by omega⟩
      simpa using hb

theorem init_one (n : ℕ) (M : Finset ℕ) (i : ℕ) (hi : i < n) (hm : i ∈ M) :
    ((List.range n).map fun i => if i ∈ M then 1 else 0).getD i 0 = 1 := by
  simp [List.getD_eq_getElem?_getD, hi, hm]

theorem deg_pos (N : ℕ) (C : Circuit)
    (hC : (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C) :
    ∀ j < C.gates.length, 0 < (C.lineDegrees (N + N) (Finset.range N)).getD (N + N + j) 0 ∨
      0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (N + N + j) 0 := by
  intro j hj
  have hinit : ∀ i < N + N,
      0 < ((List.range (N + N)).map fun i => if i ∈ Finset.range N then 1 else 0).getD i 0 ∨
      0 < ((List.range (N + N)).map fun i => if i ∈ Finset.Ico N (N + N) then 1 else 0).getD i 0 := by
    intro i hi
    by_cases h : i < N
    · left; rw [init_one _ _ _ hi (by simpa using h)]; omega
    · right; rw [init_one _ _ _ hi (by simp; omega)]; omega
  have hread : ∀ j2 < C.gates.length,
      ∃ i ∈ (C.gates.getD j2 ⟨GateOp.or, []⟩).inputs, i < N + N + j2 := by
    intro j2 hj2
    have hmem : C.gates.getD j2 ⟨GateOp.or, []⟩ ∈ C.gates := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2]
    have h2 := (hC.1 _ hmem).2
    obtain ⟨a, ha⟩ := List.exists_mem_of_length_pos (l := (C.gates.getD j2 ⟨GateOp.or, []⟩).inputs) (by omega)
    exact ⟨a, ha, hC.2 j2 hj2 a ha⟩
  exact fold_pos2 C.gates (N + N) _ _ (by simp) (by simp) hinit hread (N + N + j) (by omega)

theorem ofFn_getD_eq (n : ℕ) (x y : Fin n → Bool) (i : ℕ) (h : ∀ hi : i < n, x ⟨i, hi⟩ = y ⟨i, hi⟩) :
    (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
  by_cases hi : i < n
  · simp [List.getD_eq_getElem?_getD, hi, h hi]
  · simp [List.getD_eq_getElem?_getD, hi]

theorem eval_eq_of_deg0 (N : ℕ) (C : Circuit) (M : Finset ℕ) (x y : Fin (N + N) → Bool)
    (hM : ∀ i : Fin (N + N), i.val ∉ M → x i = y i)
    (h0 : (C.lineDegrees (N + N) M).getD C.output 0 = 0) :
    PEqualNP.MetaComplexity.circuitFun (N + N) C x = PEqualNP.MetaComplexity.circuitFun (N + N) C y := by
  unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval Circuit.wires
  apply fold_dep C.gates ((List.range (N + N)).map fun i => if i ∈ M then 1 else 0) _ _
    (by simp) (by simp) _ C.output h0
  intro i hi0
  apply ofFn_getD_eq
  intro hi
  apply hM
  intro hm
  rw [init_one _ _ _ hi hm] at hi0
  exact one_ne_zero hi0

theorem append_right_val (N : ℕ) (a b : Fin N → Bool) (i : ℕ) (hi : i < N + N) (h : N ≤ i) :
    Fin.append a b ⟨i, hi⟩ = b ⟨i - N, by omega⟩ := by
  have : (⟨i, hi⟩ : Fin (N + N)) = Fin.natAdd N ⟨i - N, by omega⟩ := by ext; simp; omega
  rw [this, Fin.append_right]

theorem append_left_val (N : ℕ) (a b : Fin N → Bool) (i : ℕ) (hi : i < N + N) (h : i < N) :
    Fin.append a b ⟨i, hi⟩ = a ⟨i, h⟩ := by
  have : (⟨i, hi⟩ : Fin (N + N)) = Fin.castAdd N ⟨i, h⟩ := rfl
  rw [this, Fin.append_left]

theorem count3 (len : ℕ) (P L : ℕ → ℕ) (hpos : ∀ j < len, 0 < P j ∨ 0 < L j) :
    Set.ncard {j | j < len ∧ P j = 0} + Set.ncard {j | j < len ∧ L j = 0} +
      Set.ncard {j | j < len ∧ 0 < P j ∧ 0 < L j} ≤ len := by
  have e1 : {j | j < len ∧ P j = 0} = ↑((Finset.range len).filter (fun j => P j = 0)) := by
    ext j; simp
  have e2 : {j | j < len ∧ L j = 0} = ↑((Finset.range len).filter (fun j => L j = 0)) := by
    ext j; simp
  have e3 : {j | j < len ∧ 0 < P j ∧ 0 < L j} =
      ↑((Finset.range len).filter (fun j => 0 < P j ∧ 0 < L j)) := by
    ext j; simp
  rw [e1, e2, e3, Set.ncard_coe_finset, Set.ncard_coe_finset, Set.ncard_coe_finset]
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  calc _ ≤ ∑ j ∈ Finset.range len, 1 := Finset.sum_le_sum (fun j hj => by
          have := hpos j (Finset.mem_range.mp hj)
          split_ifs <;> omega)
    _ = len := by simp

theorem sum_ncard_eq {N : ℕ} (S W : Finset (Fin N)) (P : Fin N → Fin N → Prop)
    (Q : Fin N → Fin N → Bool) (h : ∀ w ∈ W, ∀ u, P w u ↔ Q w u = true) :
    ∑ w ∈ W, Set.ncard {u | u ∈ S ∧ P w u} = ∑ w ∈ W, (S.filter (fun u => Q w u = true)).card := by
  apply Finset.sum_congr rfl
  intro w hw
  rw [← Set.ncard_coe_finset]
  congr 1
  ext u
  simp [h w hw u]

theorem arith (R D q INC Wc pf lf mix sz size S1 mx : ℕ) (hB : D * INC ≤ mx * pf + D * S1)
    (hC : R * S1 ≤ R * Wc + q * sz) (hsz : sz ≤ lf + 3 * mix) (hc : pf + lf + mix ≤ size) :
    R * D * INC ≤ R * D * Wc + max (R * mx) (3 * q * D) * size := by
  have e1 : R * (D * INC) ≤ R * (mx * pf + D * S1) := Nat.mul_le_mul_left R hB
  have e2 : D * (R * S1) ≤ D * (R * Wc + q * sz) := Nat.mul_le_mul_left D hC
  have e3 : D * q * sz ≤ D * q * (lf + 3 * mix) := Nat.mul_le_mul_left _ hsz
  have e4 : R * mx ≤ max (R * mx) (3 * q * D) := le_max_left _ _
  have e5 : 3 * q * D ≤ max (R * mx) (3 * q * D) := le_max_right _ _
  have e5b : D * q ≤ max (R * mx) (3 * q * D) := le_trans (by nlinarith) e5
  have e6 : R * mx * pf ≤ max (R * mx) (3 * q * D) * pf := Nat.mul_le_mul_right _ e4
  have e7 : D * q * lf ≤ max (R * mx) (3 * q * D) * lf := Nat.mul_le_mul_right _ e5b
  have e8 : 3 * q * D * mix ≤ max (R * mx) (3 * q * D) * mix := Nat.mul_le_mul_right _ e5
  have e9 : max (R * mx) (3 * q * D) * (pf + lf + mix) ≤ max (R * mx) (3 * q * D) * size :=
    Nat.mul_le_mul_left _ hc
  nlinarith [e1, e2, e3, e6, e7, e8, e9]

end PEqualNP.Outside.L_meta_1945

theorem PEqualNP.Outside.L_meta_1945 : (∀ (Nlv17a Rlv17a : ℕ) (Ilv17a : Fin Nlv17a → Fin Nlv17a → Prop) [DecidableRel Ilv17a] (Clv17a Corlv17a : PEqualNP.CircuitLowerBounds.Circuit) (Vlv17a : (ℕ → Fin 2) → PEqualNP.CircuitLowerBounds.Circuit) (Slv17a Wlv17a : Finset (Fin Nlv17a)), ((∀ glv17ax2 ∈ Clv17a.gates, (glv17ax2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17ax2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17ax2.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv17a + Nlv17a) Clv17a) → (0 < Clv17a.gates.length ∧ (∀ jlv17ax11 < Clv17a.gates.length, ∀ ilv17ax4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax11).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.image (fun plv17ax6 : Fin Nlv17a => (plv17ax6 : ℕ)) (Slv17a)ᶜ ∪ Finset.image (fun llv17ax4 : Fin Nlv17a => Nlv17a + (llv17ax4 : ℕ)) (Wlv17a)ᶜ)).getD ilv17ax4 0 = 0) ∧ (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.image (fun plv17ax7 : Fin Nlv17a => (plv17ax7 : ℕ)) (Slv17a)ᶜ ∪ Finset.image (fun llv17ax5 : Fin Nlv17a => Nlv17a + (llv17ax5 : ℕ)) (Wlv17a)ᶜ)).getD Clv17a.output 0 = 0) → Corlv17a = (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv17ax12 : Fin Clv17a.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17ax5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD ilv17ax5 0 = 0) ∨ (∀ hlv17ax3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax3 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val).inputs) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val))) Clv17a.output) → Vlv17a = (fun sglv17ax3 : ℕ → Fin 2 => (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv17ax13 : Fin Clv17a.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17ax6 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD ilv17ax6 0 = 0) ∨ (∀ hlv17ax4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax4 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).inputs.getD (sglv17ax3 jlv17ax13.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).inputs.getD (sglv17ax3 jlv17ax13.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val))) Clv17a.output)) → ((∀ sglv17a : ℕ → Fin 2, ∀ wlv17ax1 ∈ Wlv17a, ∀ Xlv17ax1 : Finset (Fin Nlv17a), Xlv17ax1 ⊆ Slv17a → (∀ plv17ax1 ∈ Xlv17ax1, ¬ Ilv17a plv17ax1 wlv17ax1) → Xlv17ax1.card ≤ Rlv17a → PEqualNP.MetaComplexity.circuitFun (Nlv17a + Nlv17a) (Vlv17a sglv17a) (Fin.append (fun plv17ax2 : Fin Nlv17a => decide (plv17ax2 ∈ Xlv17ax1)) (fun llv17a : Fin Nlv17a => decide (llv17a ∈ ({wlv17ax1} : Finset (Fin Nlv17a))))) = false) → ∀ wlv17a ∈ Wlv17a, ∀ Xlv17a : Finset (Fin Nlv17a), Xlv17a ⊆ Slv17a → (∀ plv17a ∈ Xlv17a, ¬ Ilv17a plv17a wlv17a) → Xlv17a.card ≤ Rlv17a → ¬ (∃ hlv17a : ℕ, ((Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17a 0 = 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD hlv17a 0 ∧ ∃ jlv17a < Corlv17a.gates.length, hlv17a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17a).inputs ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17a) 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17a) 0)) ∧ (Wlv17a.filter (fun llv17ax1 : Fin Nlv17a => (Clv17a.wires (List.ofFn (Fin.append (fun ulv17a : Fin Nlv17a => false) (fun alv17ax1 : Fin Nlv17a => decide (alv17ax1 = llv17ax1))))).getD hlv17a false = true)) = ({wlv17a} : Finset (Fin Nlv17a)) ∧ (Relation.ReflTransGen (fun alv17ax2 blv17a : ℕ => ∃ jlv17ax1 < Corlv17a.gates.length, blv17a = Nlv17a + Nlv17a + jlv17ax1 ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17a 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17a 0) ∧ alv17ax2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax1).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax1).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax1).inputs, ilv17a ≠ alv17ax2 → (Corlv17a.wires (List.ofFn (Fin.append (fun alv17a : Fin Nlv17a => decide (alv17a ∈ Xlv17a)) (fun ulv17ax1 : Fin Nlv17a => false)))).getD ilv17a false = true)) hlv17a Corlv17a.output))) ∧ (∀ (sglv17ax1 : ℕ → Fin 2) (glv17a hlv17ax1 : ℕ) (xlv17a : Fin Nlv17a → Bool), (((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD glv17a 0 = 0 ∧ 0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD glv17a 0 ∧ ∃ jlv17ax2 < (Vlv17a sglv17ax1).gates.length, glv17a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax2).inputs ∧ (0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17ax2) 0 ∧ 0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax2) 0)) → (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax1 0 = 0 → (Relation.ReflTransGen (fun alv17ax3 blv17ax1 : ℕ => ∃ jlv17ax3 < (Vlv17a sglv17ax1).gates.length, blv17ax1 = Nlv17a + Nlv17a + jlv17ax3 ∧ alv17ax3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax3).inputs ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax3).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17ax1 0 ∧ 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17ax1 0) hlv17ax1 glv17a) → ((Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax1 0 = 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD hlv17ax1 0 ∧ ∃ jlv17ax4 < Corlv17a.gates.length, hlv17ax1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax4).inputs ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17ax4) 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax4) 0)) ∧ ((Relation.ReflTransGen (fun alv17ax4 blv17ax2 : ℕ => ∃ jlv17ax5 < (Vlv17a sglv17ax1).gates.length, blv17ax2 = Nlv17a + Nlv17a + jlv17ax5 ∧ (0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17ax2 0 ∧ 0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17ax2 0) ∧ alv17ax4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax5).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax5).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17ax1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax5).inputs, ilv17ax1 ≠ alv17ax4 → ((Vlv17a sglv17ax1).wires (List.ofFn (Fin.append xlv17a (fun ulv17ax2 : Fin Nlv17a => false)))).getD ilv17ax1 false = true)) glv17a (Vlv17a sglv17ax1).output) → (Relation.ReflTransGen (fun alv17ax5 blv17ax3 : ℕ => ∃ jlv17ax6 < Corlv17a.gates.length, blv17ax3 = Nlv17a + Nlv17a + jlv17ax6 ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17ax3 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17ax3 0) ∧ alv17ax5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax6).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax6).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17ax2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax6).inputs, ilv17ax2 ≠ alv17ax5 → (Corlv17a.wires (List.ofFn (Fin.append xlv17a (fun ulv17ax3 : Fin Nlv17a => false)))).getD ilv17ax2 false = true)) hlv17ax1 Corlv17a.output))) ∧ ((∀ sglv17ax2 : ℕ → Fin 2, ∀ wlv17ax4 ∈ Wlv17a, ∀ Xlv17ax2 : Finset (Fin Nlv17a), Xlv17ax2 ⊆ Slv17a → (∀ plv17ax4 ∈ Xlv17ax2, ¬ Ilv17a plv17ax4 wlv17ax4) → Xlv17ax2.card ≤ Rlv17a → PEqualNP.MetaComplexity.circuitFun (Nlv17a + Nlv17a) (Vlv17a sglv17ax2) (Fin.append (fun plv17ax5 : Fin Nlv17a => decide (plv17ax5 ∈ Xlv17ax2)) (fun llv17ax2 : Fin Nlv17a => decide (llv17ax2 ∈ ({wlv17ax4} : Finset (Fin Nlv17a))))) = false) → 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD Clv17a.output 0 → 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD Clv17a.output 0 → ∃ (Xclv17a : PEqualNP.CircuitLowerBounds.Circuit) (pslv17a : Fin Nlv17a → ℕ), ((∀ glv17ax1 ∈ Xclv17a.gates, (glv17ax1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17ax1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17ax1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack Nlv17a Xclv17a) ∧ Xclv17a.size ≤ Set.ncard {jlv17ax7 : ℕ | jlv17ax7 < Clv17a.gates.length ∧ (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax7) 0 = 0} + 3 * Set.ncard {jlv17ax8 : ℕ | jlv17ax8 < Clv17a.gates.length ∧ 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17ax8) 0 ∧ 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax8) 0} ∧ (∀ (wlv17ax2 : Fin Nlv17a) (xlv17ax1 xlv17ax2 : Fin Nlv17a → Bool), (∀ plv17ax3 ∈ Slv17a, xlv17ax1 plv17ax3 = xlv17ax2 plv17ax3) → (Xclv17a.wires (List.ofFn xlv17ax1)).getD (pslv17a wlv17ax2) false = (Xclv17a.wires (List.ofFn xlv17ax2)).getD (pslv17a wlv17ax2) false) ∧ ∀ wlv17ax3 ∈ Wlv17a, ∀ xlv17ax3 : Fin Nlv17a → Bool, ((Xclv17a.wires (List.ofFn xlv17ax3)).getD (pslv17a wlv17ax3) false = true ↔ (∃ hlv17ax2 : ℕ, ((Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax2 0 = 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD hlv17ax2 0 ∧ ∃ jlv17ax9 < Corlv17a.gates.length, hlv17ax2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax9).inputs ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17ax9) 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax9) 0)) ∧ (Wlv17a.filter (fun llv17ax3 : Fin Nlv17a => (Clv17a.wires (List.ofFn (Fin.append (fun ulv17ax4 : Fin Nlv17a => false) (fun alv17ax6 : Fin Nlv17a => decide (alv17ax6 = llv17ax3))))).getD hlv17ax2 false = true)) = ({wlv17ax3} : Finset (Fin Nlv17a)) ∧ (Relation.ReflTransGen (fun alv17ax7 blv17ax4 : ℕ => ∃ jlv17ax10 < Corlv17a.gates.length, blv17ax4 = Nlv17a + Nlv17a + jlv17ax10 ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17ax4 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17ax4 0) ∧ alv17ax7 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax10).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17ax3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax10).inputs, ilv17ax3 ≠ alv17ax7 → (Corlv17a.wires (List.ofFn (Fin.append xlv17ax3 (fun ulv17ax5 : Fin Nlv17a => false)))).getD ilv17ax3 false = true)) hlv17ax2 Corlv17a.output))))) → (∀ (qlv17b Nlv17b Klv17b mlv17b Dlv17b : ℕ) (Ilv17b : Fin Nlv17b → Fin Nlv17b → Prop) [DecidableRel Ilv17b] (Clv17b Corlv17b : PEqualNP.CircuitLowerBounds.Circuit) (Slv17b Wlv17b : Finset (Fin Nlv17b)), 2 ≤ qlv17b → Nlv17b = qlv17b ^ 2 + qlv17b + 1 → (∀ llv17b : Fin Nlv17b, (Finset.univ.filter (fun plv17b => Ilv17b plv17b llv17b)).card = qlv17b + 1) → (∀ palv17b pblv17b : Fin Nlv17b, palv17b ≠ pblv17b → ∃! lblv17b : Fin Nlv17b, Ilv17b palv17b lblv17b ∧ Ilv17b pblv17b lblv17b) → ((∀ glv17b ∈ Clv17b.gates, (glv17b.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17b.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17b.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv17b + Nlv17b) Clv17b) → Corlv17b = (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv17b : Fin Clv17b.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17b.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17b.val).inputs, (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.Ico Nlv17b (Nlv17b + Nlv17b))).getD ilv17b 0 = 0) ∨ (∀ hlv17b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17b.val).inputs, (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD hlv17b 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17b.val).inputs) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17b.val))) Clv17b.output) → Set.ncard {jlv17bx1 : ℕ | jlv17bx1 < Clv17b.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17bx1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17bx1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17bx1).inputs, (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.Ico Nlv17b (Nlv17b + Nlv17b))).getD ilv17bx1 0 = 0) ∨ (∀ hlv17bx1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17bx1).inputs, (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD hlv17bx1 0 = 0))} ≤ mlv17b → ((0 < Clv17b.gates.length ∧ (∀ jlv17bx2 < Clv17b.gates.length, ∀ ilv17bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17bx2).inputs, (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.image (fun plv17bx3 : Fin Nlv17b => (plv17bx3 : ℕ)) (Slv17b)ᶜ ∪ Finset.image (fun llv17bx3 : Fin Nlv17b => Nlv17b + (llv17bx3 : ℕ)) (Wlv17b)ᶜ)).getD ilv17bx2 0 = 0) ∧ (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.image (fun plv17bx4 : Fin Nlv17b => (plv17bx4 : ℕ)) (Slv17b)ᶜ ∪ Finset.image (fun llv17bx4 : Fin Nlv17b => Nlv17b + (llv17bx4 : ℕ)) (Wlv17b)ᶜ)).getD Clv17b.output 0 = 0) ∧ (∀ plv17bx1 ∈ Slv17b, ∀ llv17bx1 ∈ Wlv17b, Ilv17b plv17bx1 llv17bx1 → PEqualNP.MetaComplexity.circuitFun (Nlv17b + Nlv17b) Clv17b (Fin.append (fun plv17bx5 : Fin Nlv17b => decide (plv17bx5 ∈ ({plv17bx1} : Finset (Fin Nlv17b)))) (fun llv17bx5 : Fin Nlv17b => decide (llv17bx5 ∈ ({llv17bx1} : Finset (Fin Nlv17b))))) = true) ∧ (∀ Xlv17b Ylv17b : Finset (Fin Nlv17b), Xlv17b ⊆ Slv17b → Ylv17b ⊆ Wlv17b → Ylv17b.card ≤ Klv17b → (∀ plv17bx2 ∈ Xlv17b, ∀ llv17bx2 ∈ Ylv17b, ¬ Ilv17b plv17bx2 llv17bx2) → PEqualNP.MetaComplexity.circuitFun (Nlv17b + Nlv17b) Clv17b (Fin.append (fun plv17bx6 : Fin Nlv17b => decide (plv17bx6 ∈ Xlv17b)) (fun llv17bx6 : Fin Nlv17b => decide (llv17bx6 ∈ Ylv17b))) = false)) → 2 ^ mlv17b + Dlv17b = Klv17b + 1 → 1 ≤ Dlv17b → Dlv17b * ((Slv17b ×ˢ Wlv17b).filter (fun pllv17b => Ilv17b pllv17b.1 pllv17b.2)).card ≤ max (2 * Dlv17b) (qlv17b + 1) * Set.ncard {jlv17bx3 : ℕ | jlv17bx3 < Clv17b.gates.length ∧ (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD (Nlv17b + Nlv17b + jlv17bx3) 0 = 0} + Dlv17b * ∑ wlv17b ∈ Wlv17b, Set.ncard {ulv17b : Fin Nlv17b | ulv17b ∈ Slv17b ∧ (∃ hlv17bx2 : ℕ, ((Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD hlv17bx2 0 = 0 ∧ 0 < (Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.Ico Nlv17b (Nlv17b + Nlv17b))).getD hlv17bx2 0 ∧ ∃ jlv17bx4 < Corlv17b.gates.length, hlv17bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17b jlv17bx4).inputs ∧ (0 < (Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD (Nlv17b + Nlv17b + jlv17bx4) 0 ∧ 0 < (Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.Ico Nlv17b (Nlv17b + Nlv17b))).getD (Nlv17b + Nlv17b + jlv17bx4) 0)) ∧ (Wlv17b.filter (fun llv17bx7 : Fin Nlv17b => (Clv17b.wires (List.ofFn (Fin.append (fun ulv17bx1 : Fin Nlv17b => false) (fun alv17bx1 : Fin Nlv17b => decide (alv17bx1 = llv17bx7))))).getD hlv17bx2 false = true)) = ({wlv17b} : Finset (Fin Nlv17b)) ∧ (Relation.ReflTransGen (fun alv17bx2 blv17b : ℕ => ∃ jlv17bx5 < Corlv17b.gates.length, blv17b = Nlv17b + Nlv17b + jlv17bx5 ∧ (0 < (Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD blv17b 0 ∧ 0 < (Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.Ico Nlv17b (Nlv17b + Nlv17b))).getD blv17b 0) ∧ alv17bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17b jlv17bx5).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17b jlv17bx5).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17bx3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17b jlv17bx5).inputs, ilv17bx3 ≠ alv17bx2 → (Corlv17b.wires (List.ofFn (Fin.append (fun alv17b : Fin Nlv17b => decide (alv17b = ulv17b)) (fun ulv17bx2 : Fin Nlv17b => false)))).getD ilv17bx3 false = true)) hlv17bx2 Corlv17b.output))}) → (∀ (qlv17c Nlv17c Rlv17c : ℕ) (Ilv17c : Fin Nlv17c → Fin Nlv17c → Prop) [DecidableRel Ilv17c] (Xlv17c : PEqualNP.CircuitLowerBounds.Circuit) (pslv17c : Fin Nlv17c → ℕ) (Slv17c Wlv17c : Finset (Fin Nlv17c)), 2 ≤ qlv17c → Nlv17c = qlv17c ^ 2 + qlv17c + 1 → (∀ llv17c : Fin Nlv17c, (Finset.univ.filter (fun plv17cx2 => Ilv17c plv17cx2 llv17c)).card = qlv17c + 1) → (∀ palv17c pblv17c : Fin Nlv17c, palv17c ≠ pblv17c → ∃! lblv17c : Fin Nlv17c, Ilv17c palv17c lblv17c ∧ Ilv17c pblv17c lblv17c) → 1 ≤ Rlv17c → Rlv17c ≤ qlv17c → ((∀ glv17c ∈ Xlv17c.gates, (glv17c.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17c.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17c.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack Nlv17c Xlv17c) → (∀ (wlv17c : Fin Nlv17c) (xlv17c xlv17cx1 : Fin Nlv17c → Bool), (∀ plv17c ∈ Slv17c, xlv17c plv17c = xlv17cx1 plv17c) → (Xlv17c.wires (List.ofFn xlv17c)).getD (pslv17c wlv17c) false = (Xlv17c.wires (List.ofFn xlv17cx1)).getD (pslv17c wlv17c) false) → (∀ wlv17cx1 ∈ Wlv17c, ∀ Xslv17c : Finset (Fin Nlv17c), Xslv17c ⊆ Slv17c → (∀ plv17cx1 ∈ Xslv17c, ¬ Ilv17c plv17cx1 wlv17cx1) → Xslv17c.card ≤ Rlv17c → (Xlv17c.wires (List.ofFn (fun alv17c : Fin Nlv17c => decide (alv17c ∈ Xslv17c)))).getD (pslv17c wlv17cx1) false = false) → Rlv17c * ∑ wlv17cx2 ∈ Wlv17c, (Slv17c.filter (fun ulv17c : Fin Nlv17c => (Xlv17c.wires (List.ofFn (fun alv17cx1 : Fin Nlv17c => decide (alv17cx1 = ulv17c)))).getD (pslv17c wlv17cx2) false = true)).card ≤ Rlv17c * Wlv17c.card + qlv17c * Xlv17c.size) → ∀ (qlv17 Nlv17 Klv17 mlv17 Rlv17 Dlv17 : ℕ) (Ilv17 : Fin Nlv17 → Fin Nlv17 → Prop) [DecidableRel Ilv17] (Clv17 : PEqualNP.CircuitLowerBounds.Circuit) (Slv17 Wlv17 : Finset (Fin Nlv17)), 2 ≤ qlv17 → Nlv17 = qlv17 ^ 2 + qlv17 + 1 → (∀ llv17 : Fin Nlv17, (Finset.univ.filter (fun plv17 => Ilv17 plv17 llv17)).card = qlv17 + 1) → (∀ palv17 pblv17 : Fin Nlv17, palv17 ≠ pblv17 → ∃! lblv17 : Fin Nlv17, Ilv17 palv17 lblv17 ∧ Ilv17 pblv17 lblv17) → ((∀ glv17 ∈ Clv17.gates, (glv17.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv17 + Nlv17) Clv17) → Set.ncard {jlv17 : ℕ | jlv17 < Clv17.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.Ico Nlv17 (Nlv17 + Nlv17))).getD ilv17 0 = 0) ∨ (∀ hlv17 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.range Nlv17)).getD hlv17 0 = 0))} ≤ mlv17 → ((0 < Clv17.gates.length ∧ (∀ jlv17x1 < Clv17.gates.length, ∀ ilv17x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x1).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.image (fun plv17x3 : Fin Nlv17 => (plv17x3 : ℕ)) (Slv17)ᶜ ∪ Finset.image (fun llv17x3 : Fin Nlv17 => Nlv17 + (llv17x3 : ℕ)) (Wlv17)ᶜ)).getD ilv17x1 0 = 0) ∧ (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.image (fun plv17x4 : Fin Nlv17 => (plv17x4 : ℕ)) (Slv17)ᶜ ∪ Finset.image (fun llv17x4 : Fin Nlv17 => Nlv17 + (llv17x4 : ℕ)) (Wlv17)ᶜ)).getD Clv17.output 0 = 0) ∧ (∀ plv17x1 ∈ Slv17, ∀ llv17x1 ∈ Wlv17, Ilv17 plv17x1 llv17x1 → PEqualNP.MetaComplexity.circuitFun (Nlv17 + Nlv17) Clv17 (Fin.append (fun plv17x5 : Fin Nlv17 => decide (plv17x5 ∈ ({plv17x1} : Finset (Fin Nlv17)))) (fun llv17x5 : Fin Nlv17 => decide (llv17x5 ∈ ({llv17x1} : Finset (Fin Nlv17))))) = true) ∧ (∀ Xlv17 Ylv17 : Finset (Fin Nlv17), Xlv17 ⊆ Slv17 → Ylv17 ⊆ Wlv17 → Ylv17.card ≤ Klv17 → (∀ plv17x2 ∈ Xlv17, ∀ llv17x2 ∈ Ylv17, ¬ Ilv17 plv17x2 llv17x2) → PEqualNP.MetaComplexity.circuitFun (Nlv17 + Nlv17) Clv17 (Fin.append (fun plv17x6 : Fin Nlv17 => decide (plv17x6 ∈ Xlv17)) (fun llv17x6 : Fin Nlv17 => decide (llv17x6 ∈ Ylv17))) = false)) → 2 ^ mlv17 + Dlv17 = Klv17 + 1 → 1 ≤ Dlv17 → 1 ≤ Rlv17 → Rlv17 ≤ qlv17 → (∀ sglv17 : ℕ → Fin 2, ∀ wlv17 ∈ Wlv17, ∀ Xlv17x1 : Finset (Fin Nlv17), Xlv17x1 ⊆ Slv17 → (∀ plv17x7 ∈ Xlv17x1, ¬ Ilv17 plv17x7 wlv17) → Xlv17x1.card ≤ Rlv17 → PEqualNP.MetaComplexity.circuitFun (Nlv17 + Nlv17) (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv17x2 : Fin Clv17.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.Ico Nlv17 (Nlv17 + Nlv17))).getD ilv17x2 0 = 0) ∨ (∀ hlv17x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.range Nlv17)).getD hlv17x1 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).inputs.getD (sglv17 jlv17x2.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).inputs.getD (sglv17 jlv17x2.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val))) Clv17.output) (Fin.append (fun plv17x8 : Fin Nlv17 => decide (plv17x8 ∈ Xlv17x1)) (fun llv17x7 : Fin Nlv17 => decide (llv17x7 ∈ ({wlv17} : Finset (Fin Nlv17))))) = false) → Rlv17 * Dlv17 * ((Slv17 ×ˢ Wlv17).filter (fun pllv17 => Ilv17 pllv17.1 pllv17.2)).card ≤ Rlv17 * Dlv17 * Wlv17.card + max (Rlv17 * max (2 * Dlv17) (qlv17 + 1)) (3 * qlv17 * Dlv17) * Clv17.size := by
  intro hA hB hC q N K m R D I _ C S W hq hN hdeg huniq hC2 hm hSW hKD hD hR1 hRq hview
  by_cases hmix : 0 < (C.lineDegrees (N + N) (Finset.range N)).getD C.output 0 ∧
      0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD C.output 0
  · obtain ⟨hA1, -, hA3⟩ := hA N R I C _ _ S W hC2 hSW.1 rfl rfl
    obtain ⟨Xc, ps, hXg, hsz, hdep, hiff⟩ := hA3 hview hmix.1 hmix.2
    have hCres := hC q N R I Xc ps S W hq hN hdeg huniq hR1 hRq hXg hdep (by
      intro w hw Xs hXs hni hcard
      exact Bool.eq_false_iff.mpr (fun ht => hA1 hview w hw Xs hXs hni hcard ((hiff w hw _).mp ht)))
    have hBres := hB q N K m D I C _ S W hq hN hdeg huniq hC2 rfl hm hSW hKD hD
    have hs := PEqualNP.Outside.L_meta_1945.sum_ncard_eq S W _ _
      (fun w hw u => (hiff w hw (fun a => decide (a = u))).symm)
    rw [hs] at hBres
    have hcount := PEqualNP.Outside.L_meta_1945.count3 C.gates.length
      (fun j => (C.lineDegrees (N + N) (Finset.range N)).getD (N + N + j) 0)
      (fun j => (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (N + N + j) 0)
      (PEqualNP.Outside.L_meta_1945.deg_pos N C hC2)
    beta_reduce at hcount
    exact PEqualNP.Outside.L_meta_1945.arith _ _ _ _ _ _ _ _ _ _ _ _ hBres hCres hsz hcount
  · have hK : 1 ≤ K := by
      have := Nat.one_le_two_pow (n := m)
      omega
    have hinc : ((S ×ˢ W).filter (fun pl => I pl.1 pl.2)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ⟨p, l⟩ hpl hI
      rw [Finset.mem_product] at hpl
      have hacc := hSW.2.1 p hpl.1 l hpl.2 hI
      rcases not_and_or.mp hmix with h0 | h0
      · have h0b : (C.lineDegrees (N + N) (Finset.range N)).getD C.output 0 = 0 := by omega
        have hrej := hSW.2.2 ∅ {l} (Finset.empty_subset _) (Finset.singleton_subset_iff.mpr hpl.2)
          (by simpa using hK) (by simp)
        have hM : ∀ i : Fin (N + N), i.val ∉ Finset.range N →
            Fin.append (fun a => decide (a ∈ ({p} : Finset (Fin N))))
              (fun b => decide (b ∈ ({l} : Finset (Fin N)))) i =
            Fin.append (fun a => decide (a ∈ (∅ : Finset (Fin N))))
              (fun b => decide (b ∈ ({l} : Finset (Fin N)))) i := by
          intro i hi
          obtain ⟨v, hv⟩ := i
          simp only [Fin.val_mk, Finset.mem_range, not_lt] at hi
          rw [PEqualNP.Outside.L_meta_1945.append_right_val _ _ _ v hv hi,
            PEqualNP.Outside.L_meta_1945.append_right_val _ _ _ v hv hi]
        have e := PEqualNP.Outside.L_meta_1945.eval_eq_of_deg0 N C _ _ _ hM h0b
        exact absurd (hacc.symm.trans (e.trans hrej)) (by decide)
      · have h0b : (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD C.output 0 = 0 := by omega
        have hrej := hSW.2.2 {p} ∅ (Finset.singleton_subset_iff.mpr hpl.1) (Finset.empty_subset _)
          (by simp) (by simp)
        have hM : ∀ i : Fin (N + N), i.val ∉ Finset.Ico N (N + N) →
            Fin.append (fun a => decide (a ∈ ({p} : Finset (Fin N))))
              (fun b => decide (b ∈ ({l} : Finset (Fin N)))) i =
            Fin.append (fun a => decide (a ∈ ({p} : Finset (Fin N))))
              (fun b => decide (b ∈ (∅ : Finset (Fin N)))) i := by
          intro i hi
          obtain ⟨v, hv⟩ := i
          simp only [Fin.val_mk, Finset.mem_Ico, not_and, not_lt] at hi
          have hvN : v < N := by
            rcases Nat.lt_or_ge v N with h | h
            · exact h
            · exact absurd (hi h) (by omega)
          rw [PEqualNP.Outside.L_meta_1945.append_left_val _ _ _ v hv hvN,
            PEqualNP.Outside.L_meta_1945.append_left_val _ _ _ v hv hvN]
        have e := PEqualNP.Outside.L_meta_1945.eval_eq_of_deg0 N C _ _ _ hM h0b
        exact absurd (hacc.symm.trans (e.trans hrej)) (by decide)
    rw [hinc]
    simp
