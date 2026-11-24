import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2774

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_len (gs : List Gate) (x : List Bool) :
    (gs.foldl stepW x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, stepW] <;> omega

theorem fold_pre (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl stepW x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    have hl : x.length < (stepW x g).length := by
      simp only [stepW, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.foldl_cons, ih _ (lt_trans hi hl)]
    simp only [stepW]
    exact List.getD_append _ _ _ _ hi

theorem fold_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ gs[j].inputs, i < x.length + j) :
    (gs.foldl stepW x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (gs.foldl stepW x).getD i false) := by
  have hF : ((gs.take j).foldl stepW x).length = x.length + j := by
    rw [fold_len, List.length_take]; omega
  have hfull : gs.foldl stepW x =
      (gs.drop (j + 1)).foldl stepW (stepW ((gs.take j).foldl stepW x) gs[j]) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
    rw [List.foldl_append, List.foldl_cons]
  have hS : x.length + j < (stepW ((gs.take j).foldl stepW x) gs[j]).length := by
    simp only [stepW, List.length_append, List.length_cons, List.length_nil, hF]
    omega
  have hread : ∀ i < x.length + j,
      (gs.foldl stepW x).getD i false = ((gs.take j).foldl stepW x).getD i false := by
    intro i hi
    rw [hfull, fold_pre _ _ _ (by omega)]
    simp only [stepW]
    exact List.getD_append _ _ _ _ (by omega)
  have hL : (gs.foldl stepW x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => ((gs.take j).foldl stepW x).getD i false) := by
    rw [hfull, fold_pre _ _ _ hS]
    simp only [stepW]
    rw [List.getD_append_right _ _ _ _ (by omega), hF, Nat.sub_self, List.getD_cons_zero]
  rw [hL]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (hread i (hrb i hi)).symm

def VV (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem VV_low (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    VV n C x w = (List.ofFn x).getD w false := by
  unfold VV
  exact fold_pre C.gates (List.ofFn x) w (by simpa using hw)

theorem VV_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hrb : ReadsBack n C) (j : ℕ)
    (hj : j < C.gates.length) :
    VV n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (VV n C x)) := by
  have hg : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hl : (List.ofFn x).length = n := List.length_ofFn
  have key := fold_gate C.gates (List.ofFn x) j hj (by
    intro i hi; rw [hl]; exact hrb j hj i (by rw [hg]; exact hi))
  rw [hl] at key
  rw [hg]
  exact key

theorem LR (n : ℕ) (D : Circuit) (hrb : ReadsBack n D) (x : Fin n → Bool) (P : ℕ → Prop)
    (r : ℕ)
    (hP : ∀ w, P w → w ≠ r → ∃ j < D.gates.length, (gateAt D j).op = GateOp.or ∧
      w ∈ (gateAt D j).inputs ∧ P (n + j)) :
    ∀ m w, n + D.gates.length - w = m → P w → VV n D x w = true → VV n D x r = true := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro w hm hPw hv
    by_cases hwr : w = r
    · rw [← hwr]; exact hv
    obtain ⟨j, hj, hor, hin, hPj⟩ := hP w hPw hwr
    have hlt : w < n + j := hrb j hj w hin
    refine ih (n + D.gates.length - (n + j)) (by omega) (n + j) rfl hPj ?_
    rw [VV_gate n D x hrb j hj, hor]
    exact List.any_eq_true.mpr ⟨VV n D x w, List.mem_map.mpr ⟨w, hin, rfl⟩, hv⟩

theorem op2 (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (p q p' q' u : Bool)
    (hp : p' = true → p = true ∨ u = true) (hq : q' = true → q = true ∨ u = true) :
    op.eval [p', q'] = true → op.eval [p, q] = true ∨ u = true := by
  rcases hop with rfl | rfl <;> cases p <;> cases q <;> cases p' <;> cases q' <;> cases u <;>
    simp_all [GateOp.eval]

theorem claim (n len e t k s a b c : ℕ) (T : Finset ℕ) (G : ℕ → Gate) (VC VD : ℕ → Bool)
    (rh : ℕ → ℕ)
    (hG2 : ∀ j < len, (G j).op = GateOp.and ∨ (G j).op = GateOp.or)
    (hGl : ∀ j < len, ∃ p q, (G j).inputs = [p, q])
    (hrb : ∀ j < len, ∀ i ∈ (G j).inputs, i < n + j)
    (hTor : ∀ j ∈ T, (G j).op = GateOp.or)
    (heT : e ∉ T) (hkT : k ∉ T) (htT : t ∈ T)
    (hnon : ∀ m < len, m ∉ T → n + e ∉ (G m).inputs ∧ n + k ∉ (G m).inputs ∧
      ∀ j ∈ T, n + j ∉ (G m).inputs)
    (hnoE : ∀ j < len, j ≠ t → n + e ∉ (G j).inputs)
    (ht_in : (G t).inputs = [n + e, s] ∨ (G t).inputs = [s, n + e])
    (hs : s < n + t) (hse : s ≠ n + e)
    (ha : a < n + e) (hb : b < n + e) (hck : c < n + k) (hce : c ≠ n + e)
    (haT : ∀ j ∈ T, a ≠ n + j) (hbT : ∀ j ∈ T, b ≠ n + j) (hcT : ∀ j ∈ T, c ≠ n + j)
    (hek : e < k) (het : e < t)
    (hk_in : (G k).inputs = [a, c] ∨ (G k).inputs = [c, a]) (hk_op : (G k).op = GateOp.and)
    (he_in : (G e).inputs = [a, b] ∨ (G e).inputs = [b, a]) (he_op : (G e).op = GateOp.and)
    (hlow : ∀ w < n, VD (rh w) = VC w)
    (hC : ∀ j < len, VC (n + j) = (G j).op.eval ((G j).inputs.map VC))
    (hD : ∀ j < len, j ≠ e → j ≠ t → j ≠ k →
      VD (rh (n + j)) = (G j).op.eval ((G j).inputs.map (fun i => VD (rh i))))
    (hDk : VD (rh (n + k)) = (VD (rh a) && (VD (rh b) || VD (rh c))))
    (hrht : rh (n + t) = rh s)
    (hk : k < len) (ht : t < len) (he : e < len) :
    ∀ w, w < n + len → w ≠ n + e →
      (VD (rh w) = true → VC w = true ∨ VC (n + e) = true) ∧
      (VC w = true → VD (rh w) = true ∨ VC (n + e) = true) ∧
      ((¬ (n ≤ w ∧ w - n ∈ T)) → w ≠ n + k → VD (rh w) = VC w) := by
  have hnj : ∀ i, (∀ j ∈ T, i ≠ n + j) → ¬ (n ≤ i ∧ i - n ∈ T) := by
    intro i h ⟨h1, h2⟩
    exact h (i - n) h2 (by omega)
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw hwe
  by_cases hwn : w < n
  · have h0 := hlow w hwn
    exact ⟨fun h => Or.inl (by rw [← h0]; exact h), fun h => Or.inl (by rw [h0]; exact h),
      fun _ _ => h0⟩
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < len := by omega
  have hje : j ≠ e := fun h => hwe (by rw [h])
  by_cases hjt : j = t
  · rw [hjt]
    obtain ⟨hA, hB, -⟩ := ih s (by omega) (by omega) hse
    have hCt : VC (n + t) = (VC s || VC (n + e)) := by
      rw [hC t ht, hTor t htT]
      rcases ht_in with h | h <;> rw [h] <;> simp [GateOp.eval, Bool.or_comm]
    refine ⟨?_, ?_, ?_⟩
    · intro h
      rw [hrht] at h
      rcases hA h with h' | h'
      · left; simp [hCt, h']
      · right; exact h'
    · intro h
      rw [hrht]
      rw [hCt, Bool.or_eq_true] at h
      rcases h with h | h
      · exact hB h
      · exact Or.inr h
    · intro hn
      exact absurd ⟨Nat.le_add_right n t, by rw [Nat.add_sub_cancel_left]; exact htT⟩ hn
  by_cases hjk : j = k
  · rw [hjk]
    have hEa := (ih a (by omega) (by omega) (by omega)).2.2 (hnj a haT) (by omega)
    have hEb := (ih b (by omega) (by omega) (by omega)).2.2 (hnj b hbT) (by omega)
    have hEc := (ih c (by omega) (by omega) hce).2.2 (hnj c hcT) (by omega)
    have hCk : VC (n + k) = (VC a && VC c) := by
      rw [hC k hk, hk_op]
      rcases hk_in with h | h <;> rw [h] <;> simp [GateOp.eval, Bool.and_comm]
    have hu : VC (n + e) = (VC a && VC b) := by
      rw [hC e he, he_op]
      rcases he_in with h | h <;> rw [h] <;> simp [GateOp.eval, Bool.and_comm]
    rw [hDk, hEa, hEb, hEc, hCk, hu]
    generalize VC a = A
    generalize VC b = B
    generalize VC c = Cc
    cases A <;> cases B <;> cases Cc <;> simp
  by_cases hjT : j ∈ T
  · obtain ⟨p, q, hpq⟩ := hGl j hj
    have hp : p < n + j := hrb j hj p (by rw [hpq]; simp)
    have hq : q < n + j := hrb j hj q (by rw [hpq]; simp)
    have hpe : p ≠ n + e := fun h => hnoE j hj hjt (by rw [hpq, ← h]; simp)
    have hqe : q ≠ n + e := fun h => hnoE j hj hjt (by rw [hpq, ← h]; simp)
    obtain ⟨hpA, hpB, -⟩ := ih p hp (by omega) hpe
    obtain ⟨hqA, hqB, -⟩ := ih q hq (by omega) hqe
    have hop := hG2 j hj
    rw [hD j hj hje hjt hjk, hC j hj, hpq]
    simp only [List.map_cons, List.map_nil]
    refine ⟨op2 _ hop _ _ _ _ _ hpA hqA, op2 _ hop _ _ _ _ _ hpB hqB, ?_⟩
    intro hn
    exact absurd ⟨Nat.le_add_right n j, by rw [Nat.add_sub_cancel_left]; exact hjT⟩ hn
  · obtain ⟨hne, hnk, hnT⟩ := hnon j hj hjT
    obtain ⟨p, q, hpq⟩ := hGl j hj
    have hpm : p ∈ (G j).inputs := by rw [hpq]; simp
    have hqm : q ∈ (G j).inputs := by rw [hpq]; simp
    have hp : p < n + j := hrb j hj p hpm
    have hq : q < n + j := hrb j hj q hqm
    have hpe : p ≠ n + e := fun h => hne (h ▸ hpm)
    have hqe : q ≠ n + e := fun h => hne (h ▸ hqm)
    have hpk : p ≠ n + k := fun h => hnk (h ▸ hpm)
    have hqk : q ≠ n + k := fun h => hnk (h ▸ hqm)
    have hpT : ∀ j' ∈ T, p ≠ n + j' := fun j' hj' h => hnT j' hj' (h ▸ hpm)
    have hqT : ∀ j' ∈ T, q ≠ n + j' := fun j' hj' h => hnT j' hj' (h ▸ hqm)
    have hEp := (ih p hp (by omega) hpe).2.2 (hnj p hpT) hpk
    have hEq := (ih q hq (by omega) hqe).2.2 (hnj q hqT) hqk
    have hval : VD (rh (n + j)) = VC (n + j) := by
      rw [hD j hj hje hjt hjk, hC j hj, hpq]
      simp [hEp, hEq]
    exact ⟨fun h => Or.inl (by rw [← hval]; exact h), fun h => Or.inl (by rw [hval]; exact h),
      fun _ _ => hval⟩

def rho (n e t k w : ℕ) : ℕ :=
  w - (if n + e < w then 1 else 0) - (if n + t < w then 1 else 0) + (if n + k ≤ w then 1 else 0)

def zp (t k : ℕ) : ℕ := k - 1 - (if t < k then 1 else 0)

def sig0 (e t i : ℕ) : ℕ := if i < e then i else if i + 1 < t then i + 1 else i + 2

def sig (e t k j : ℕ) : ℕ := sig0 e t (if zp t k < j then j - 1 else j)

def rh (n e t k s w : ℕ) : ℕ := rho n e t k (if w = n + t then s else w)

theorem rho_low (n e t k w : ℕ) (h1 : e < k) (h2 : e < t) (hw : w ≤ n + e) :
    rho n e t k w = w := by
  unfold rho; split_ifs <;> omega

theorem rho_lt (n e t k w₁ w₂ : ℕ) (h12 : w₁ < w₂) (h1e : w₁ ≠ n + e) (h2e : w₂ ≠ n + e)
    (h1t : w₁ ≠ n + t) (h2t : w₂ ≠ n + t) (het : e < t) :
    rho n e t k w₁ < rho n e t k w₂ := by
  unfold rho; split_ifs <;> omega

theorem rho_k (n e t k : ℕ) (h1 : e < k) (h2 : e < t) (h3 : t ≠ k) :
    rho n e t k (n + k) = n + zp t k + 1 := by
  unfold rho zp; split_ifs <;> omega

theorem zp_ge (e t k : ℕ) (h1 : e < k) (h2 : e < t) (h3 : t ≠ k) : e ≤ zp t k := by
  unfold zp; split_ifs <;> omega

theorem rho_ltk (n e t k w : ℕ) (h1 : e < k) (h2 : e < t) (h3 : t ≠ k) (hw : w < n + k)
    (hwe : w ≠ n + e) (hwt : w ≠ n + t) : rho n e t k w < n + zp t k := by
  unfold rho zp; split_ifs <;> omega

theorem sig_spec (n e t k len j : ℕ) (h1 : e < k) (h2 : e < t) (h3 : t ≠ k) (hk : k < len)
    (ht : t < len) (hj : j < len - 1) (hjz : j ≠ zp t k) :
    sig e t k j < len ∧ sig e t k j ≠ e ∧ sig e t k j ≠ t ∧
      rho n e t k (n + sig e t k j) = n + j := by
  have hz : zp t k = k - 1 - (if t < k then 1 else 0) := rfl
  by_cases htk : t < k
  · rw [if_pos htk] at hz
    rw [hz] at hjz
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [sig, sig0, rho, hz]; split_ifs <;> omega)
  · rw [if_neg htk] at hz
    rw [hz] at hjz
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [sig, sig0, rho, hz]; split_ifs <;> omega)

theorem nu_spec (n e t k len j : ℕ) (h1 : e < k) (h2 : e < t) (h3 : t ≠ k) (hk : k < len)
    (ht : t < len) (hj : j < len) (hje : j ≠ e) (hjt : j ≠ t) :
    ∃ j', rho n e t k (n + j) = n + j' ∧ j' < len - 1 ∧ j' ≠ zp t k ∧ sig e t k j' = j := by
  refine ⟨rho n e t k (n + j) - n, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [sig, sig0, rho, zp]; split_ifs <;> omega)

def newGate (C : Circuit) (n e t k s a b c j : ℕ) : Gate :=
  if j = zp t k then ⟨GateOp.or, [rh n e t k s b, rh n e t k s c]⟩
  else if sig e t k j = k then ⟨GateOp.and, [rh n e t k s a, n + zp t k]⟩
  else ⟨(gateAt C (sig e t k j)).op, (gateAt C (sig e t k j)).inputs.map (rh n e t k s)⟩

def mkD (C : Circuit) (n e t k s a b c : ℕ) : Circuit :=
  ⟨List.ofFn (fun j : Fin (C.gates.length - 1) => newGate C n e t k s a b c j.val),
    rh n e t k s C.output⟩

theorem gateAt_mkD (C : Circuit) (n e t k s a b c j : ℕ) (hj : j < C.gates.length - 1) :
    gateAt (mkD C n e t k s a b c) j = newGate C n e t k s a b c j := by
  unfold gateAt mkD
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem mkD_len (C : Circuit) (n e t k s a b c : ℕ) :
    (mkD C n e t k s a b c).gates.length = C.gates.length - 1 := by
  simp [mkD]

theorem core (n : ℕ) (C : Circuit) (T L : Finset ℕ) (e k a b c : ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hrb : ReadsBack n C) (hTree : IsOrTree n C T L C.output)
    (heL : n + e ∈ L) (hkL : n + k ∈ L) (hek : e < k)
    (he_op : (gateAt C e).op = GateOp.and)
    (he_in : (gateAt C e).inputs = [a, b] ∨ (gateAt C e).inputs = [b, a])
    (hk_op : (gateAt C k).op = GateOp.and)
    (hk_in : (gateAt C k).inputs = [a, c] ∨ (gateAt C k).inputs = [c, a])
    (hnon : ∀ m < C.gates.length, m ∉ T → n + e ∉ (gateAt C m).inputs ∧
      n + k ∉ (gateAt C m).inputs ∧ ∀ j ∈ T, n + j ∉ (gateAt C m).inputs) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧
      D.size + 1 ≤ C.size := by
  classical
  obtain ⟨hT1, hT2, hT3, hT4⟩ := hTree
  have hlt2 : ∀ j, (gateAt C j).inputs.length = 2 → j < C.gates.length := by
    intro j hj
    by_contra hc
    have h0 : gateAt C j = ⟨GateOp.or, []⟩ := List.getD_eq_default _ _ (by omega)
    rw [h0] at hj
    simp at hj
  have hmem : ∀ j < C.gates.length, gateAt C j ∈ C.gates := fun j hj => by
    rw [show gateAt C j = C.gates[j] from List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have hG2 : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or :=
    fun j hj => hAO.1 _ (hmem j hj)
  have hGlen : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2 :=
    fun j hj => hAO.2.2 _ (hmem j hj)
  have hGl : ∀ j < C.gates.length, ∃ p q, (gateAt C j).inputs = [p, q] :=
    fun j hj => List.length_eq_two.mp (hGlen j hj)
  have he : e < C.gates.length := hlt2 e (by rcases he_in with h | h <;> rw [h] <;> rfl)
  have hk : k < C.gates.length := hlt2 k (by rcases hk_in with h | h <;> rw [h] <;> rfl)
  have heT : e ∉ T := fun h => (hT2 _ heL).1 ⟨by omega, by simpa using h⟩
  have hkT : k ∉ T := fun h => (hT2 _ hkL).1 ⟨by omega, by simpa using h⟩
  have hTne : T ≠ ∅ := by
    intro h0
    have hL := hT4
    rw [if_pos h0] at hL
    rw [hL, Finset.mem_singleton] at heL hkL
    omega
  obtain ⟨j0, hj0T, hout⟩ : ∃ j ∈ T, C.output = n + j := by
    have h4 := hT4
    rw [if_neg hTne] at h4
    exact h4
  have hj0 : j0 < C.gates.length := hlt2 j0 (hT1 j0 hj0T).2.1
  have hreadsIn : ∀ w, (w ∈ L ∨ (n ≤ w ∧ w - n ∈ T)) → w ≠ C.output → readsIn C T w = 1 := by
    intro w hw hwo
    rcases hw with hw | ⟨hw1, hw2⟩
    · rw [(hT2 w hw).2, if_neg hwo]
    · have h3 := hT3 (w - n) hw2
      rw [show n + (w - n) = w by omega, if_neg hwo] at h3
      exact h3
  have hreader : ∀ w, (w ∈ L ∨ (n ≤ w ∧ w - n ∈ T)) → w ≠ C.output →
      ∃ j ∈ T, w ∈ (gateAt C j).inputs := by
    intro w hw hwo
    have h1 := hreadsIn w hw hwo
    unfold readsIn at h1
    obtain ⟨j, hjT, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (by rw [h1]; exact one_ne_zero : (∑ j ∈ T, (gateAt C j).inputs.count w) ≠ 0)
    exact ⟨j, hjT, List.count_pos_iff.mp (Nat.pos_of_ne_zero hj)⟩
  have hoe : C.output ≠ n + e := by
    rw [hout]
    intro h
    have hje : j0 = e := by omega
    exact heT (hje ▸ hj0T)
  obtain ⟨t, htT, hte⟩ := hreader (n + e) (Or.inl heL) (Ne.symm hoe)
  have hsum1 := hreadsIn (n + e) (Or.inl heL) (Ne.symm hoe)
  unfold readsIn at hsum1
  have hct : (gateAt C t).inputs.count (n + e) ≤ 1 := by
    rw [← hsum1]
    exact Finset.single_le_sum (f := fun i => (gateAt C i).inputs.count (n + e))
      (fun _ _ => Nat.zero_le _) htT
  have huniq : ∀ j ∈ T, j ≠ t → n + e ∉ (gateAt C j).inputs := by
    intro j hjT hjt hin
    have h2 : ∑ i ∈ ({j, t} : Finset ℕ), (gateAt C i).inputs.count (n + e) ≤
        ∑ i ∈ T, (gateAt C i).inputs.count (n + e) :=
      Finset.sum_le_sum_of_subset (by
        intro y hy
        rw [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> assumption)
    rw [Finset.sum_pair hjt, hsum1] at h2
    have h3 := List.count_pos_iff.mpr hin
    have h4 := List.count_pos_iff.mpr hte
    omega
  have ht : t < C.gates.length := hlt2 t (hT1 t htT).2.1
  obtain ⟨s, hse, ht_in⟩ : ∃ s, s ≠ n + e ∧
      ((gateAt C t).inputs = [n + e, s] ∨ (gateAt C t).inputs = [s, n + e]) := by
    obtain ⟨p, q, hpq⟩ := hGl t ht
    rw [hpq] at hte hct
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hte
    rcases hte with h | h
    · subst h
      refine ⟨q, ?_, Or.inl hpq⟩
      intro hq
      subst hq
      simp at hct
    · subst h
      refine ⟨p, ?_, Or.inr hpq⟩
      intro hp
      subst hp
      simp at hct
  have het' : e < t := by
    have h5 := hrb t ht (n + e) hte
    omega
  have hs : s < n + t := hrb t ht s (by rcases ht_in with h | h <;> rw [h] <;> simp)
  have htk : t ≠ k := fun h => hkT (h ▸ htT)
  have hein : ∀ i, (i = a ∨ i = b) → i ∈ (gateAt C e).inputs := by
    intro i hi
    rcases hi with rfl | rfl <;> rcases he_in with h | h <;> rw [h] <;> simp
  have hkin : ∀ i, (i = a ∨ i = c) → i ∈ (gateAt C k).inputs := by
    intro i hi
    rcases hi with rfl | rfl <;> rcases hk_in with h | h <;> rw [h] <;> simp
  have ha : a < n + e := hrb e he a (hein a (Or.inl rfl))
  have hb : b < n + e := hrb e he b (hein b (Or.inr rfl))
  have hck : c < n + k := hrb k hk c (hkin c (Or.inr rfl))
  have hce : c ≠ n + e := fun h => (hnon k hk hkT).1 (h ▸ hkin c (Or.inr rfl))
  have hcT : ∀ j ∈ T, c ≠ n + j := fun j hj h =>
    (hnon k hk hkT).2.2 j hj (h ▸ hkin c (Or.inr rfl))
  have haT : ∀ j ∈ T, a ≠ n + j := fun j hj h =>
    (hnon e he heT).2.2 j hj (h ▸ hein a (Or.inl rfl))
  have hbT : ∀ j ∈ T, b ≠ n + j := fun j hj h =>
    (hnon e he heT).2.2 j hj (h ▸ hein b (Or.inr rfl))
  have hnoE : ∀ j < C.gates.length, j ≠ t → n + e ∉ (gateAt C j).inputs := by
    intro j hj hjt
    by_cases hjT : j ∈ T
    · exact huniq j hjT hjt
    · exact (hnon j hj hjT).1
  have hrhb : rh n e t k s b = b := by
    unfold rh; rw [if_neg (by omega)]; exact rho_low n e t k b hek het' (by omega)
  have hrha : rh n e t k s a = a := by
    unfold rh; rw [if_neg (by omega)]; exact rho_low n e t k a hek het' (by omega)
  have hrhc : rh n e t k s c = rho n e t k c := by
    unfold rh; rw [if_neg (hcT t htT)]
  have hrhs : rh n e t k s s = rho n e t k s := by
    unfold rh; rw [if_neg (by omega)]
  have hrht : rh n e t k s (n + t) = rho n e t k s := by
    unfold rh; rw [if_pos rfl]
  have hrhj : ∀ j, j ≠ t → rh n e t k s (n + j) = rho n e t k (n + j) := by
    intro j hj; unfold rh; rw [if_neg (by omega)]
  have hzg := zp_ge e t k hek het' htk
  have hng : ∀ j' < C.gates.length - 1,
      ((newGate C n e t k s a b c j').op = GateOp.and ∨
        (newGate C n e t k s a b c j').op = GateOp.or) ∧
      (newGate C n e t k s a b c j').inputs.length = 2 ∧
      ∀ i ∈ (newGate C n e t k s a b c j').inputs, i < n + j' := by
    intro j' hj'
    unfold newGate
    by_cases hz : j' = zp t k
    · rw [if_pos hz]
      refine ⟨Or.inr rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · rw [hrhb]; omega
      · rw [hrhc]
        have h6 := rho_ltk n e t k c hek het' htk hck hce (hcT t htT)
        omega
    · rw [if_neg hz]
      obtain ⟨hs1, hs2, hs3, hs4⟩ := sig_spec n e t k C.gates.length j' hek het' htk hk ht hj' hz
      by_cases hsk : sig e t k j' = k
      · rw [if_pos hsk]
        have hj'z : j' = zp t k + 1 := by
          rw [hsk, rho_k n e t k hek het' htk] at hs4
          omega
        refine ⟨Or.inl rfl, rfl, ?_⟩
        intro i hi
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · rw [hrha]; omega
        · omega
      · rw [if_neg hsk]
        refine ⟨hG2 _ hs1, by simp [hGlen _ hs1], ?_⟩
        intro i hi
        rw [List.mem_map] at hi
        obtain ⟨i0, hi0, rfl⟩ := hi
        have hi0lt := hrb _ hs1 i0 hi0
        have hi0e : i0 ≠ n + e := fun h => hnoE _ hs1 hs3 (h ▸ hi0)
        by_cases hi0t : i0 = n + t
        · unfold rh
          rw [if_pos hi0t, ← hs4]
          exact rho_lt n e t k s _ (by omega) hse (by omega) (by omega) (by omega) het'
        · unfold rh
          rw [if_neg hi0t, ← hs4]
          exact rho_lt n e t k i0 _ hi0lt hi0e (by omega) hi0t (by omega) het'
  have hDlen := mkD_len C n e t k s a b c
  have hAOD : PEqualNP.TopForm.IsAO2 n (mkD C n e t k s a b c) := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [mkD, List.mem_ofFn, Set.mem_range] at hg
      obtain ⟨j', rfl⟩ := hg
      exact (hng j'.val j'.isLt).1
    · intro j' hj' i hi
      rw [hDlen] at hj'
      rw [gateAt_mkD C n e t k s a b c j' hj'] at hi
      exact (hng j' hj').2.2 i hi
    · intro g hg
      simp only [mkD, List.mem_ofFn, Set.mem_range] at hg
      obtain ⟨j', rfl⟩ := hg
      exact (hng j'.val j'.isLt).2.1
  have hrbD : ReadsBack n (mkD C n e t k s a b c) := hAOD.2.1
  have hDT : ∀ j ∈ T, j ≠ t → ∃ j' < (mkD C n e t k s a b c).gates.length,
      (gateAt (mkD C n e t k s a b c) j').op = GateOp.or ∧
      (gateAt (mkD C n e t k s a b c) j').inputs = (gateAt C j).inputs.map (rh n e t k s) ∧
      rh n e t k s (n + j) = n + j' := by
    intro j hjT hjt
    have hj := hlt2 j (hT1 j hjT).2.1
    have hje : j ≠ e := fun h => heT (h ▸ hjT)
    have hjk : j ≠ k := fun h => hkT (h ▸ hjT)
    obtain ⟨j', h1, h2, h3, h4⟩ := nu_spec n e t k C.gates.length j hek het' htk hk ht hj hje hjt
    have hg : gateAt (mkD C n e t k s a b c) j' =
        ⟨(gateAt C j).op, (gateAt C j).inputs.map (rh n e t k s)⟩ := by
      rw [gateAt_mkD C n e t k s a b c j' h2]
      unfold newGate
      rw [if_neg h3, h4, if_neg hjk]
    exact ⟨j', by rw [hDlen]; exact h2, by rw [hg]; exact (hT1 j hjT).1, by rw [hg],
      by rw [hrhj j hjt, h1]⟩
  have hsem : ∀ x : Fin n → Bool,
      VV n (mkD C n e t k s a b c) x (rh n e t k s C.output) = VV n C x C.output := by
    intro x
    have hDgen : ∀ j < C.gates.length, j ≠ e → j ≠ t → j ≠ k →
        VV n (mkD C n e t k s a b c) x (rh n e t k s (n + j)) =
          (gateAt C j).op.eval ((gateAt C j).inputs.map
            (fun i => VV n (mkD C n e t k s a b c) x (rh n e t k s i))) := by
      intro j hj hje hjt hjk
      obtain ⟨j', h1, h2, h3, h4⟩ :=
        nu_spec n e t k C.gates.length j hek het' htk hk ht hj hje hjt
      rw [hrhj j hjt, h1, VV_gate n _ x hrbD j' (by rw [hDlen]; exact h2),
        gateAt_mkD C n e t k s a b c j' h2]
      unfold newGate
      rw [if_neg h3, h4, if_neg hjk, List.map_map]
      rfl
    have hDk : VV n (mkD C n e t k s a b c) x (rh n e t k s (n + k)) =
        (VV n (mkD C n e t k s a b c) x (rh n e t k s a) &&
          (VV n (mkD C n e t k s a b c) x (rh n e t k s b) ||
            VV n (mkD C n e t k s a b c) x (rh n e t k s c))) := by
      obtain ⟨j', h1, h2, h3, h4⟩ :=
        nu_spec n e t k C.gates.length k hek het' htk hk ht hk (by omega) (Ne.symm htk)
      have hz : zp t k < C.gates.length - 1 := by
        have h7 := rho_k n e t k hek het' htk
        omega
      rw [hrhj k (Ne.symm htk), h1, VV_gate n _ x hrbD j' (by rw [hDlen]; exact h2),
        gateAt_mkD C n e t k s a b c j' h2]
      unfold newGate
      rw [if_neg h3, if_pos h4]
      simp only [List.map_cons, List.map_nil]
      rw [VV_gate n _ x hrbD (zp t k) (by rw [hDlen]; exact hz),
        gateAt_mkD C n e t k s a b c (zp t k) hz]
      unfold newGate
      rw [if_pos rfl]
      simp [GateOp.eval]
    have hlow : ∀ w < n, VV n (mkD C n e t k s a b c) x (rh n e t k s w) = VV n C x w := by
      intro w hw
      have h8 : rh n e t k s w = w := by
        unfold rh; rw [if_neg (by omega)]; exact rho_low n e t k w hek het' (by omega)
      rw [h8, VV_low n _ x w hw, VV_low n C x w hw]
    have hcl := claim n C.gates.length e t k s a b c T (gateAt C) (VV n C x)
      (VV n (mkD C n e t k s a b c) x) (rh n e t k s) hG2 hGl hrb (fun j hj => (hT1 j hj).1)
      heT hkT htT hnon hnoE ht_in hs hse ha hb hck hce haT hbT hcT hek het' hk_in hk_op he_in
      he_op hlow (fun j hj => VV_gate n C x hrb j hj) hDgen hDk (by rw [hrht, hrhs]) hk ht he
    have hLRC : VV n C x (n + e) = true → VV n C x C.output = true := by
      intro hu
      refine LR n C hrb x (fun w => w ∈ L ∨ (n ≤ w ∧ w - n ∈ T)) C.output ?_ _ (n + e) rfl
        (Or.inl heL) hu
      intro w hw hwo
      obtain ⟨j, hjT, hj⟩ := hreader w hw hwo
      exact ⟨j, hlt2 j (hT1 j hjT).2.1, (hT1 j hjT).1, hj, Or.inr ⟨by omega, by simpa using hjT⟩⟩
    have hcaseT : n + t ≠ C.output → ∃ j' < (mkD C n e t k s a b c).gates.length,
        (gateAt (mkD C n e t k s a b c) j').op = GateOp.or ∧
        rh n e t k s (n + t) ∈ (gateAt (mkD C n e t k s a b c) j').inputs ∧
        ∃ w, (w ∈ L ∨ (n ≤ w ∧ w - n ∈ T)) ∧ w ≠ n + e ∧ rh n e t k s w = n + j' := by
      intro hto
      obtain ⟨j2, hj2T, hj2⟩ := hreader (n + t) (Or.inr ⟨by omega, by simpa using htT⟩) hto
      have h9 := hrb j2 (hlt2 j2 (hT1 j2 hj2T).2.1) (n + t) hj2
      have hj2t : j2 ≠ t := by omega
      obtain ⟨j', hj', hop, hin, hrj⟩ := hDT j2 hj2T hj2t
      refine ⟨j', hj', hop, ?_, n + j2, Or.inr ⟨by omega, by simpa using hj2T⟩,
        fun h => heT (by have h10 : j2 = e := by omega
                         exact h10 ▸ hj2T), hrj⟩
      rw [hin]
      exact List.mem_map.mpr ⟨n + t, hj2, rfl⟩
    have hLRD : VV n (mkD C n e t k s a b c) x (rh n e t k s (n + k)) = true →
        VV n (mkD C n e t k s a b c) x (rh n e t k s C.output) = true := by
      intro hv
      refine LR n (mkD C n e t k s a b c) hrbD x
        (fun w' => ∃ w, (w ∈ L ∨ (n ≤ w ∧ w - n ∈ T)) ∧ w ≠ n + e ∧ rh n e t k s w = w')
        (rh n e t k s C.output) ?_ _ _ rfl ⟨n + k, Or.inl hkL, by omega, rfl⟩ hv
      intro w' hw' hne
      obtain ⟨w, hw, hwe, rfl⟩ := hw'
      by_cases hwt : w = n + t
      · rw [hwt] at hne ⊢
        exact hcaseT (fun h => hne (by rw [h]))
      · have hwo : w ≠ C.output := fun h => hne (by rw [h])
        obtain ⟨j, hjT, hj⟩ := hreader w hw hwo
        by_cases hjt : j = t
        · rw [hjt] at hj
          have hws : w = s := by
            rcases ht_in with h | h <;> rw [h] at hj <;> simp at hj <;> omega
          have hto : n + t ≠ C.output := fun h => hne (by rw [hws, hrhs, ← hrht, h])
          obtain ⟨j', hj', hop, hin, hP⟩ := hcaseT hto
          refine ⟨j', hj', hop, ?_, hP⟩
          rw [hws, hrhs, ← hrht]
          exact hin
        · obtain ⟨j', hj', hop, hin, hrj⟩ := hDT j hjT hjt
          refine ⟨j', hj', hop, ?_, n + j, Or.inr ⟨by omega, by simpa using hjT⟩,
            fun h => heT (by have h11 : j = e := by omega
                             exact h11 ▸ hjT), hrj⟩
          rw [hin]
          exact List.mem_map.mpr ⟨w, hj, rfl⟩
    obtain ⟨hA, hB, -⟩ := hcl C.output (by rw [hout]; omega) hoe
    have hEa := (hcl a (by omega) (by omega)).2.2
      (fun h => haT (a - n) h.2 (by omega)) (by omega)
    have hEb := (hcl b (by omega) (by omega)).2.2
      (fun h => hbT (b - n) h.2 (by omega)) (by omega)
    have hu : VV n C x (n + e) = (VV n C x a && VV n C x b) := by
      rw [VV_gate n C x hrb e he, he_op]
      rcases he_in with h | h <;> rw [h] <;> simp [GateOp.eval, Bool.and_comm]
    cases hco : VV n C x C.output
    · cases hdo : VV n (mkD C n e t k s a b c) x (rh n e t k s C.output)
      · rfl
      · exfalso
        rcases hA hdo with h | h
        · rw [hco] at h; exact Bool.false_ne_true h
        · have h12 := hLRC h
          rw [hco] at h12
          exact Bool.false_ne_true h12
    · rcases hB hco with h | h
      · exact h
      · apply hLRD
        rw [hDk, hEa, hEb]
        rw [hu] at h
        revert h
        generalize VV n C x a = A
        generalize VV n C x b = B
        cases A <;> cases B <;> simp
  refine ⟨mkD C n e t k s a b c, hAOD, ?_, ?_⟩
  · funext x
    exact hsem x
  · show (mkD C n e t k s a b c).gates.length + 1 ≤ C.gates.length
    rw [hDlen]
    omega

end PEqualNP.Outside.L_meta_2774

theorem PEqualNP.Outside.L_meta_2774 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (T L : Finset ℕ) (i₁ i₂ a b c : ℕ),
  (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ PEqualNP.MetaComplexity.NestedCover.IsOrTree n C T L C.output ∧
  n + i₁ ∈ L ∧ n + i₂ ∈ L ∧ i₁ ≠ i₂ ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).inputs = [a, b] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).inputs = [b, a]) ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).inputs = [a, c] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).inputs = [c, a]) ∧
  (∀ k < C.gates.length, k ∉ T → n + i₁ ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧ n + i₂ ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧
    ∀ j ∈ T, n + j ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs)) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧
  PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧ D.size + 1 ≤ C.size := by
  rintro n C T L i₁ i₂ a b c ⟨hAO, hrb, hTree, h1L, h2L, hne, h1op, h1in, h2op, h2in, hnon⟩
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact PEqualNP.Outside.L_meta_2774.core n C T L i₁ i₂ a b c hAO hrb hTree h1L h2L h
      h1op h1in h2op h2in hnon
  · exact PEqualNP.Outside.L_meta_2774.core n C T L i₂ i₁ a c b hAO hrb hTree h2L h1L h
      h2op h2in h1op h1in (fun m hm hmT => ⟨(hnon m hm hmT).2.1, (hnon m hm hmT).1,
        (hnon m hm hmT).2.2⟩)
