import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2479

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

open PEqualNP.CleanedNonEdge in
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩

open PEqualNP.CleanedNonEdge in
lemma orSets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp only [orSets]
  rw [orFold_length]
  simp

-- an OR gate with a true input below it is true
lemma or_true (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C k).inputs)
    (hlt : i < n + k) (hv : W n C x i = true) : W n C x (n + k) = true := by
  rw [W_gate n C x k hk, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  exact ⟨i, hi, by simp only [hlt, ite_true]; exact hv⟩

open PEqualNP.CleanedNonEdge in
lemma orReach (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    ∀ w j : ℕ, OrReaches n C w j → W n C x (n + j) = true → W n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro j hr hv
    obtain ⟨hn, hmem⟩ := hr
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    rw [show n + k - n = k by omega] at hmem
    by_cases hk : k < C.gates.length
    · rcases (orSets_mem_iff n C k j hk).1 hmem with h | ⟨hop, w', hw', hn', hlt, hx⟩
      · subst h; exact hv
      · have hw'v : W n C x w' = true := ih w' hlt j ⟨hn', hx⟩ hv
        exact or_true n C x k hk hop w' hw' hlt hw'v
    · exfalso
      have hlen := orSets_length n C
      have : (orSets n C).getD k [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      rw [this] at hmem
      simp at hmem

open PEqualNP.CleanedNonEdge in
lemma toV (n : ℕ) (C : Circuit) (x : Fin n → Bool) (V h : ℕ)
    (H : (∃ i_1 : Fin n, i_1.val = h ∧ i_1 ∈ PEqualNP.TopForm.orIn n C V) ∨
      (∃ j_1 : ℕ, h = n + j_1 ∧ OrReaches n C V j_1))
    (hh : W n C x h = true) : W n C x V = true := by
  rcases H with ⟨i, rfl, hi⟩ | ⟨j, rfl, hr⟩
  · simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases hi with h1 | ⟨k, hk, hr, hop, hin⟩
    · rw [← h1]; exact hh
    · have hk' : W n C x (n + k) = true :=
        or_true n C x k hk hop i hin (by have := i.isLt; omega) hh
      exact orReach n C x V k hr hk'
  · exact orReach n C x V j hr hh

lemma andGate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hRB : ReadsBack n C) (j a b : ℕ)
    (H : j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      ((gateAt C j).inputs = [a, b] ∨ (gateAt C j).inputs = [b, a]))
    (ha : W n C x a = true) (hb : W n C x b = true) : W n C x (n + j) = true := by
  obtain ⟨hj, hop, hin⟩ := H
  have ha' : a < n + j := hRB j hj a (by rcases hin with h | h <;> simp [h])
  have hb' : b < n + j := hRB j hj b (by rcases hin with h | h <;> simp [h])
  rw [W_gate n C x j hj, hop]
  rcases hin with h | h <;> simp [h, GateOp.eval, ha', hb', ha, hb]

lemma cf (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = W n C x C.output := rfl

lemma wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) :
    PEqualNP.CleanedNonEdge.wireVal n C w x = W n C x w := rfl

end PEqualNP.Outside.L_meta_2479

theorem PEqualNP.Outside.L_meta_2479 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → (∀ (j K F : ℕ), (j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [K, F] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [F, K])) → PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j → (∀ z_1 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (K) z_1 = true → PEqualNP.CleanedNonEdge.wireVal n C (F) z_1 = true → PEqualNP.CleanedNonEdge.wireVal n C (F) z_1 = true → PEqualNP.MetaComplexity.circuitFun n C z_1 = true)) ∧ (∀ (j1 j2 K1 F1 V F2 h : ℕ), (j1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j1).inputs = [K1, F1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j1).inputs = [F1, K1])) → PEqualNP.CleanedNonEdge.OrReaches n C (h) j1 → ((∃ i_1 : Fin n, i_1.val = h ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (V)) ∨ (∃ j_1 : ℕ, h = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V) j_1)) → (j2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j2).inputs = [V, F2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).inputs = [F2, V])) → PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j2 → (∀ z_2 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (K1) z_2 = true → PEqualNP.CleanedNonEdge.wireVal n C (F1) z_2 = true → PEqualNP.CleanedNonEdge.wireVal n C (F2) z_2 = true → PEqualNP.MetaComplexity.circuitFun n C z_2 = true) ∧ (∀ z_3 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (h) z_3 = true → PEqualNP.CleanedNonEdge.wireVal n C (F2) z_3 = true → PEqualNP.CleanedNonEdge.wireVal n C (F2) z_3 = true → PEqualNP.MetaComplexity.circuitFun n C z_3 = true)) ∧ (∀ (j3 j4 F3 F4 U K2 : ℕ), (j3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j3).inputs = [F3, F4] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j3).inputs = [F4, F3])) → PEqualNP.CleanedNonEdge.OrReaches n C (U) j3 → (j4 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j4).inputs = [K2, U] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j4).inputs = [U, K2])) → PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j4 → (∀ z_4 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (K2) z_4 = true → PEqualNP.CleanedNonEdge.wireVal n C (F3) z_4 = true → PEqualNP.CleanedNonEdge.wireVal n C (F4) z_4 = true → PEqualNP.MetaComplexity.circuitFun n C z_4 = true) ∧ (∀ z_5 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (K2) z_5 = true → PEqualNP.CleanedNonEdge.wireVal n C (U) z_5 = true → PEqualNP.CleanedNonEdge.wireVal n C (U) z_5 = true → PEqualNP.MetaComplexity.circuitFun n C z_5 = true)) := by
  intro n C hAO
  have hRB := hAO.2.1
  simp only [PEqualNP.Outside.L_meta_2479.wv, PEqualNP.Outside.L_meta_2479.cf]
  refine ⟨?_, ?_, ?_⟩
  · intro j K F H hr z hK hF _
    exact PEqualNP.Outside.L_meta_2479.orReach n C z _ j hr
      (PEqualNP.Outside.L_meta_2479.andGate n C z hRB j K F H hK hF)
  · intro j1 j2 K1 F1 V F2 h H1 hr1 Hv H2 hr2
    refine ⟨?_, ?_⟩
    · intro z hK hF1 hF2
      have hh := PEqualNP.Outside.L_meta_2479.orReach n C z h j1 hr1
        (PEqualNP.Outside.L_meta_2479.andGate n C z hRB j1 K1 F1 H1 hK hF1)
      have hV := PEqualNP.Outside.L_meta_2479.toV n C z V h Hv hh
      exact PEqualNP.Outside.L_meta_2479.orReach n C z _ j2 hr2
        (PEqualNP.Outside.L_meta_2479.andGate n C z hRB j2 V F2 H2 hV hF2)
    · intro z hh hF2 _
      exact PEqualNP.Outside.L_meta_2479.orReach n C z _ j2 hr2
        (PEqualNP.Outside.L_meta_2479.andGate n C z hRB j2 V F2 H2
          (PEqualNP.Outside.L_meta_2479.toV n C z V h Hv hh) hF2)
  · intro j3 j4 F3 F4 U K2 H3 hr3 H4 hr4
    refine ⟨?_, ?_⟩
    · intro z hK hF3 hF4
      have hU := PEqualNP.Outside.L_meta_2479.orReach n C z U j3 hr3
        (PEqualNP.Outside.L_meta_2479.andGate n C z hRB j3 F3 F4 H3 hF3 hF4)
      exact PEqualNP.Outside.L_meta_2479.orReach n C z _ j4 hr4
        (PEqualNP.Outside.L_meta_2479.andGate n C z hRB j4 K2 U H4 hK hU)
    · intro z hK hU _
      exact PEqualNP.Outside.L_meta_2479.orReach n C z _ j4 hr4
        (PEqualNP.Outside.L_meta_2479.andGate n C z hRB j4 K2 U H4 hK hU)
