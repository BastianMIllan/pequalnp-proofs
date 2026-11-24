import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2486

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

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

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

lemma W_gate' (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map (W n C x)) := by
  rw [W_gate n C x k hk]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  simp [hRB k hk i hi]

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_past (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : ¬ k < C.gates.length) :
    W n C x (n + k) = false := by
  simp only [W]
  exact getD_ge_length _ _ (by rw [wires_length]; omega)

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
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by simp [orStep, hl0])]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by simp [orStep, hl0]; omega)]
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

lemma gateAt_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k ∈ C.gates := by
  rw [gateAt_eq C k hk]
  exact List.getElem_mem hk

theorem mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (hRB : ReadsBack n C) (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, W n C x w = true → W n C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [W_input n C _ w hwn] at hw
      rw [W_input n C _ w hwn]
      exact hxy _ hw
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k < C.gates.length
      · rw [W_gate' n C hRB x k hk] at hw
        rw [W_gate' n C hRB y k hk]
        rcases hAO _ (gateAt_mem C k hk) with hop | hop
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at hw ⊢
          intro i hi
          exact ih i (hRB k hk i hi) (hw i hi)
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at hw ⊢
          obtain ⟨i, hi, hv⟩ := hw
          exact ⟨i, hi, ih i (hRB k hk i hi) hv⟩
      · rw [W_past n C x k hk] at hw
        exact absurd hw Bool.false_ne_true

theorem orReach (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (x : Fin n → Bool) :
    ∀ b j : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C b j → W n C x (n + j) = true →
      W n C x b = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro j hr hv
    obtain ⟨hnb, hmem⟩ := hr
    obtain ⟨k, rfl⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    rw [show n + k - n = k by omega] at hmem
    by_cases hk : k < C.gates.length
    · rcases (orSets_mem_iff n C k j hk).1 hmem with rfl | ⟨hop, w, hw, hnw, hwlt, hj⟩
      · exact hv
      · have hW := ih w hwlt j ⟨hnw, hj⟩ hv
        rw [W_gate' n C hRB x k hk, hop]
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
        exact ⟨w, hw, hW⟩
    · exfalso
      have hl : (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
        simp [PEqualNP.CleanedNonEdge.orSets, orFold_length]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hmem
      simp at hmem

theorem andGate (n : ℕ) (C : Circuit) (hAO2 : PEqualNP.TopForm.IsAO2 n C) (x : Fin n → Bool)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    W n C x (n + j) = (W n C x ((gateAt C j).inputs.getD 0 0) &&
      W n C x ((gateAt C j).inputs.getD 1 0)) := by
  have hlen := hAO2.2.2 _ (gateAt_mem C j hj)
  rw [W_gate' n C hAO2.2.1 x j hj, hop]
  generalize (gateAt C j).inputs = l at hlen ⊢
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  all_goals first | (simp at hlen; done) | simp [GateOp.eval]

theorem reachUp (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (x2 : Fin n → Bool) (a b : ℕ)
    (hab : (∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ PEqualNP.TopForm.orIn n C b) ∨
      (∃ j_1 : ℕ, a = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C b j_1))
    (hv : W n C x2 a = true) : W n C x2 b = true := by
  rcases hab with ⟨i, rfl, hi⟩ | ⟨j, rfl, hr⟩
  · simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases hi with hib | ⟨k, hk, hr, hop, hik⟩
    · rw [← hib]
      exact hv
    · have hk1 : W n C x2 (n + k) = true := by
        rw [W_gate' n C hRB x2 k hk, hop]
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
        exact ⟨i, hik, hv⟩
      exact orReach n C hRB x2 b k hr hk1
  · exact orReach n C hRB x2 b j hr hv

theorem chain (n : ℕ) (C : Circuit) (hAO2 : PEqualNP.TopForm.IsAO2 n C) (h V F2 j2 : ℕ)
    (x xl z : Fin n → Bool) (hxz : ∀ i : Fin n, x i = true → z i = true)
    (hlz : ∀ i : Fin n, xl i = true → z i = true)
    (hreach : (∃ i_1 : Fin n, i_1.val = h ∧ i_1 ∈ PEqualNP.TopForm.orIn n C V) ∨
      (∃ j_1 : ℕ, h = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C V j_1))
    (hj2 : j2 < C.gates.length ∧ (gateAt C j2).op = GateOp.and ∧
      ((gateAt C j2).inputs = [V, F2] ∨ (gateAt C j2).inputs = [F2, V]))
    (hout : PEqualNP.CleanedNonEdge.OrReaches n C C.output j2)
    (hv : W n C x h = true) (hF : W n C xl F2 = true) :
    PEqualNP.MetaComplexity.circuitFun n C z = true := by
  obtain ⟨hAO, hRB, h3⟩ := hAO2
  have hhz : W n C z h = true := mono n C hAO hRB x z hxz h hv
  have hVz : W n C z V = true := reachUp n C hRB z h V hreach hhz
  have hFz : W n C z F2 = true := mono n C hAO hRB xl z hlz F2 hF
  have hA : W n C z (n + j2) = true := by
    rw [andGate n C ⟨hAO, hRB, h3⟩ z j2 hj2.1 hj2.2.1]
    rcases hj2.2.2 with hi | hi <;> rw [hi] <;> simp [hVz, hFz]
  exact orReach n C hRB z C.output j2 hout hA

end PEqualNP.Outside.L_meta_2486

theorem PEqualNP.Outside.L_meta_2486 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (l : Fin M) (h V F2 j2 : ℕ), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_3 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_3 l_3) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → ((∃ i_1 : Fin n, i_1.val = h ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (V)) ∨ (∃ j_1 : ℕ, h = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V) j_1)) → (j2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j2).inputs = [V, F2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).inputs = [F2, V])) → PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j2 → l ∈ {a_1 | PEqualNP.CleanedNonEdge.wireVal n C (F2) (fun k_2 : Fin n => decide (k_2.val = lw a_1)) = true} → {p_4 | ∃ m_1, ¬ I p_4 m_1 ∧ PEqualNP.CleanedNonEdge.wireVal n C (h) (fun k_3 : Fin n => decide (k_3.val ∈ ({pw p_4, lw m_1} : Finset ℕ))) = true} ⊆ {p_5 | I p_5 l} := by
  intro n N M pw lw I C l h V F2 j2 hAO2 _hinj hsound hreach hj2 hout hl p hp
  obtain ⟨m, hm, hv⟩ := hp
  by_contra hpl
  have hpl' : ¬ I p l := hpl
  have hfalse := hsound {p} {m, l} (by simp) ((Finset.card_insert_le m {l}).trans (by simp))
    (by
      intro p3 hp3 l3 hl3
      rw [Finset.mem_singleton] at hp3
      subst hp3
      rw [Finset.mem_insert, Finset.mem_singleton] at hl3
      rcases hl3 with rfl | rfl
      exacts [hm, hpl'])
  have hc := PEqualNP.Outside.L_meta_2486.chain n C hAO2 h V F2 j2
    (fun k_3 : Fin n => decide (k_3.val ∈ ({pw p, lw m} : Finset ℕ)))
    (fun k_2 : Fin n => decide (k_2.val = lw l))
    (fun k_1 : Fin n => decide (k_1.val ∈ ({p} : Finset (Fin N)).image pw ∪ ({m, l} : Finset (Fin M)).image lw))
    (by
      intro i hi
      simp only [decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with hi | hi <;> simp [hi])
    (by
      intro i hi
      simp only [decide_eq_true_eq] at hi
      simp [hi])
    hreach hj2 hout hv hl
  exact absurd (hc.symm.trans hfalse) (by decide)
