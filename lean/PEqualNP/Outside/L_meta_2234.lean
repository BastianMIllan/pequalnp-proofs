import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2234

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

open PEqualNP.TopForm

lemma orIn_sub {n : ℕ} {C : Circuit} {w i : ℕ} (h : OrReaches n C w i) :
    orIn n C (n + i) ⊆ orIn n C w := by
  intro u hu
  exact reach_mem_orIn u ((orReaches_reach i w h).1.trans (mem_orIn_reach u hu))

lemma refl_of_lt {n : ℕ} {C : Circuit} {w v : ℕ} (hw : w < n)
    (h : Relation.ReflTransGen (OrStep n C) w v) : v = w := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hs, _⟩
  · exact h.symm
  · obtain ⟨k, _, hk, _⟩ := hs
    omega

lemma orIn_small {n : ℕ} {C : Circuit} {w : ℕ} (hw : w < n) : (orIn n C w).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have h1 := refl_of_lt hw (mem_orIn_reach a ha)
  have h2 := refl_of_lt hw (mem_orIn_reach b hb)
  exact Fin.ext (by omega)

open Classical in
def U (n : ℕ) (C : Circuit) (Rt : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun b => ∃ r ∈ Rt, b ∈ orIn n C r)

open Classical in
noncomputable def Sv (n : ℕ) (C : Circuit) (Rt : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun i => (gateAt C i).op = GateOp.or ∧
    2 ≤ (orIn n C (n + i)).card ∧ ∃ r ∈ Rt, OrReaches n C r i)

lemma dag (n : ℕ) (C : Circuit) (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) :
    ∀ N, ∀ Rt : Finset ℕ, (∀ r ∈ Rt, r < N) → (U n C Rt).card ≤ (Sv n C Rt).card + Rt.card := by
  intro N
  induction N with
  | zero =>
    intro Rt hR
    have : Rt = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun r hr => absurd (hR r hr) (Nat.not_lt_zero r))
    subst this
    simp [U]
  | succ N ih =>
    intro Rt hR
    by_cases hN : N ∈ Rt
    swap
    · refine ih Rt (fun r hr => ?_)
      have h1 := hR r hr
      have h3 : r ≠ N := fun h => hN (h ▸ hr)
      omega
    have hR0 : ∀ r ∈ Rt.erase N, r < N := by
      intro r hr
      rw [Finset.mem_erase] at hr
      have := hR r hr.2
      omega
    have hcard : (Rt.erase N).card + 1 = Rt.card := Finset.card_erase_add_one hN
    have hUsplit : U n C Rt ⊆ U n C (Rt.erase N) ∪ orIn n C N := by
      intro b hb
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      obtain ⟨r, hr, hbr⟩ := hb
      by_cases hrN : r = N
      · subst hrN
        exact Finset.mem_union_right _ hbr
      · apply Finset.mem_union_left
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨r, Finset.mem_erase.mpr ⟨hrN, hr⟩, hbr⟩
    have hSv0 : Sv n C (Rt.erase N) ⊆ Sv n C Rt := by
      intro i hi
      simp only [Sv, Finset.mem_filter] at hi ⊢
      obtain ⟨h1, h2', h3, r, hr, h4⟩ := hi
      exact ⟨h1, h2', h3, r, Finset.mem_of_mem_erase hr, h4⟩
    by_cases hsmall : (orIn n C N).card ≤ 1
    · have a1 := Finset.card_le_card hUsplit
      have a2 := Finset.card_union_le (U n C (Rt.erase N)) (orIn n C N)
      have a3 := ih (Rt.erase N) hR0
      have a4 := Finset.card_le_card hSv0
      omega
    · replace hsmall := not_le.mp hsmall
      obtain ⟨u, hu⟩ : (orIn n C N).Nonempty := Finset.card_pos.mp (by omega)
      have hNn : n ≤ N := by
        by_contra hlt
        replace hlt := not_le.mp hlt
        have := orIn_small (C := C) hlt
        omega
      have hr := mem_orIn_reach u hu
      rcases Relation.ReflTransGen.cases_head hr with he | ⟨c, hs, _⟩
      · exfalso
        have := u.isLt
        omega
      obtain ⟨k, hk, hNk, hop, _, _⟩ := hs
      have hIkc : ((gateAt C k).inputs.toFinset.filter (fun w => w < n + k)).card ≤ 2 := by
        calc ((gateAt C k).inputs.toFinset.filter (fun w => w < n + k)).card
            ≤ (gateAt C k).inputs.toFinset.card := Finset.card_filter_le _ _
          _ ≤ (gateAt C k).inputs.length := List.toFinset_card_le _
          _ = 2 := h2 _ (gateAt_mem hk)
      have hR' : ∀ r ∈ Rt.erase N ∪ (gateAt C k).inputs.toFinset.filter (fun w => w < n + k),
          r < N := by
        intro r hr
        rcases Finset.mem_union.mp hr with hr | hr
        · exact hR0 r hr
        · rw [Finset.mem_filter] at hr
          omega
      have a3 := ih _ hR'
      have hU' : U n C Rt ⊆
          U n C (Rt.erase N ∪ (gateAt C k).inputs.toFinset.filter (fun w => w < n + k)) := by
        intro b hb
        rcases Finset.mem_union.mp (hUsplit hb) with hb | hb
        · simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
          obtain ⟨r, hr, h⟩ := hb
          exact ⟨r, Finset.mem_union_left _ hr, h⟩
        · have hrb := mem_orIn_reach b hb
          rcases Relation.ReflTransGen.cases_head hrb with he | ⟨c, hs, hrest⟩
          · exfalso
            have := b.isLt
            omega
          obtain ⟨k', hk', hNk', hop', hin', hlt'⟩ := hs
          have hkk : k' = k := by omega
          rw [hkk] at hin' hlt'
          simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨c, Finset.mem_union_right _ ?_, reach_mem_orIn b hrest⟩
          rw [Finset.mem_filter, List.mem_toFinset]
          exact ⟨hin', hlt'⟩
      have hS' : insert k (Sv n C (Rt.erase N ∪
          (gateAt C k).inputs.toFinset.filter (fun w => w < n + k))) ⊆ Sv n C Rt := by
        intro i hi
        rcases Finset.mem_insert.mp hi with hik | hi
        · rw [hik]
          simp only [Sv, Finset.mem_filter, Finset.mem_range]
          refine ⟨hk, hop, ?_, N, hN, ?_⟩
          · rw [← hNk]
            omega
          · rw [hNk]
            exact (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩
        · simp only [Sv, Finset.mem_filter] at hi ⊢
          obtain ⟨h1, h2', h3, r, hr, h4⟩ := hi
          rcases Finset.mem_union.mp hr with hr | hr
          · exact ⟨h1, h2', h3, r, Finset.mem_of_mem_erase hr, h4⟩
          · rw [Finset.mem_filter, List.mem_toFinset] at hr
            refine ⟨h1, h2', h3, N, hN, ?_⟩
            rw [hNk]
            exact (orReaches_iff n C k i).mpr ⟨hk, Or.inr ⟨hop, r, hr.1, hr.2, h4⟩⟩
      have hkn : k ∉ Sv n C (Rt.erase N ∪
          (gateAt C k).inputs.toFinset.filter (fun w => w < n + k)) := by
        intro hi
        simp only [Sv, Finset.mem_filter] at hi
        obtain ⟨_, _, _, r, hr, h4⟩ := hi
        have h5 := orStep_le (orReaches_reach k r h4).1
        have h6 := hR' r hr
        omega
      have a1 := Finset.card_le_card hU'
      have a2 := Finset.card_le_card hS'
      rw [Finset.card_insert_of_notMem hkn] at a2
      have a5 := Finset.card_union_le (Rt.erase N)
        ((gateAt C k).inputs.toFinset.filter (fun w => w < n + k))
      omega

def Fc {n : ℕ} (F : Finset ℕ) (ctr : ℕ → Fin n) (c : Fin n) : Finset ℕ :=
  F.filter (fun j => ctr j = c)

noncomputable def Sc (n : ℕ) (C : Circuit) (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ) (c : Fin n) :
    Finset ℕ :=
  Sv n C ((Fc F ctr c).image lf)

theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) → (∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or → 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card → (∃ j1 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j1) i) → ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output i) ∧ ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  intro n G _ C F ctr lf h4 hAO hw1 hF
  refine ⟨?_, ?_⟩
  · intro i _ _ hc _ hout
    obtain ⟨u, hu⟩ : (orIn n C (n + i)).Nonempty := Finset.card_pos.mp (by omega)
    have hr := (orReaches_reach i C.output hout).1.trans (mem_orIn_reach u hu)
    have hv := reach_var_val (fun k1 => decide (k1 = u)) C.output u hr (by simp)
    have h' : PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = u)) = true := hv
    rw [hw1 u] at h'
    exact absurd h' (by decide)
  · have hA : ∀ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧
        b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤
        (Sc n C F ctr lf c).card + (Fc F ctr c).card := by
      intro c
      have hsub : Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧
          b2 ∈ PEqualNP.TopForm.orIn n C (lf j2)) ⊆ U n C ((Fc F ctr c).image lf) := by
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        obtain ⟨j, hj, hc, hb⟩ := hb
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨lf j, Finset.mem_image_of_mem _ ?_, hb⟩
        simp only [Fc, Finset.mem_filter]
        exact ⟨hj, hc⟩
      have h1 := dag n C hAO.2.2 (((Fc F ctr c).image lf).sup id + 1) ((Fc F ctr c).image lf)
        (fun r hr => Nat.lt_succ_of_le (Finset.le_sup (f := id) hr))
      have h2 := Finset.card_le_card hsub
      have h3 : ((Fc F ctr c).image lf).card ≤ (Fc F ctr c).card := Finset.card_image_le
      have h5 : Sc n C F ctr lf c = Sv n C ((Fc F ctr c).image lf) := rfl
      rw [h5]
      omega
    have hB : ∀ c ∈ (Finset.univ : Finset (Fin n)), ∀ c' ∈ (Finset.univ : Finset (Fin n)),
        c ≠ c' → Disjoint (Sc n C F ctr lf c) (Sc n C F ctr lf c') := by
      intro c _ c' _ hne
      rw [Finset.disjoint_left]
      intro i hi hi'
      simp only [Sc, Sv, Finset.mem_filter] at hi hi'
      obtain ⟨_, _, hc2, r, hr, hreach⟩ := hi
      obtain ⟨_, _, _, r', hr', hreach'⟩ := hi'
      obtain ⟨j, hjF, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨j', hjF', rfl⟩ := Finset.mem_image.mp hr'
      simp only [Fc, Finset.mem_filter] at hjF hjF'
      have hsub : orIn n C (n + i) ⊆ Finset.univ.filter (fun w => G.Adj c w ∧ G.Adj c' w) := by
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · rw [← hjF.2]
          exact hF j hjF.1 b (orIn_sub hreach hb)
        · rw [← hjF'.2]
          exact hF j' hjF'.1 b (orIn_sub hreach' hb)
      have e1 := Finset.card_le_card hsub
      have e2 := h4 c c' hne
      omega
    have hD : ((Finset.univ : Finset (Fin n)).biUnion (Sc n C F ctr lf)).card ≤
        Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧
          2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, OrReaches n C (lf j3) i2} := by
      rw [← Set.ncard_coe_finset]
      apply Set.ncard_le_ncard
      · intro i hi
        rw [Finset.mem_coe, Finset.mem_biUnion] at hi
        obtain ⟨c, _, hi⟩ := hi
        simp only [Sc, Sv, Finset.mem_filter, Finset.mem_range] at hi
        obtain ⟨h1, h2, h3, r, hr, h5⟩ := hi
        obtain ⟨j, hjF, rfl⟩ := Finset.mem_image.mp hr
        simp only [Fc, Finset.mem_filter] at hjF
        simp only [Set.mem_setOf_eq]
        exact ⟨h1, h2, h3, j, hjF.1, h5⟩
      · exact (Set.finite_lt_nat C.gates.length).subset (fun i hi => hi.1)
    have e2 : ((Finset.univ : Finset (Fin n)).biUnion (Sc n C F ctr lf)).card =
        ∑ c : Fin n, (Sc n C F ctr lf c).card :=
      Finset.card_biUnion (by
        intro x _ y _ hxy
        exact hB x (Finset.mem_univ _) y (Finset.mem_univ _) hxy)
    have e3 : F.card = ∑ c : Fin n, (Fc F ctr c).card :=
      Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_univ (ctr j))
    have e1 : ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧
        b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤
        ∑ c : Fin n, ((Sc n C F ctr lf c).card + (Fc F ctr c).card) :=
      Finset.sum_le_sum (fun c _ => hA c)
    rw [Finset.sum_add_distrib] at e1
    omega

end PEqualNP.Outside.L_meta_2234

theorem PEqualNP.Outside.L_meta_2234 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) → (∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or → 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card → (∃ j1 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j1) i) → ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output i) ∧ ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card :=
  PEqualNP.Outside.L_meta_2234.main
