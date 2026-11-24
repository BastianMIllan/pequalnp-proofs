import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_2235.P2230

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

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

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

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

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

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

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

def stepR {β : Type} (F : Gate → List β → β) (d : β) (R : List β) (g : Gate) : List β :=
  R ++ [F g (g.inputs.map fun i => R.getD i d)]

lemma R_length {β : Type} (F : Gate → List β → β) (d : β) (gs : List Gate) (w : List β) :
    (gs.foldl (stepR F d) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepR]
    omega

lemma R_getD_lt {β : Type} (F : Gate → List β → β) (d : β) (gs : List Gate) (w : List β)
    (i : ℕ) (hi : i < w.length) :
    (gs.foldl (stepR F d) w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepR F d w g).length := by simp [stepR]; omega
    rw [ih (stepR F d w g) hlt]
    simp [stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma R_getD_ge {β : Type} (d : β) (w : List β) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma R_getD_gate {β : Type} (F : Gate → List β → β) (d : β) (gs : List Gate) (w : List β)
    (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (stepR F d) w).getD (w.length + j) d =
      F (gs[j]) ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl (stepR F d) w).getD i d else d) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepR F d w g).length := by simp [stepR]
      rw [Nat.add_zero, R_getD_lt F d gs (stepR F d w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepR F d w g).getD w.length d =
          F g (g.inputs.map fun i => w.getD i d) := by
        simp [stepR, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, R_getD_lt F d gs (stepR F d w g) i (by simp [stepR]; omega)]
        simp [stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact R_getD_ge d w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepR F d w g) j hj'
      have hl : (stepR F d w g).length = w.length + 1 := by simp [stepR]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def FR (S : List ℕ) (k : ℕ) (g : Gate) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl PEqualNP.ReadK.insertNew acc) []
  | GateOp.and => ins.foldl (PEqualNP.ReadK.andStep k) [S.map fun _ => 0]
  | _ => []

lemma rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    PEqualNP.ReadK.readVectors C n S k =
      C.gates.foldl (stepR (FR S k) []) ((List.range n).map (PEqualNP.ReadK.leafVectors S k)) :=
  rfl

def vecs (C : Circuit) (n : ℕ) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
  (PEqualNP.ReadK.readVectors C n S 1).getD w []

lemma vecs_input (C : Circuit) (n : ℕ) (S : List ℕ) (w : ℕ) (hw : w < n) :
    vecs C n S w = PEqualNP.ReadK.leafVectors S 1 w := by
  unfold vecs
  rw [rv_eq, R_getD_lt _ _ _ _ _ (by simp; exact hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma vecs_ge (C : Circuit) (n : ℕ) (S : List ℕ) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    vecs C n S w = [] := by
  unfold vecs
  rw [rv_eq]
  apply R_getD_ge
  rw [R_length]
  simp
  omega

lemma vecs_gate (C : Circuit) (n : ℕ) (S : List ℕ) (j : ℕ) (hj : j < C.gates.length) :
    vecs C n S (n + j) = FR S 1 (gateAt C j) ((gateAt C j).inputs.map fun i =>
      if i < n + j then vecs C n S i else []) := by
  unfold vecs
  rw [rv_eq, gateAt_eq hj]
  have := R_getD_gate (FR S 1) [] C.gates ((List.range n).map (PEqualNP.ReadK.leafVectors S 1)) j hj
  simp only [List.length_map, List.length_range] at this
  exact this

lemma mem_ins_foldl (L acc : List (List ℕ)) (v : List ℕ) :
    v ∈ L.foldl PEqualNP.ReadK.insertNew acc ↔ v ∈ acc ∨ v ∈ L := by
  induction L generalizing acc with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons, ih]
    unfold PEqualNP.ReadK.insertNew
    split_ifs with h
    · simp only [List.mem_cons]
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | rfl | h1)
        · exact Or.inl h1
        · exact Or.inl h
        · exact Or.inr h1
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      tauto

lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) :
    v ∈ PEqualNP.ReadK.andStep k A B ↔ ∃ u ∈ A, ∃ w ∈ B, PEqualNP.ReadK.capAdd k u w = v := by
  unfold PEqualNP.ReadK.andStep
  rw [mem_ins_foldl]
  simp [List.mem_flatMap]

def Good (n : ℕ) (C : Circuit) (a b : ℕ) (w : ℕ) (v : List ℕ) : Prop :=
  ∃ p q, v = [p, q] ∧ 1 ≤ p + q ∧ (p ≤ 1 → q ≤ 1 →
    (p = 1 → q = 0 → Relation.ReflTransGen (OrStep n C) w a) ∧
    (p = 0 → q = 1 → Relation.ReflTransGen (OrStep n C) w b) ∧
    (p = 1 → q = 1 → ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      Relation.ReflTransGen (OrStep n C) w (n + j) ∧
      ((Relation.ReflTransGen (OrStep n C) (PEqualNP.TopForm.opnd C j 0) a ∧
        Relation.ReflTransGen (OrStep n C) (PEqualNP.TopForm.opnd C j 1) b) ∨
       (Relation.ReflTransGen (OrStep n C) (PEqualNP.TopForm.opnd C j 0) b ∧
        Relation.ReflTransGen (OrStep n C) (PEqualNP.TopForm.opnd C j 1) a))))

lemma good_all (n : ℕ) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C) (a b : ℕ)
    (hab : a ≠ b) : ∀ w, ∀ v ∈ vecs C n [a, b] w, Good n C a b w v := by
  obtain ⟨hAnd, hRB, h2⟩ := hAO
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    by_cases hw : w < n
    · rw [vecs_input C n _ w hw] at hv
      unfold PEqualNP.ReadK.leafVectors at hv
      split_ifs at hv with hmem
      · simp only [List.mem_singleton] at hv
        subst hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · refine ⟨1, 0, by simp [hab, Ne.symm hab], by norm_num, ?_⟩
          intro _ _
          refine ⟨fun _ _ => Relation.ReflTransGen.refl, fun h _ => absurd h (by norm_num),
            fun _ h => absurd h (by norm_num)⟩
        · refine ⟨0, 1, by simp [hab, Ne.symm hab], by norm_num, ?_⟩
          intro _ _
          refine ⟨fun _ h => absurd h (by norm_num), fun _ _ => Relation.ReflTransGen.refl,
            fun h _ => absurd h (by norm_num)⟩
      · simp at hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [vecs_ge C n _ w hlen] at hv
        simp at hv
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hj))
        have hp : p < n + j := hRB j hj p (by rw [hin]; simp)
        have hq : q < n + j := hRB j hj q (by rw [hin]; simp)
        have e0 : PEqualNP.TopForm.opnd C j 0 = p := by simp [PEqualNP.TopForm.opnd, hin]
        have e1 : PEqualNP.TopForm.opnd C j 1 = q := by simp [PEqualNP.TopForm.opnd, hin]
        rw [vecs_gate C n _ j hj, hin] at hv
        simp only [List.map_cons, List.map_nil, if_pos hp, if_pos hq] at hv
        rcases hAnd _ (gateAt_mem hj) with hop | hop
        · -- an AND gate
          have hv' : v ∈ PEqualNP.ReadK.andStep 1 (PEqualNP.ReadK.andStep 1 [[0, 0]] (vecs C n [a, b] p))
              (vecs C n [a, b] q) := by
            simpa [FR, hop] using hv
          rw [mem_andStep] at hv'
          obtain ⟨u, hu, z, hz, rfl⟩ := hv'
          rw [mem_andStep] at hu
          obtain ⟨y, hy, u', hu', rfl⟩ := hu
          simp only [List.mem_singleton] at hy
          subst hy
          obtain ⟨u0, u1, rfl, hus, cu⟩ := ih p hp u' hu'
          obtain ⟨w0, w1, rfl, hws, cw⟩ := ih q hq z hz
          refine ⟨min (min u0 2 + w0) 2, min (min u1 2 + w1) 2,
            by simp [PEqualNP.ReadK.capAdd], by omega, ?_⟩
          intro hA hB
          refine ⟨fun x y => by omega, fun x y => by omega, fun x y => ?_⟩
          refine ⟨j, hj, hop, Relation.ReflTransGen.refl, ?_⟩
          rw [e0, e1]
          rcases (by omega : (u0 = 1 ∧ u1 = 0 ∧ w0 = 0 ∧ w1 = 1) ∨
              (u0 = 0 ∧ u1 = 1 ∧ w0 = 1 ∧ w1 = 0)) with ⟨f1, f2, f3, f4⟩ | ⟨f1, f2, f3, f4⟩
          · left
            exact ⟨(cu (by omega) (by omega)).1 f1 f2, (cw (by omega) (by omega)).2.1 f3 f4⟩
          · right
            exact ⟨(cu (by omega) (by omega)).2.1 f1 f2, (cw (by omega) (by omega)).1 f3 f4⟩
        · -- an OR gate
          have hv' : v ∈ vecs C n [a, b] p ∨ v ∈ vecs C n [a, b] q := by
            simpa [FR, hop, mem_ins_foldl] using hv
          have lift : ∀ r, r ∈ (gateAt C j).inputs → r < n + j → v ∈ vecs C n [a, b] r →
              Good n C a b (n + j) v := by
            intro r hrin hr hvr
            have step : OrStep n C (n + j) r := ⟨j, hj, rfl, hop, hrin, hr⟩
            obtain ⟨p0, q0, rfl, hs, hc⟩ := ih r hr v hvr
            refine ⟨p0, q0, rfl, hs, fun h1 h2 => ?_⟩
            obtain ⟨c1, c2, c3⟩ := hc h1 h2
            refine ⟨fun x y => Relation.ReflTransGen.head step (c1 x y),
              fun x y => Relation.ReflTransGen.head step (c2 x y), fun x y => ?_⟩
            obtain ⟨j', h1', h2', h3', h4'⟩ := c3 x y
            exact ⟨j', h1', h2', Relation.ReflTransGen.head step h3', h4'⟩
          rcases hv' with h | h
          · exact lift p (by rw [hin]; simp) hp h
          · exact lift q (by rw [hin]; simp) hq h

end PEqualNP.Outside.L_meta_2235.P2230

namespace PEqualNP.Outside.L_meta_2235.Q2230

theorem sib_main : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin n), PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → a < b → PEqualNP.ReadK.readsAtMost C n [a.val, b.val] 1 = true → ∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j ∧ ((a ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ b ∈ PEqualNP.TopForm.side (n := n) C j 1) ∨ (b ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ a ∈ PEqualNP.TopForm.side (n := n) C j 1)) := by
  intro n C a b hAO h1 hlt hr
  have hab : a.val ≠ b.val := by
    have := Fin.lt_def.mp hlt
    omega
  unfold PEqualNP.ReadK.readsAtMost at hr
  rw [List.any_eq_true] at hr
  obtain ⟨v, hv, hall⟩ := hr
  change v ∈ PEqualNP.Outside.L_meta_2235.P2230.vecs C n [a.val, b.val] C.output at hv
  obtain ⟨p, q, rfl, hs, hc⟩ :=
    PEqualNP.Outside.L_meta_2235.P2230.good_all n C hAO a.val b.val hab C.output v hv
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hall
  obtain ⟨c1, c2, c3⟩ := hc hall.1 hall.2
  rcases (by omega : (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 1)) with
    ⟨f1, f2⟩ | ⟨f1, f2⟩ | ⟨f1, f2⟩
  · exfalso
    have hv1 := PEqualNP.Outside.L_meta_2235.P2230.reach_var_val (n := n) (C := C)
      (fun k1 => decide (k1 = a)) C.output a (c1 f1 f2) (by simp)
    have h2 : PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a)) = true := hv1
    rw [h1 a] at h2
    exact Bool.false_ne_true h2
  · exfalso
    have hv1 := PEqualNP.Outside.L_meta_2235.P2230.reach_var_val (n := n) (C := C)
      (fun k1 => decide (k1 = b)) C.output b (c2 f1 f2) (by simp)
    have h2 : PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = b)) = true := hv1
    rw [h1 b] at h2
    exact Bool.false_ne_true h2
  · obtain ⟨j, hj, hop, hR, hsd⟩ := c3 f1 f2
    refine ⟨j, hj, hop, PEqualNP.Outside.L_meta_2235.P2230.reach_orReaches hR j rfl hj, ?_⟩
    simp only [PEqualNP.TopForm.side]
    rcases hsd with ⟨x, y⟩ | ⟨x, y⟩
    · left
      exact ⟨PEqualNP.Outside.L_meta_2235.P2230.reach_mem_orIn a x,
        PEqualNP.Outside.L_meta_2235.P2230.reach_mem_orIn b y⟩
    · right
      exact ⟨PEqualNP.Outside.L_meta_2235.P2230.reach_mem_orIn b x,
        PEqualNP.Outside.L_meta_2235.P2230.reach_mem_orIn a y⟩

end PEqualNP.Outside.L_meta_2235.Q2230


namespace PEqualNP.Outside.L_meta_2235.P2231

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

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

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

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

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

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

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

open PEqualNP.TopForm in
lemma fire {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (hr : OrReaches n C C.output j)
    (x : Fin n → Bool) (u v : Fin n) (hu : u ∈ side (n := n) C j 0) (hv : v ∈ side (n := n) C j 1)
    (hxu : x u = true) (hxv : x v = true) :
    PEqualNP.MetaComplexity.circuitFun n C x = true := by
  obtain ⟨_, hRB, h2⟩ := hAO
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hj))
  have hp : p < n + j := hRB j hj p (by rw [hin]; simp)
  have hq : q < n + j := hRB j hj q (by rw [hin]; simp)
  have e0 : opnd C j 0 = p := by simp [opnd, hin]
  have e1 : opnd C j 1 = q := by simp [opnd, hin]
  simp only [side, e0] at hu
  simp only [side, e1] at hv
  have hval : val C (List.ofFn x) (n + j) = true := by
    rw [val_and (n := n) (by simp) hj hop, hin]
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨hp, reach_var_val _ _ u (mem_orIn_reach u hu) hxu⟩
    · exact ⟨hq, reach_var_val _ _ v (mem_orIn_reach v hv) hxv⟩
  have hR := (orReaches_reach j C.output hr).1
  show val C (List.ofFn x) C.output = true
  exact orStep_up (n := n) (by simp) hR hval

open PEqualNP.TopForm in
lemma part1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hAO : IsAO2 n C)
    (h1 : ∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false)
    (h2 : ∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 →
      PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hr : OrReaches n C C.output j) :
    (∀ w : Fin n, w ∈ side (n := n) C j 0 → w ∉ side (n := n) C j 1) ∧
    (∀ u : Fin n, u ∈ side (n := n) C j 0 → ∀ v : Fin n, v ∈ side (n := n) C j 1 → G.Adj u v) ∧
    ((side (n := n) C j 0).card ≤ 1 ∨ (side (n := n) C j 1).card ≤ 1) := by
  have hdis : ∀ w : Fin n, w ∈ side (n := n) C j 0 → w ∉ side (n := n) C j 1 := by
    intro w hw0 hw1
    have := fire C hAO j hj hop hr (fun k1 => decide (k1 = w)) w w hw0 hw1 (by simp) (by simp)
    rw [h1 w] at this
    exact Bool.false_ne_true this
  have hadj : ∀ u : Fin n, u ∈ side (n := n) C j 0 → ∀ v : Fin n, v ∈ side (n := n) C j 1 →
      G.Adj u v := by
    intro u hu v hv
    have hne : u ≠ v := by
      rintro rfl
      exact hdis u hu hv
    by_contra hna
    have := fire C hAO j hj hop hr (fun k2 => decide (k2 = u ∨ k2 = v)) u v hu hv (by simp)
      (by simp)
    rw [h2 u v hne hna] at this
    exact Bool.false_ne_true this
  refine ⟨hdis, hadj, ?_⟩
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcon.1
  have hsub : side (n := n) C j 1 ⊆ Finset.univ.filter (fun w => G.Adj x w ∧ G.Adj y w) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hadj x hx w hw, hadj y hy w hw⟩
  have h5 := Finset.card_le_card hsub
  have h6 := h4 x y hxy
  omega

end PEqualNP.Outside.L_meta_2235.P2231

namespace PEqualNP.Outside.L_meta_2235.Q2231

theorem sib_main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 → PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.OrReaches n C C.output j → (∀ w : Fin n, w ∈ PEqualNP.TopForm.side (n := n) C j 0 → w ∉ PEqualNP.TopForm.side (n := n) C j 1) ∧ (∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 → ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C j 1).card ≤ 1)) ∧ (∀ F : Finset ℕ, (∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), ∃ i ∈ F, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i ∧ ((e.1 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.2 ∈ PEqualNP.TopForm.side (n := n) C i 1) ∨ (e.2 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.1 ∈ PEqualNP.TopForm.side (n := n) C i 1))) → ∃ T : Finset (Fin n), T.card ≤ F.card ∧ ∀ e3 ∈ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)), e3.1 ∈ T ∨ e3.2 ∈ T) := by
  intro n G _ C h4 hAO h1 h2
  have P1 := fun j hj hop hr => PEqualNP.Outside.L_meta_2235.P2231.part1 G C h4 hAO h1 h2 j hj hop hr
  refine ⟨P1, ?_⟩
  intro F hF
  let piece : ℕ → Finset (Fin n) := fun i =>
    if (PEqualNP.TopForm.side (n := n) C i 0).card ≤ 1 then PEqualNP.TopForm.side (n := n) C i 0
    else if (PEqualNP.TopForm.side (n := n) C i 1).card ≤ 1 then PEqualNP.TopForm.side (n := n) C i 1
    else ∅
  refine ⟨F.biUnion piece, ?_, ?_⟩
  · have hle : ∀ i ∈ F, (piece i).card ≤ 1 := by
      intro i _
      simp only [piece]
      split_ifs with ha hb
      · exact ha
      · exact hb
      · simp
    have := Finset.card_biUnion_le_card_mul F piece 1 hle
    simpa using this
  · intro e he
    obtain ⟨i, hiF, hi, hop, hr, hside⟩ := hF e he
    obtain ⟨_, _, hc⟩ := P1 i hi hop hr
    by_cases ha : (PEqualNP.TopForm.side (n := n) C i 0).card ≤ 1
    · have hp : piece i = PEqualNP.TopForm.side (n := n) C i 0 := by simp only [piece]; rw [if_pos ha]
      rcases hside with ⟨h0, _⟩ | ⟨h0, _⟩
      · left; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hp]; exact h0⟩
      · right; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hp]; exact h0⟩
    · have hb : (PEqualNP.TopForm.side (n := n) C i 1).card ≤ 1 := hc.resolve_left ha
      have hp : piece i = PEqualNP.TopForm.side (n := n) C i 1 := by
        simp only [piece]; rw [if_neg ha, if_pos hb]
      rcases hside with ⟨_, h1'⟩ | ⟨_, h1'⟩
      · right; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hp]; exact h1'⟩
      · left; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hp]; exact h1'⟩

end PEqualNP.Outside.L_meta_2235.Q2231


namespace PEqualNP.Outside.L_meta_2235.P2233

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open Classical

theorem getD_app_lt {α : Type} (l l' : List α) (z : α) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i z = l.getD i z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_self {α : Type} (l : List α) (v z : α) : (l ++ [v]).getD l.length z = v := by
  simp [List.getD_eq_getElem?_getD]

theorem orStep_length (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (orStep n cs g).length = cs.length + 1 := by
  unfold orStep; simp

theorem orStep_getD (n : ℕ) (cs : List (List ℕ)) (g : Gate) (i : ℕ) (h : i < cs.length) :
    (orStep n cs g).getD i [] = cs.getD i [] := by
  unfold orStep; exact getD_app_lt _ _ _ _ h

theorem orStep_last_or (n : ℕ) (cs : List (List ℕ)) (g : Gate) (hg : g.op = GateOp.or) :
    (orStep n cs g).getD cs.length [] = cs.length ::
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) []) := by
  unfold orStep; rw [if_pos hg, getD_app_self]

theorem orStep_last_nor (n : ℕ) (cs : List (List ℕ)) (g : Gate) (hg : ¬ g.op = GateOp.or) :
    (orStep n cs g).getD cs.length [] = [cs.length] := by
  unfold orStep; rw [if_neg hg, getD_app_self]

theorem T_length (n : ℕ) (gs : List Gate) :
    ∀ cs : List (List ℕ), (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs with
  | nil => intro cs; simp
  | cons g gs ih => intro cs; rw [List.foldl_cons, ih, orStep_length]; simp; omega

theorem T_getD (n : ℕ) (gs : List Gate) :
    ∀ (cs : List (List ℕ)) (i : ℕ), i < cs.length → (gs.foldl (orStep n) cs).getD i [] = cs.getD i [] := by
  induction gs with
  | nil => intro cs i _; rfl
  | cons g gs ih =>
    intro cs i hi
    rw [List.foldl_cons, ih _ _ (by rw [orStep_length]; omega), orStep_getD _ _ _ _ hi]

-- the OR closure of gate k
def cl (n : ℕ) (C : Circuit) (k : ℕ) : List ℕ := (orSets n C).getD k []

theorem orSets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  unfold orSets; rw [T_length]; simp

theorem cl_split (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    ∃ P : List (List ℕ), P.length = k ∧ (∀ i < k, P.getD i [] = cl n C i) ∧
      cl n C k = (orStep n P (gateAt C k)).getD k [] := by
  have hg : gateAt C k = C.gates[k] := List.getD_eq_getElem _ _ hk
  set P := (C.gates.take k).foldl (orStep n) [] with hP
  have hPl : P.length = k := by rw [hP, T_length, List.length_take]; simp; omega
  have hsplit : orSets n C = (C.gates.drop k).foldl (orStep n) P := by
    rw [hP, ← List.foldl_append, List.take_append_drop]; rfl
  have hdrop : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := by
    rw [List.drop_eq_getElem_cons hk]
  refine ⟨P, hPl, ?_, ?_⟩
  · intro i hi
    unfold cl
    rw [hsplit]; exact (T_getD n _ P i (by omega)).symm
  · unfold cl
    rw [hsplit, hdrop, List.foldl_cons, T_getD n (C.gates.drop (k + 1)) (orStep n P C.gates[k]) k (by rw [orStep_length]; omega), hg]

theorem mem_cl_or (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hor : (gateAt C k).op = GateOp.or) (g : ℕ) :
    g ∈ cl n C k ↔ g = k ∨ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ g ∈ cl n C (w - n) := by
  obtain ⟨P, hPl, hPg, hcl⟩ := cl_split n C k hk
  rw [hcl]
  have e := orStep_last_or n P (gateAt C k) hor
  rw [hPl] at e
  rw [e, List.mem_cons, List.mem_flatMap]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨w, hw, hgw⟩
    rw [List.mem_filter, decide_eq_true_eq] at hw
    refine ⟨w, hw.1, hw.2.1, hw.2.2, ?_⟩
    rw [← hPg _ (by omega)]; exact hgw
  · rintro ⟨w, hw, h1, h2, hgw⟩
    refine ⟨w, ?_, ?_⟩
    · rw [List.mem_filter, decide_eq_true_eq]; exact ⟨hw, h1, h2⟩
    · rw [hPg _ (by omega)]; exact hgw

theorem cl_nor (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hor : ¬ (gateAt C k).op = GateOp.or) : cl n C k = [k] := by
  obtain ⟨P, hPl, _, hcl⟩ := cl_split n C k hk
  rw [hcl]
  have e := orStep_last_nor n P (gateAt C k) hor
  rw [hPl] at e
  exact e

theorem cl_ge (n : ℕ) (C : Circuit) (k : ℕ) (hk : C.gates.length ≤ k) : cl n C k = [] := by
  unfold cl
  apply List.getD_eq_default
  rw [orSets_length]; exact hk

theorem cl_le (n : ℕ) (C : Circuit) : ∀ k g, g ∈ cl n C k → g ≤ k ∧ g < C.gates.length := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro g hg
    by_cases hk : k < C.gates.length
    · by_cases hor : (gateAt C k).op = GateOp.or
      · rcases (mem_cl_or n C k hk hor g).1 hg with rfl | ⟨w, _, h1, h2, hgw⟩
        · exact ⟨le_refl _, hk⟩
        · have := ih (w - n) (by omega) g hgw
          exact ⟨by omega, this.2⟩
      · rw [cl_nor n C k hk hor] at hg
        simp at hg
        subst hg
        exact ⟨le_refl _, hk⟩
    · rw [cl_ge n C k (by omega)] at hg
      simp at hg

noncomputable def AS (n : ℕ) (C : Circuit) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter
    (fun g => (gateAt C g).op = GateOp.and ∧ ∃ s ∈ S, g ∈ cl n C s)

noncomputable def OS (n : ℕ) (C : Circuit) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter
    (fun g => (gateAt C g).op = GateOp.or ∧ ∃ s ∈ S, g ∈ cl n C s)

theorem main_count (n : ℕ) (C : Circuit)
    (hAO : ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length = 2) :
    ∀ B (S : Finset ℕ), (∀ s ∈ S, s < B) → (AS n C S).card ≤ (OS n C S).card + S.card := by
  intro B
  induction B with
  | zero =>
    intro S hS
    have : S = ∅ := by
      ext s; simp only [Finset.notMem_empty, iff_false]; intro hs; have := hS s hs; omega
    subst this
    simp [AS]
  | succ B ih =>
    intro S hS
    by_cases hB : B ∈ S
    · set S0 := S.erase B with hS0
      have hS0lt : ∀ s ∈ S0, s < B := by
        intro s hs
        rw [hS0, Finset.mem_erase] at hs
        have := hS s hs.2; omega
      have hcard : S.card = S0.card + 1 := by
        rw [hS0, Finset.card_erase_of_mem hB]
        have := Finset.card_pos.2 ⟨B, hB⟩
        omega
      have hmemS : ∀ s, s ∈ S ↔ s = B ∨ s ∈ S0 := by
        intro s; rw [hS0, Finset.mem_erase]
        constructor
        · intro hs; by_cases h : s = B
          · exact Or.inl h
          · exact Or.inr ⟨h, hs⟩
        · rintro (rfl | ⟨_, hs⟩)
          · exact hB
          · exact hs
      by_cases hk : B < C.gates.length
      · by_cases hor : (gateAt C B).op = GateOp.or
        · -- replace B by its gate inputs
          set W := (((gateAt C B).inputs.filter (fun w => decide (n ≤ w ∧ w < n + B))).toFinset).image
            (fun w => w - n) with hW
          set S' := S0 ∪ W with hS'
          have hWcard : W.card ≤ 2 := by
            rw [hW]
            refine le_trans Finset.card_image_le (le_trans (List.toFinset_card_le _) ?_)
            rw [← (hAO B hk).2]
            exact List.length_filter_le _ _
          have hS'lt : ∀ s ∈ S', s < B := by
            intro s hs
            rw [hS', Finset.mem_union] at hs
            rcases hs with hs | hs
            · exact hS0lt s hs
            · rw [hW, Finset.mem_image] at hs
              obtain ⟨w, hw, rfl⟩ := hs
              rw [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hw
              omega
          have hS'card : S'.card ≤ S0.card + 2 := by
            rw [hS']
            exact le_trans (Finset.card_union_le _ _) (by omega)
          have hih := ih S' hS'lt
          -- closure of S is closure of S' plus B
          have hcl : ∀ g, (∃ s ∈ S, g ∈ cl n C s) ↔ g = B ∨ ∃ s ∈ S', g ∈ cl n C s := by
            intro g
            constructor
            · rintro ⟨s, hs, hgs⟩
              rcases (hmemS s).1 hs with rfl | hs0
              · rcases (mem_cl_or n C s hk hor g).1 hgs with h | ⟨w, hw, h1, h2, hgw⟩
                · exact Or.inl h
                · refine Or.inr ⟨w - n, ?_, hgw⟩
                  rw [hS', Finset.mem_union]; right
                  rw [hW, Finset.mem_image]
                  refine ⟨w, ?_, rfl⟩
                  rw [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
                  exact ⟨hw, h1, h2⟩
              · exact Or.inr ⟨s, by rw [hS', Finset.mem_union]; exact Or.inl hs0, hgs⟩
            · rintro (rfl | ⟨s, hs, hgs⟩)
              · exact ⟨g, hB, (mem_cl_or n C g hk hor g).2 (Or.inl rfl)⟩
              · rw [hS', Finset.mem_union] at hs
                rcases hs with hs | hs
                · exact ⟨s, (hmemS s).2 (Or.inr hs), hgs⟩
                · rw [hW, Finset.mem_image] at hs
                  obtain ⟨w, hw, rfl⟩ := hs
                  rw [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hw
                  exact ⟨B, hB, (mem_cl_or n C B hk hor g).2 (Or.inr ⟨w, hw.1, hw.2.1, hw.2.2, hgs⟩)⟩
          have hA : AS n C S ⊆ AS n C S' := by
            intro g hg
            simp only [AS, Finset.mem_filter] at hg ⊢
            refine ⟨hg.1, hg.2.1, ?_⟩
            rcases (hcl g).1 hg.2.2 with rfl | h
            · rw [hor] at hg; exact absurd hg.2.1 (by intro h; cases h)
            · exact h
          have hBnot : B ∉ OS n C S' := by
            intro h
            simp only [OS, Finset.mem_filter] at h
            obtain ⟨s, hs, hBs⟩ := h.2.2
            have := (cl_le n C s B hBs).1
            have := hS'lt s hs
            omega
          have hO : insert B (OS n C S') ⊆ OS n C S := by
            intro g hg
            rw [Finset.mem_insert] at hg
            simp only [OS, Finset.mem_filter, Finset.mem_range]
            rcases hg with rfl | hg
            · exact ⟨hk, hor, (hcl g).2 (Or.inl rfl)⟩
            · simp only [OS, Finset.mem_filter, Finset.mem_range] at hg
              exact ⟨hg.1, hg.2.1, (hcl g).2 (Or.inr hg.2.2)⟩
          have h1 := Finset.card_le_card hA
          have h2 := Finset.card_le_card hO
          rw [Finset.card_insert_of_notMem hBnot] at h2
          omega
        · -- B is an AND gate: its closure is itself
          have hih := ih S0 hS0lt
          have hclB : cl n C B = [B] := cl_nor n C B hk hor
          have hA : AS n C S ⊆ insert B (AS n C S0) := by
            intro g hg
            rw [Finset.mem_insert]
            simp only [AS, Finset.mem_filter] at hg ⊢
            obtain ⟨s, hs, hgs⟩ := hg.2.2
            rcases (hmemS s).1 hs with rfl | hs0
            · rw [hclB] at hgs; simp at hgs; exact Or.inl hgs
            · exact Or.inr ⟨hg.1, hg.2.1, s, hs0, hgs⟩
          have hO : OS n C S0 ⊆ OS n C S := by
            intro g hg
            simp only [OS, Finset.mem_filter] at hg ⊢
            obtain ⟨s, hs, hgs⟩ := hg.2.2
            exact ⟨hg.1, hg.2.1, s, (hmemS s).2 (Or.inr hs), hgs⟩
          have h1 := le_trans (Finset.card_le_card hA) (Finset.card_insert_le _ _)
          have h2 := Finset.card_le_card hO
          omega
      · -- B is not a gate: its closure is empty
        have hih := ih S0 hS0lt
        have hclB : cl n C B = [] := cl_ge n C B (by omega)
        have hA : AS n C S ⊆ AS n C S0 := by
          intro g hg
          simp only [AS, Finset.mem_filter] at hg ⊢
          obtain ⟨s, hs, hgs⟩ := hg.2.2
          rcases (hmemS s).1 hs with rfl | hs0
          · rw [hclB] at hgs; simp at hgs
          · exact ⟨hg.1, hg.2.1, s, hs0, hgs⟩
        have hO : OS n C S0 ⊆ OS n C S := by
          intro g hg
          simp only [OS, Finset.mem_filter] at hg ⊢
          obtain ⟨s, hs, hgs⟩ := hg.2.2
          exact ⟨hg.1, hg.2.1, s, (hmemS s).2 (Or.inr hs), hgs⟩
        have h1 := Finset.card_le_card hA
        have h2 := Finset.card_le_card hO
        omega
    · apply ih S
      intro s hs
      have := hS s hs
      have : s ≠ B := fun h => hB (h ▸ hs)
      omega

end PEqualNP.Outside.L_meta_2235.P2233

namespace PEqualNP.Outside.L_meta_2235.Q2233

open PEqualNP.Outside.L_meta_2235.P2233 in
theorem sib_main : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  classical
  intro n C F hAO hF
  by_cases hFe : F = ∅
  · subst hFe; simp
  obtain ⟨j0, hj0⟩ := Finset.nonempty_iff_ne_empty.2 hFe
  have hn : n ≤ C.output := (hF j0 hj0).2.2.1
  have hAO' : ∀ k < C.gates.length, ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.length = 2 := by
    intro k hk
    have hg : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := List.getD_eq_getElem _ _ hk
    rw [hg]
    exact ⟨hAO.1 _ (List.getElem_mem hk), hAO.2.2 _ (List.getElem_mem hk)⟩
  have hc := main_count n C hAO' (C.output - n + 1) {C.output - n} (by intro s hs; simp at hs; omega)
  have hFA : F ⊆ AS n C {C.output - n} := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := hF j hj
    simp only [AS, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, exists_eq_left]
    exact ⟨h1, h2, h3.2⟩
  have hset : {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} = ↑(OS n C {C.output - n}) := by
    ext i
    simp only [Set.mem_setOf_eq, OS, Finset.coe_filter, Finset.mem_range, Finset.mem_singleton,
      exists_eq_left, PEqualNP.CleanedNonEdge.OrReaches, cl]
    constructor
    · rintro ⟨h1, h2, _, h4⟩; exact ⟨h1, h2, h4⟩
    · rintro ⟨h1, h2, h4⟩; exact ⟨h1, h2, hn, h4⟩
  rw [hset, Set.ncard_coe_finset]
  have := Finset.card_le_card hFA
  simp only [Finset.card_singleton] at hc
  omega

end PEqualNP.Outside.L_meta_2235.Q2233


namespace PEqualNP.Outside.L_meta_2235.P2234

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

end PEqualNP.Outside.L_meta_2235.P2234

namespace PEqualNP.Outside.L_meta_2235.Q2234

theorem sib_main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) → (∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or → 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card → (∃ j1 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j1) i) → ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output i) ∧ ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card :=
  PEqualNP.Outside.L_meta_2235.P2234.main

end PEqualNP.Outside.L_meta_2235.Q2234

namespace PEqualNP.Outside.L_meta_2235.Asm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open Classical

theorem count (n : ℕ) (C : Circuit) (F : Finset ℕ) (A B : Set ℕ)
    (hA : ∀ i ∈ A, i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i)
    (hB : ∀ i ∈ B, i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧ ¬ OrReaches n C C.output i)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and) :
    A.ncard + B.ncard + F.card ≤ C.size := by
  have hfin : (Set.Iio C.gates.length).Finite := Set.finite_Iio _
  have hAs : A ⊆ Set.Iio C.gates.length := fun i hi => (hA i hi).1
  have hBs : B ⊆ Set.Iio C.gates.length := fun i hi => (hB i hi).1
  have hFs : (↑F : Set ℕ) ⊆ Set.Iio C.gates.length := fun i hi => (hF i hi).1
  have hAf : A.Finite := hfin.subset hAs
  have hBf : B.Finite := hfin.subset hBs
  have hdAB : Disjoint A B := Set.disjoint_left.mpr fun x hx hy => (hB x hy).2.2 (hA x hx).2.2
  have hdABF : Disjoint (A ∪ B) (↑F : Set ℕ) := by
    refine Set.disjoint_left.mpr fun x hx hy => ?_
    have h2 := (hF x hy).2
    rcases hx with hx | hx
    · have h3 := (hA x hx).2.1
      rw [h2] at h3
      cases h3
    · have h3 := (hB x hx).2.1
      rw [h2] at h3
      cases h3
  have e1 : (A ∪ B ∪ ↑F).ncard = A.ncard + B.ncard + F.card := by
    rw [Set.ncard_union_eq hdABF (hAf.union hBf) (Finset.finite_toSet F),
      Set.ncard_union_eq hdAB hAf hBf, Set.ncard_coe_finset]
  have hsub : A ∪ B ∪ ↑F ⊆ (↑(Finset.range C.gates.length) : Set ℕ) := by
    intro i hi
    rw [Finset.coe_range]
    rcases hi with (hi | hi) | hi
    · exact hAs hi
    · exact hBs hi
    · exact hFs hi
  have h3 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Finset.card_range, e1] at h3
  exact h3

end PEqualNP.Outside.L_meta_2235.Asm

theorem PEqualNP.Outside.L_meta_2235 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 → PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false) → ∃ T : Finset (Fin n), (∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), e.1 ∈ T ∨ e.2 ∈ T) ∧ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)).card + T.card ≤ C.size + 1 := by
  intro n G _ C h4 hAO h1 h2
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨∅, ?_, ?_⟩
    · intro e _
      exact e.1.elim0
    · simp
  have P1 := (PEqualNP.Outside.L_meta_2235.Q2231.sib_main n G C h4 hAO h1 h2).1
  have P2 := (PEqualNP.Outside.L_meta_2235.Q2231.sib_main n G C h4 hAO h1 h2).2
  let F : Finset ℕ := (Finset.range C.gates.length).filter (fun j =>
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
    PEqualNP.CleanedNonEdge.OrReaches n C C.output j ∧
    (PEqualNP.TopForm.side (n := n) C j 0).Nonempty ∧ (PEqualNP.TopForm.side (n := n) C j 1).Nonempty)
  have memF : ∀ j, j ∈ F ↔ j < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      PEqualNP.CleanedNonEdge.OrReaches n C C.output j ∧
      (PEqualNP.TopForm.side (n := n) C j 0).Nonempty ∧ (PEqualNP.TopForm.side (n := n) C j 1).Nonempty := by
    intro j
    simp only [F, Finset.mem_filter, Finset.mem_range]
  have hF : ∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), ∃ i ∈ F, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i ∧ ((e.1 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.2 ∈ PEqualNP.TopForm.side (n := n) C i 1) ∨ (e.2 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.1 ∈ PEqualNP.TopForm.side (n := n) C i 1)) := by
    intro e he
    have he' := (Finset.mem_filter.mp he).2
    obtain ⟨j, hj, hop, hre, hs⟩ := PEqualNP.Outside.L_meta_2235.Q2230.sib_main n C e.1 e.2 hAO h1 he'.1 he'.2.2
    refine ⟨j, ?_, hj, hop, hre, hs⟩
    rw [memF]
    refine ⟨hj, hop, hre, ?_, ?_⟩
    · rcases hs with hs | hs
      · exact ⟨_, hs.1⟩
      · exact ⟨_, hs.1⟩
    · rcases hs with hs | hs
      · exact ⟨_, hs.2⟩
      · exact ⟨_, hs.2⟩
  obtain ⟨T, hTc, hTcov⟩ := P2 F hF
  refine ⟨T, hTcov, ?_⟩
  let z : Fin n := ⟨0, hn⟩
  let ctr : ℕ → Fin n := fun j =>
    if h : (PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∧ (PEqualNP.TopForm.side (n := n) C j 0).Nonempty
    then (PEqualNP.TopForm.side (n := n) C j 0).min' h.2
    else if h' : (PEqualNP.TopForm.side (n := n) C j 1).Nonempty
    then (PEqualNP.TopForm.side (n := n) C j 1).min' h' else z
  let lf : ℕ → ℕ := fun j =>
    if (PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∧ (PEqualNP.TopForm.side (n := n) C j 0).Nonempty
    then PEqualNP.TopForm.opnd C j 1 else PEqualNP.TopForm.opnd C j 0
  -- for a gate of F: the centre and the leaf side
  have key : ∀ j ∈ F, ∀ u v : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 →
      v ∈ PEqualNP.TopForm.side (n := n) C j 1 →
      (ctr j = u ∧ v ∈ PEqualNP.TopForm.orIn n C (lf j)) ∨
      (ctr j = v ∧ u ∈ PEqualNP.TopForm.orIn n C (lf j)) := by
    intro j hj u v hu hv
    have hj' := (memF j).mp hj
    by_cases hA : (PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∧ (PEqualNP.TopForm.side (n := n) C j 0).Nonempty
    · left
      have hc : ctr j = (PEqualNP.TopForm.side (n := n) C j 0).min' hA.2 := by
        simp only [ctr, dif_pos hA]
      have hl : lf j = PEqualNP.TopForm.opnd C j 1 := by
        simp only [lf, if_pos hA]
      refine ⟨?_, ?_⟩
      · rw [hc]
        exact Finset.card_le_one.mp hA.1 _ (Finset.min'_mem _ _) _ hu
      · rw [hl]
        exact hv
    · right
      have hB : (PEqualNP.TopForm.side (n := n) C j 1).card ≤ 1 := by
        rcases (P1 j hj'.1 hj'.2.1 hj'.2.2.1).2.2 with h | h
        · exact absurd ⟨h, hj'.2.2.2.1⟩ hA
        · exact h
      have hc : ctr j = (PEqualNP.TopForm.side (n := n) C j 1).min' hj'.2.2.2.2 := by
        simp only [ctr, dif_neg hA, dif_pos hj'.2.2.2.2]
      have hl : lf j = PEqualNP.TopForm.opnd C j 0 := by
        simp only [lf, if_neg hA]
      refine ⟨?_, ?_⟩
      · rw [hc]
        exact Finset.card_le_one.mp hB _ (Finset.min'_mem _ _) _ hv
      · rw [hl]
        exact hu
  have hadj : ∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b := by
    intro j hj b hb
    have hj' := (memF j).mp hj
    have cross := (P1 j hj'.1 hj'.2.1 hj'.2.2.1).2.1
    by_cases hA : (PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∧ (PEqualNP.TopForm.side (n := n) C j 0).Nonempty
    · have hc : ctr j = (PEqualNP.TopForm.side (n := n) C j 0).min' hA.2 := by
        simp only [ctr, dif_pos hA]
      have hl : lf j = PEqualNP.TopForm.opnd C j 1 := by
        simp only [lf, if_pos hA]
      rw [hl] at hb
      rw [hc]
      exact cross _ (Finset.min'_mem _ _) b hb
    · have hc : ctr j = (PEqualNP.TopForm.side (n := n) C j 1).min' hj'.2.2.2.2 := by
        simp only [ctr, dif_neg hA, dif_pos hj'.2.2.2.2]
      have hl : lf j = PEqualNP.TopForm.opnd C j 0 := by
        simp only [lf, if_neg hA]
      rw [hl] at hb
      rw [hc]
      exact (cross b hb _ (Finset.min'_mem _ _)).symm
  obtain ⟨hdisj, hsum⟩ := PEqualNP.Outside.L_meta_2235.Q2234.sib_main n G C F ctr lf h4 hAO h1 hadj
  have hF2 := PEqualNP.Outside.L_meta_2235.Q2233.sib_main n C F hAO (fun j hj => by
    have hj' := (memF j).mp hj
    exact ⟨hj'.1, hj'.2.1, hj'.2.2.1⟩)
  -- edges into centre/leaf pairs
  let S : Finset (Fin n × Fin n) := Finset.univ.filter (fun p : Fin n × Fin n =>
    ∃ j2 ∈ F, ctr j2 = p.1 ∧ p.2 ∈ PEqualNP.TopForm.orIn n C (lf j2))
  have hS : S.card = ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card := by
    simp only [S, Finset.card_filter]
    rw [Fintype.sum_prod_type]
  let f : Fin n × Fin n → Fin n × Fin n := fun e =>
    if ∃ j2 ∈ F, ctr j2 = e.1 ∧ e.2 ∈ PEqualNP.TopForm.orIn n C (lf j2) then e else (e.2, e.1)
  have hE : (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn f
    · intro e he
      obtain ⟨i, hi, -, -, -, hs⟩ := hF e he
      by_cases hc : ∃ j2 ∈ F, ctr j2 = e.1 ∧ e.2 ∈ PEqualNP.TopForm.orIn n C (lf j2)
      · have : f e = e := if_pos hc
        rw [this]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
      · have : f e = (e.2, e.1) := if_neg hc
        rw [this]
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rcases hs with hs | hs
        · rcases key i hi _ _ hs.1 hs.2 with k | k
          · exact absurd ⟨i, hi, k⟩ hc
          · exact ⟨i, hi, k⟩
        · rcases key i hi _ _ hs.1 hs.2 with k | k
          · exact ⟨i, hi, k⟩
          · exact absurd ⟨i, hi, k⟩ hc
    · intro e he e' he' hee
      have hlt := (Finset.mem_filter.mp he).2.1
      have hlt' := (Finset.mem_filter.mp he').2.1
      by_cases hc : ∃ j2 ∈ F, ctr j2 = e.1 ∧ e.2 ∈ PEqualNP.TopForm.orIn n C (lf j2)
      · have h5 : f e = e := if_pos hc
        by_cases hc' : ∃ j2 ∈ F, ctr j2 = e'.1 ∧ e'.2 ∈ PEqualNP.TopForm.orIn n C (lf j2)
        · have h6 : f e' = e' := if_pos hc'
          rw [h5, h6] at hee
          exact hee
        · have h6 : f e' = (e'.2, e'.1) := if_neg hc'
          rw [h5, h6] at hee
          have a1 : e.1 = e'.2 := congrArg Prod.fst hee
          have a2 : e.2 = e'.1 := congrArg Prod.snd hee
          rw [a1, a2] at hlt
          exact absurd (lt_trans hlt hlt') (lt_irrefl _)
      · have h5 : f e = (e.2, e.1) := if_neg hc
        by_cases hc' : ∃ j2 ∈ F, ctr j2 = e'.1 ∧ e'.2 ∈ PEqualNP.TopForm.orIn n C (lf j2)
        · have h6 : f e' = e' := if_pos hc'
          rw [h5, h6] at hee
          have a1 : e.2 = e'.1 := congrArg Prod.fst hee
          have a2 : e.1 = e'.2 := congrArg Prod.snd hee
          rw [a1, a2] at hlt
          exact absurd (lt_trans hlt hlt') (lt_irrefl _)
        · have h6 : f e' = (e'.2, e'.1) := if_neg hc'
          rw [h5, h6] at hee
          have a1 : e.2 = e'.2 := congrArg Prod.fst hee
          have a2 : e.1 = e'.1 := congrArg Prod.snd hee
          exact Prod.ext a2 a1
  have hcount := PEqualNP.Outside.L_meta_2235.Asm.count n C F
    {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i}
    {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2}
    (fun i hi => hi)
    (fun i hi => ⟨hi.1, hi.2.1, hdisj i hi.1 hi.2.1 hi.2.2.1 hi.2.2.2⟩)
    (fun j hj => by
      have hj' := (memF j).mp hj
      exact ⟨hj'.1, hj'.2.1⟩)
  omega
