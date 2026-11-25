import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9008

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

def bits (V : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) : List Bool :=
  (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (Sum.inl x2 ∈ V)) ++
    List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (Sum.inr x2 ∈ V)

lemma bits_length (V : Finset (Fin 13 ⊕ Fin 13)) : (bits V).length = 26 := by simp [bits]

def var (i : ℕ) : Fin 13 ⊕ Fin 13 :=
  if h : i < 13 then Sum.inl ⟨i, h⟩ else Sum.inr ⟨(i - 13) % 13, Nat.mod_lt _ (by norm_num)⟩

lemma bits_getD (V : Finset (Fin 13 ⊕ Fin 13)) (i : ℕ) (hi : i < 26) :
    (bits V).getD i false = decide (var i ∈ V) := by
  by_cases h : i < 13
  · rw [List.getD_eq_getElem?_getD]
    unfold bits
    rw [List.getElem?_append_left (by simpa using h), List.getElem?_ofFn]
    simp [var, h]
  · rw [List.getD_eq_getElem?_getD]
    unfold bits
    rw [List.getElem?_append_right (by simp; omega)]
    have e : (i - 13) % 13 = i - 13 := Nat.mod_eq_of_lt (by omega)
    have e2 : i - (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (Sum.inl x2 ∈ V)).length
        = i - 13 := by simp
    rw [e2, List.getElem?_ofFn]
    simp [var, h, e, show i - 13 < 13 by omega]

def F (C : Circuit) (i : ℕ) : Finset (Finset (Fin 13 ⊕ Fin 13)) :=
  if i < 26 then {Finset.univ.erase (var i)} else
    if h : (gateAt C (i - 26)).inputs.getD 0 0 < i ∧ (gateAt C (i - 26)).inputs.getD 1 0 < i then
      match (gateAt C (i - 26)).op with
      | GateOp.and => F C ((gateAt C (i - 26)).inputs.getD 0 0) ∪
          F C ((gateAt C (i - 26)).inputs.getD 1 0)
      | _ => Finset.image₂ (fun x y => x ∩ y) (F C ((gateAt C (i - 26)).inputs.getD 0 0))
          (F C ((gateAt C (i - 26)).inputs.getD 1 0))
    else ∅
termination_by i
decreasing_by
  all_goals first | exact h.1 | exact h.2

lemma sub_erase_iff (V : Finset (Fin 13 ⊕ Fin 13)) (a : Fin 13 ⊕ Fin 13) :
    V ⊆ Finset.univ.erase a ↔ a ∉ V := by
  constructor
  · intro h ha; exact (Finset.mem_erase.mp (h ha)).1 rfl
  · intro h x hx; exact Finset.mem_erase.mpr ⟨fun e => h (e ▸ hx), Finset.mem_univ _⟩

lemma gate_shape (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 26 C) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j).inputs = [a, b] ∧ a < 26 + j ∧ b < 26 + j ∧
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  obtain ⟨hao, hrb, h2⟩ := hC
  have hm := gateAt_mem hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h2 _ hm)
  exact ⟨a, b, hab, hrb j hj a (by rw [hab]; simp), hrb j hj b (by rw [hab]; simp), hao _ hm⟩

lemma F_gate (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 26 C) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j).inputs = [a, b] ∧ a < 26 + j ∧ b < 26 + j ∧
      (((gateAt C j).op = GateOp.and ∧ F C (26 + j) = F C a ∪ F C b) ∨
       ((gateAt C j).op = GateOp.or ∧
         F C (26 + j) = Finset.image₂ (fun x y => x ∩ y) (F C a) (F C b))) := by
  obtain ⟨a, b, hab, ha, hb, hop⟩ := gate_shape C hC j hj
  refine ⟨a, b, hab, ha, hb, ?_⟩
  have e : 26 + j - 26 = j := by omega
  have hn : ¬ (26 + j < 26) := by omega
  have hc : (gateAt C (26 + j - 26)).inputs.getD 0 0 < 26 + j ∧
      (gateAt C (26 + j - 26)).inputs.getD 1 0 < 26 + j := by
    rw [e, hab]; simp; omega
  rcases hop with hop | hop
  · left
    refine ⟨hop, ?_⟩
    rw [F, if_neg hn, dif_pos hc]
    simp only [e, hab, hop]
    simp
  · right
    refine ⟨hop, ?_⟩
    rw [F, if_neg hn, dif_pos hc]
    simp only [e, hab, hop]
    simp

lemma inv (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 26 C) :
    ∀ w, w < 26 + C.gates.length → ∀ V, val C (bits V) w = false ↔ ∃ W ∈ F C w, V ⊆ W := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw V
    by_cases h26 : w < 26
    · rw [val_input (bits_length V) h26, bits_getD V w h26, F, if_pos h26]
      simp only [Finset.mem_singleton, exists_eq_left, sub_erase_iff]
      simp
    · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨a, b, hab, ha, hb, hcase⟩ := F_gate C hC j hj
      have iha := ih a ha (by omega) V
      have ihb := ih b hb (by omega) V
      rw [val_gate (bits_length V) hj, hab]
      simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb]
      rcases hcase with ⟨hop, hF⟩ | ⟨hop, hF⟩
      · rw [hop, hF]
        simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
          Bool.and_eq_false_iff]
        rw [iha, ihb]
        simp only [Finset.mem_union]
        constructor
        · rintro (⟨W, hW, s⟩ | ⟨W, hW, s⟩)
          · exact ⟨W, Or.inl hW, s⟩
          · exact ⟨W, Or.inr hW, s⟩
        · rintro ⟨W, (hW | hW), s⟩
          · exact Or.inl ⟨W, hW, s⟩
          · exact Or.inr ⟨W, hW, s⟩
      · rw [hop, hF]
        simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
          Bool.or_eq_false_iff]
        rw [iha, ihb]
        constructor
        · rintro ⟨⟨W1, h1, s1⟩, ⟨W2, h2, s2⟩⟩
          exact ⟨W1 ∩ W2, Finset.mem_image₂_of_mem h1 h2, Finset.subset_inter s1 s2⟩
        · rintro ⟨W, hW, s⟩
          obtain ⟨W1, h1, W2, h2, rfl⟩ := Finset.mem_image₂.mp hW
          exact ⟨⟨W1, h1, s.trans Finset.inter_subset_left⟩,
            ⟨W2, h2, s.trans Finset.inter_subset_right⟩⟩

theorem main (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 26 C)
    (hex : ∃ V, C.eval (bits V) = true) :
    ∃ (x5 : ℕ → Finset (Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)))), ∃ x6 < (26 : ℕ) + C.size,
      (∀ x7 < (26 : ℕ), ∃ (x9 : Fin (13 : ℕ) ⊕ Fin (13 : ℕ)), x5 x7 = {Finset.univ.erase x9}) ∧
      (∀ x7 < C.size, ∃ x9 < (26 : ℕ) + x7, ∃ x10 < (26 : ℕ) + x7,
        x5 ((26 : ℕ) + x7) = x5 x9 ∪ x5 x10 ∨
        x5 ((26 : ℕ) + x7) = Finset.image₂
          (fun (x11 x12 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x11 ∩ x12) (x5 x9) (x5 x10)) ∧
      ∀ (x7 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))),
        C.eval (bits x7) = Bool.false ↔ ∃ x8 ∈ x5 x6, x7 ⊆ x8 := by
  have hout : C.output < 26 + C.gates.length := by
    by_contra hc
    obtain ⟨V, hV⟩ := hex
    have h0 : val C (bits V) C.output = false := val_ge (bits_length V) (by omega)
    change val C (bits V) C.output = true at hV
    rw [h0] at hV
    exact Bool.noConfusion hV
  refine ⟨F C, C.output, hout, ?_, ?_, ?_⟩
  · intro i hi
    exact ⟨var i, by rw [F, if_pos hi]⟩
  · intro j hj
    obtain ⟨a, b, _, ha, hb, hcase⟩ := F_gate C hC j hj
    refine ⟨a, ha, b, hb, ?_⟩
    rcases hcase with ⟨_, hF⟩ | ⟨_, hF⟩
    · exact Or.inl hF
    · exact Or.inr hF
  · intro V
    exact inv C hC C.output hout V

end PEqualNP.Outside.L_meta_9008

theorem PEqualNP.Outside.L_meta_9008 : have x1 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (Sum.inl x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (Sum.inr x2 ∈ x1); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → (∃ (x4 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x2.eval (x1 x4) = Bool.true) → ∃ (x5 : ℕ → Finset (Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)))), ∃ x6 < (26 : ℕ) + x2.size, (∀ x7 < (26 : ℕ), ∃ (x9 : Fin (13 : ℕ) ⊕ Fin (13 : ℕ)), x5 x7 = {Finset.univ.erase x9}) ∧ (∀ x7 < x2.size, ∃ x9 < (26 : ℕ) + x7, ∃ x10 < (26 : ℕ) + x7, x5 ((26 : ℕ) + x7) = x5 x9 ∪ x5 x10 ∨ x5 ((26 : ℕ) + x7) = Finset.image₂ (fun (x11 x12 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x11 ∩ x12) (x5 x9) (x5 x10)) ∧ ∀ (x7 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x2.eval (x1 x7) = Bool.false ↔ ∃ x8 ∈ x5 x6, x7 ⊆ x8 := by
  intro x1 C hC hex
  exact PEqualNP.Outside.L_meta_9008.main C hC hex
