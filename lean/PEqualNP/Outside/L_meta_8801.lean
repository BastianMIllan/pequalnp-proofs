import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8801

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.MetaComplexity.NestedCover

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

theorem getD_snoc (P : List Bool) (v : Bool) (i : ℕ) :
    (P ++ [v]).getD i false =
      if i < P.length then P.getD i false else if i = P.length then v else false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases lt_trichotomy i P.length with h | h | h
  · rw [List.getElem?_append_left h, if_pos h]
  · subst h
    rw [List.getElem?_append_right (le_refl _)]
    simp
  · rw [List.getElem?_append_right (by omega), if_neg (by omega), if_neg (by omega)]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem len_fold : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl stp w).length = w.length + gs.length
  | [], w => by simp
  | g :: gs, w => by
    rw [List.foldl_cons, len_fold gs]
    simp [stp]
    omega

theorem getD_fold_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl stp w).getD i false = w.getD i false
  | [], w, i, _ => rfl
  | g :: gs, w, i, h => by
    rw [List.foldl_cons, getD_fold_lt gs _ i (by simp [stp]; omega)]
    simp only [stp]
    rw [getD_snoc, if_pos h]

theorem fold_take (gs : List Gate) (x : List Bool) (k i : ℕ) (hi : i < x.length + k)
    (hk : k ≤ gs.length) :
    (gs.foldl stp x).getD i false = ((gs.take k).foldl stp x).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gs]
  rw [List.foldl_append, getD_fold_lt]
  rw [len_fold]
  simp
  omega

theorem gate_val (C : Circuit) (x : List Bool) (k : ℕ) (hk : k < C.gates.length)
    (hread : ∀ i ∈ (C.gates[k]).inputs, i < x.length + k) :
    wireValue C x (x.length + k) =
      C.gates[k].op.eval (C.gates[k].inputs.map fun i => wireValue C x i) := by
  unfold wireValue
  rw [wires_eq]
  have hP : ((C.gates.take k).foldl stp x).length = x.length + k := by
    rw [len_fold]; simp; omega
  have e1 : (C.gates.foldl stp x).getD (x.length + k) false =
      ((C.gates.take (k + 1)).foldl stp x).getD (x.length + k) false :=
    fold_take _ _ _ _ (by omega) (by omega)
  rw [e1, List.take_succ, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [stp]
  rw [getD_snoc, if_neg (by omega), if_pos hP.symm]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [fold_take C.gates x k i (hread i hi) (by omega)]

def Le (P Q : List Bool) : Prop :=
  P.length = Q.length ∧ ∀ i, P.getD i false = true → Q.getD i false = true

theorem le_stp (P Q : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : Le P Q) : Le (stp P g) (stp Q g) := by
  refine ⟨by simp [stp, h.1], ?_⟩
  intro i hi
  simp only [stp] at hi ⊢
  rw [getD_snoc] at hi ⊢
  rw [← h.1]
  by_cases h1 : i < P.length
  · rw [if_pos h1] at hi ⊢
    exact h.2 i hi
  · rw [if_neg h1] at hi ⊢
    by_cases h2 : i = P.length
    · rw [if_pos h2] at hi ⊢
      rcases hg with hg | hg
      · rw [hg] at hi ⊢
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hi ⊢
        rintro b ⟨a, ha, rfl⟩
        exact h.2 a (hi _ ⟨a, ha, rfl⟩)
      · rw [hg] at hi ⊢
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hi ⊢
        obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := hi
        exact ⟨_, ⟨a, ha, rfl⟩, h.2 a hb⟩
    · rw [if_neg h2] at hi
      exact absurd hi (by simp)

theorem le_fold : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ P Q, Le P Q → Le (gs.foldl stp P) (gs.foldl stp Q)
  | [], _, P, Q, h => h
  | g :: gs, hg, P, Q, h => by
    rw [List.foldl_cons, List.foldl_cons]
    exact le_fold gs (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) _ _
      (le_stp P Q g (hg g (List.mem_cons_self ..)) h)

theorem mono (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (P Q : List Bool) (h : Le P Q) (w : ℕ) (hw : wireValue C P w = true) :
    wireValue C Q w = true := by
  unfold wireValue at hw ⊢
  rw [wires_eq] at hw ⊢
  exact (le_fold C.gates hC P Q h).2 w hw

theorem inc_len {n : ℕ} (X Y : Finset (Fin n)) : (incidenceInput X Y).length = n + n := by
  simp [incidenceInput]

theorem inc_getD {n : ℕ} (X Y : Finset (Fin n)) (i : ℕ) :
    (incidenceInput X Y).getD i false = true ↔
      (∃ p ∈ X, i = p.val) ∨ (∃ l ∈ Y, i = n + l.val) := by
  unfold incidenceInput
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_ofFn]
    simp only [h, dite_true, Option.getD_some, decide_eq_true_eq]
    constructor
    · intro hm; exact Or.inl ⟨_, hm, rfl⟩
    · rintro (⟨p, hp, rfl⟩ | ⟨l, hl, hi⟩)
      · exact hp
      · omega
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_ofFn]
    simp only [List.length_ofFn]
    by_cases h2 : i - n < n
    · simp only [h2, dite_true, Option.getD_some, decide_eq_true_eq]
      constructor
      · intro hm; exact Or.inr ⟨_, hm, by simp; omega⟩
      · rintro (⟨p, hp, hi⟩ | ⟨l, hl, hi⟩)
        · omega
        · have : (⟨i - n, h2⟩ : Fin n) = l := Fin.ext (by simp; omega)
          rw [this]; exact hl
    · simp only [h2, dite_false, Option.getD_none, Bool.false_eq_true, false_iff, not_or,
        not_exists, not_and]
      constructor
      · intro p _ hp; omega
      · intro l _ hl; omega

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

def Good (C : Circuit) (n : ℕ) (X : Finset (Fin n)) (x4 : Fin n) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.or ∧ wireValue C (incidenceInput Xᶜ {x4}) (n + n + j) = false ∧
    ∃ (a b : ℕ), (gateAt C j).inputs = [a, b] ∧
      (∃ (p q : Fin n), wireValue C (incidenceInput {p} {x4}) a = true ∧
        wireValue C (incidenceInput {q} {x4}) b = true) ∧
      ∀ p : Fin n, wireValue C (incidenceInput {p} {x4}) a = true →
        wireValue C (incidenceInput {p} {x4}) b = false

noncomputable def Sset (C : Circuit) (n : ℕ) (X : Finset (Fin n)) (x4 : Fin n) : Finset ℕ := by
  classical exact (Finset.range C.size).filter (Good C n X x4)

theorem mem_Sset (C : Circuit) (n : ℕ) (X : Finset (Fin n)) (x4 : Fin n) (j : ℕ) :
    j ∈ Sset C n X x4 ↔ j < C.size ∧ Good C n X x4 j := by
  unfold Sset
  simp

theorem image_merge {n : ℕ} (s : Finset (Fin n)) (rep : Fin n → Fin n) (c d : Fin n) :
    (s.image rep).card ≤ (s.image (fun r => if rep r = c then d else rep r)).card + 1 := by
  classical
  have h1 : (s.image rep).erase c ⊆ s.image (fun r => if rep r = c then d else rep r) := by
    intro z hz
    rw [Finset.mem_erase] at hz
    obtain ⟨hzc, hz⟩ := hz
    rw [Finset.mem_image] at hz ⊢
    obtain ⟨r, hr, rfl⟩ := hz
    exact ⟨r, hr, by rw [if_neg hzc]⟩
  have h2 := Finset.card_le_card h1
  have h3 := Finset.pred_card_le_card_erase (s := s.image rep) (a := c)
  omega

theorem filter_succ (S : Finset ℕ) (k : ℕ) :
    (S.filter (· < k + 1)) = if k ∈ S then insert k (S.filter (· < k)) else S.filter (· < k) := by
  ext j
  split_ifs with h
  · simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hj, hjk⟩
      by_cases e : j = k
      · exact Or.inl e
      · exact Or.inr ⟨hj, by omega⟩
    · rintro (rfl | ⟨hj, hjk⟩)
      · exact ⟨h, by omega⟩
      · exact ⟨hj, by omega⟩
  · simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hj, hjk⟩
      refine ⟨hj, ?_⟩
      by_contra hc
      have : j = k := by omega
      exact h (this ▸ hj)
    · rintro ⟨hj, hjk⟩; exact ⟨hj, by omega⟩

theorem main_inv (n : ℕ) (C : Circuit) (X : Finset (Fin n)) (x4 : Fin n)
    (hAO : PEqualNP.TopForm.IsAO2 (n + n) C) :
    ∀ k ≤ C.size, ∃ rep : Fin n → Fin n,
      X.card ≤ (X.image rep).card + ((Sset C n X x4).filter (· < k)).card ∧
      ∀ w < n + n + k, wireValue C (incidenceInput Xᶜ {x4}) w = false →
        ∀ p q : Fin n, wireValue C (incidenceInput {p} {x4}) w = true →
          wireValue C (incidenceInput {q} {x4}) w = true → rep p = rep q := by
  classical
  obtain ⟨hAnd, hRB, hTwo⟩ := hAO
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := hAnd
  set Z := incidenceInput Xᶜ {x4} with hZ
  have hZlen : Z.length = n + n := inc_len _ _
  have hsplen : ∀ p : Fin n, (incidenceInput {p} {x4}).length = n + n := fun p => inc_len _ _
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨id, by simp, ?_⟩
    intro w hw hZw p q hp hq
    unfold wireValue at hp hq hZw
    rw [wires_eq, getD_fold_lt _ _ _ (by rw [hsplen]; omega)] at hp hq
    rw [wires_eq, getD_fold_lt _ _ _ (by rw [hZlen]; omega)] at hZw
    rw [inc_getD] at hp hq
    have hZ4 : Z.getD (n + x4.val) false = true := by
      rw [hZ, inc_getD]; exact Or.inr ⟨x4, Finset.mem_singleton_self _, rfl⟩
    rcases hp with ⟨p', hp', hpw⟩ | ⟨l, hl, hlw⟩
    · rcases hq with ⟨q', hq', hqw⟩ | ⟨l, hl, hlw⟩
      · rw [Finset.mem_singleton] at hp' hq'
        subst hp' hq'
        simp only [id]
        exact Fin.ext (by omega)
      · rw [Finset.mem_singleton] at hl; subst hl; rw [hlw, hZ4] at hZw; exact absurd hZw (by simp)
    · rw [Finset.mem_singleton] at hl; subst hl; rw [hlw, hZ4] at hZw; exact absurd hZw (by simp)
  | succ k ih =>
    intro hk
    obtain ⟨rep, hcard, hrep⟩ := ih (by omega)
    have hkl : k < C.gates.length := by unfold Circuit.size at hk; omega
    set g := C.gates[k] with hg
    have hgm : g ∈ C.gates := List.getElem_mem hkl
    have hga : gateAt C k = g := gateAt_eq C k hkl
    have hlen2 := hTwo g hgm
    obtain ⟨a, b, hab⟩ : ∃ a b, g.inputs = [a, b] := by
      match h : g.inputs, hlen2 with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    have hread : ∀ i ∈ g.inputs, i < n + n + k := by
      intro i hi
      have := hRB k hkl i (by rw [hga]; exact hi)
      exact this
    have ha : a < n + n + k := hread a (by rw [hab]; simp)
    have hb : b < n + n + k := hread b (by rw [hab]; simp)
    -- value of the new wire on any input of length n + n
    have hval : ∀ x : List Bool, x.length = n + n →
        wireValue C x (n + n + k) = g.op.eval [wireValue C x a, wireValue C x b] := by
      intro x hx
      have := gate_val C x k hkl (by rw [hx]; exact hread)
      rw [hx] at this
      rw [this, hab]
      rfl
    have hfilt := filter_succ (Sset C n X x4) k
    by_cases hZk : wireValue C Z (n + n + k) = false
    · rcases hops g hgm with hand | hor
      · -- AND gate: not in S
        have hkS : k ∉ Sset C n X x4 := by
          rw [mem_Sset]; rintro ⟨_, hgood, _⟩; rw [hga, hand] at hgood; cases hgood
        rw [hfilt, if_neg hkS]
        refine ⟨rep, hcard, ?_⟩
        intro w hw hZw p q hp hq
        by_cases hwk : w < n + n + k
        · exact hrep w hwk hZw p q hp hq
        have hwe : w = n + n + k := by omega
        subst hwe
        rw [hval _ hZlen, hand] at hZw
        rw [hval _ (hsplen p), hand] at hp
        rw [hval _ (hsplen q), hand] at hq
        simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true,
          Bool.and_eq_true, Bool.and_eq_false_iff] at hZw hp hq
        rcases hZw with h | h
        · exact hrep a ha h p q hp.1 hq.1
        · exact hrep b hb h p q hp.2 hq.2
      · -- OR gate
        have hZor := hZk
        rw [hval _ hZlen, hor] at hZor
        simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false,
          Bool.or_eq_false_iff] at hZor
        obtain ⟨hZa, hZb⟩ := hZor
        have hnew : ∀ x : List Bool, x.length = n + n →
            (wireValue C x (n + n + k) = true ↔ wireValue C x a = true ∨ wireValue C x b = true) := by
          intro x hx
          rw [hval x hx, hor]
          simp [GateOp.eval]
        by_cases hkS : k ∈ Sset C n X x4
        · rw [hfilt, if_pos hkS]
          have hkF : k ∉ (Sset C n X x4).filter (· < k) := by simp
          rw [Finset.card_insert_of_notMem hkF]
          obtain ⟨_, _, _, a', b', hab', ⟨p0, q0, hp0, hq0⟩, hdis⟩ := (mem_Sset C n X x4 k).1 hkS
          rw [hga, hab] at hab'
          simp only [List.cons.injEq, and_true] at hab'
          obtain ⟨rfl, rfl⟩ := hab'
          refine ⟨fun r => if rep r = rep q0 then rep p0 else rep r, ?_, ?_⟩
          · have := image_merge X rep (rep q0) (rep p0)
            omega
          · intro w hw hZw p q hp hq
            by_cases hwk : w < n + n + k
            · have := hrep w hwk hZw p q hp hq
              simp only [this]
            have hwe : w = n + n + k := by omega
            subst hwe
            have key : ∀ r : Fin n, wireValue C (incidenceInput {r} {x4}) (n + n + k) = true →
                (if rep r = rep q0 then rep p0 else rep r) = rep p0 := by
              intro r hr
              rcases (hnew _ (hsplen r)).1 hr with hra | hrb
              · have := hrep a ha hZa r p0 hra hp0
                split_ifs <;> simp_all
              · have := hrep b hb hZb r q0 hrb hq0
                simp [this]
            exact (key p hp).trans (key q hq).symm
        · rw [hfilt, if_neg hkS]
          refine ⟨rep, hcard, ?_⟩
          intro w hw hZw p q hp hq
          by_cases hwk : w < n + n + k
          · exact hrep w hwk hZw p q hp hq
          have hwe : w = n + n + k := by omega
          subst hwe
          -- not good: some side empty, or the sides meet
          have hng : ¬ Good C n X x4 k := fun h => hkS ((mem_Sset C n X x4 k).2 ⟨by omega, h⟩)
          have hcase : (∀ r : Fin n, wireValue C (incidenceInput {r} {x4}) a = false) ∨
              (∀ r : Fin n, wireValue C (incidenceInput {r} {x4}) b = false) ∨
              ∃ r : Fin n, wireValue C (incidenceInput {r} {x4}) a = true ∧
                wireValue C (incidenceInput {r} {x4}) b = true := by
            by_contra hc
            simp only [not_or, not_forall, not_exists, not_and, Bool.not_eq_false] at hc
            obtain ⟨⟨r1, hr1⟩, ⟨r2, hr2⟩, hr3⟩ := hc
            apply hng
            refine ⟨by rw [hga]; exact hor, hZk, a, b, by rw [hga]; exact hab, ⟨r1, r2, hr1, hr2⟩, ?_⟩
            intro r hr
            have := hr3 r hr
            simpa using this
          rcases (hnew _ (hsplen p)).1 hp with hpa | hpb <;>
            rcases (hnew _ (hsplen q)).1 hq with hqa | hqb
          · exact hrep a ha hZa p q hpa hqa
          · rcases hcase with h | h | ⟨r, hra, hrb⟩
            · rw [h p] at hpa; cases hpa
            · rw [h q] at hqb; cases hqb
            · rw [hrep a ha hZa p r hpa hra, hrep b hb hZb r q hrb hqb]
          · rcases hcase with h | h | ⟨r, hra, hrb⟩
            · rw [h q] at hqa; cases hqa
            · rw [h p] at hpb; cases hpb
            · rw [hrep b hb hZb p r hpb hrb, hrep a ha hZa r q hra hqa]
          · exact hrep b hb hZb p q hpb hqb
    · -- the new wire is true on Z: not in S, nothing to do
      have hkS : k ∉ Sset C n X x4 := by
        rw [mem_Sset]; rintro ⟨_, _, hz, _⟩; exact hZk hz
      rw [hfilt, if_neg hkS]
      refine ⟨rep, hcard, ?_⟩
      intro w hw hZw p q hp hq
      by_cases hwk : w < n + n + k
      · exact hrep w hwk hZw p q hp hq
      have hwe : w = n + n + k := by omega
      subst hwe
      exact absurd hZw hZk

end PEqualNP.Outside.L_meta_8801

open PEqualNP.Outside.L_meta_8801 in
theorem PEqualNP.Outside.L_meta_8801 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1)) (x4 : Fin x1), PEqualNP.TopForm.IsAO2 (x1 + x1) x2 → x2.output < x1 + x1 + x2.size → (∀ x7 ∈ x3, x2.eval (PEqualNP.GenericRejection.incidenceInput {x7} {x4}) = Bool.true) → x2.eval (PEqualNP.GenericRejection.incidenceInput x3ᶜ {x4}) = Bool.false → ∃ (x9 : Finset ℕ), x3.card ≤ x9.card + (1 : ℕ) ∧ ∀ x10 ∈ x9, x10 < x2.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput x3ᶜ {x4}) (x1 + x1 + x10) = Bool.false ∧ ∃ (x12 : ℕ) (x13 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs = [x12, x13] ∧ (∃ (x14 : Fin x1) (x15 : Fin x1), PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput {x14} {x4}) x12 = Bool.true ∧ PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput {x15} {x4}) x13 = Bool.true) ∧ ∀ (x14 : Fin x1), PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput {x14} {x4}) x12 = Bool.true → PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput {x14} {x4}) x13 = Bool.false := by
  classical
  intro n C X x4 hAO hout hall hZ
  obtain ⟨rep, hcard, hrep⟩ := main_inv n C X x4 hAO C.size le_rfl
  refine ⟨Sset C n X x4, ?_, ?_⟩
  · have hS : (Sset C n X x4).filter (· < C.size) = Sset C n X x4 := by
      apply Finset.filter_true_of_mem
      intro j hj
      exact ((mem_Sset C n X x4 j).1 hj).1
    rw [hS] at hcard
    have h1 : (X.image rep).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro u hu v hv
      rw [Finset.mem_image] at hu hv
      obtain ⟨p, hp, rfl⟩ := hu
      obtain ⟨q, hq, rfl⟩ := hv
      exact hrep C.output hout hZ p q (hall p hp) (hall q hq)
    omega
  · intro j hj
    obtain ⟨hjs, hgood⟩ := (mem_Sset C n X x4 j).1 hj
    exact ⟨hjs, hgood⟩
