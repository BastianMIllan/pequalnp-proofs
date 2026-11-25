import Mathlib
import PEqualNP.Defs

-- Collapse a fan-in-two monotone circuit into an AND-count circuit with one gate per AND gate:
-- every wire becomes a side (a set of variables and a set of earlier AND gates, ORed), OR gates
-- merge sides, and the extra last variable (always true) stands for the constant true side.
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.L_meta_6738 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∃ (x4 : PEqualNP.AndCount.AndCountCircuit (x1 + (1 : ℕ))), x4.WellFormed ∧ x4.size ≤ {x5 : Fin x2.gates.length | (x2.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ∧ ∀ (x5 : Finset (Fin x1)), x4.eval (Insert.insert (Fin.last x1) (Finset.map Fin.castSuccEmb x5)) = PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x6 : Fin x1) => Decidable.decide (x6 ∈ x5) := by
  classical
  intro n C hMono
  have op_and_eval (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := rfl
  have op_or_eval (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := rfl
  have sideTrue_def {m : ℕ} (U B : Finset (Fin (n + 1))) (F : Finset (Fin m)) (i : Fin m) (v : Fin m → Bool) :
      PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i v =
      decide ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := rfl
  have gateValFuel_succ (E : PEqualNP.AndCount.AndCountCircuit (n + 1)) (U : Finset (Fin (n + 1))) (d : ℕ) (i : Fin E.size) :
      E.gateValFuel U (d + 1) i =
        (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U d) &&
         PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U d)) := rfl
  have gateVal_def (E : PEqualNP.AndCount.AndCountCircuit (n + 1)) (U : Finset (Fin (n + 1))) (i : Fin E.size) :
      E.gateVal U i = E.gateValFuel U E.size i := rfl
  have eval_def (E : PEqualNP.AndCount.AndCountCircuit (n + 1)) (U : Finset (Fin (n + 1))) :
      E.eval U = decide ((∃ v ∈ E.outVars, v ∈ U) ∨ ∃ j ∈ E.outGates, E.gateVal U j = true) := rfl
  let wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w
  have wiresFrom_append (gs₁ gs₂ : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
    simp [wiresFrom, List.foldl_append]
  have wiresFrom_ext (gs : List PEqualNP.CircuitLowerBounds.Gate) : ∀ w : List Bool,
      ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
    induction gs with
    | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
    | cons g gs ih =>
      intro w
      let v := g.op.eval (g.inputs.map fun i => w.getD i false)
      obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
      refine ⟨v :: t, ?_, by simp [hl]⟩
      have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
      rw [hstep, ht]
      simp
  have length_wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      (wiresFrom gs w).length = w.length + gs.length := by
    obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
    rw [ht, List.length_append, hl]
  have getD_wiresFrom_lt (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ)
      (h : i < w.length) : (wiresFrom gs w).getD i false = w.getD i false := by
    obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
    rw [ht, List.getD_append _ _ _ _ h]
  have getD_wiresFrom_take (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (k i : ℕ)
      (hk : k ≤ gs.length) :
      (wiresFrom (gs.take k) w).getD i false =
        if i < w.length + k then (wiresFrom gs w).getD i false else false := by
    have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
      rw [length_wiresFrom, List.length_take, min_eq_left hk]
    split_ifs with hi
    · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
      conv_rhs => rw [hsplit, wiresFrom_append]
      exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
    · rw [List.getD_eq_default]
      omega
  have getD_wiresFrom_gate (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (k : ℕ)
      (hk : k < gs.length) :
      (wiresFrom gs w).getD (w.length + k) false =
        (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
          if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
    have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
      have h1 := (List.take_append_drop k gs).symm
      rw [List.drop_eq_getElem_cons hk] at h1
      exact h1
    have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
      rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
    have heq : wiresFrom gs w =
        wiresFrom (gs.drop (k + 1))
          (wiresFrom (gs.take k) w ++
            [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
      conv_lhs => rw [hsplit, wiresFrom_append]
      rfl
    rw [heq, getD_wiresFrom_lt]
    · conv_lhs => rw [← hlen, List.getD_append_right _ _ _ _ (le_refl _)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
    · rw [List.length_append, hlen]; simp
  let andFin : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun i : Fin C.gates.length => (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  have hAndCard : andFin.card =
      {x4 : Fin C.gates.length | (C.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
    have hcoe : (andFin : Set (Fin C.gates.length)) =
        {x4 : Fin C.gates.length | (C.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
      ext i; simp [andFin]
    rw [← hcoe, Set.ncard_coe_finset]
  let k : ℕ := andFin.card
  let ordFin : Fin k ↪o Fin C.gates.length := andFin.orderEmbOfFin rfl
  let ord (i : Fin k) : ℕ := (ordFin i).val
  have ord_lt_iff (a b : Fin k) : ord a < ord b ↔ a < b := by
    change (ordFin a).val < (ordFin b).val ↔ a < b
    exact ordFin.lt_iff_lt
  have ok (i : Fin k) : ∃ h : ord i < C.gates.length, C.gates[ord i].op = PEqualNP.CircuitLowerBounds.GateOp.and := by
    have hmem : ordFin i ∈ andFin := andFin.orderEmbOfFin_mem rfl i
    have hop : (C.gates.get (ordFin i)).op = PEqualNP.CircuitLowerBounds.GateOp.and :=
      (Finset.mem_filter.mp hmem).2
    exact ⟨(ordFin i).isLt, hop⟩
  have allAnd (j : ℕ) (hj : j < C.gates.length)
      (ha : C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.and) : ∃ i : Fin k, ord i = j := by
    have hjMem : (⟨j, hj⟩ : Fin C.gates.length) ∈ andFin :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
    have hr : (⟨j, hj⟩ : Fin C.gates.length) ∈ Set.range ordFin := by
      rw [Finset.range_orderEmbOfFin]; exact hjMem
    obtain ⟨i, hi⟩ := hr
    exact ⟨i, congrArg Fin.val hi⟩
  let collVal (U : Finset (Fin (n + 1))) (v : Fin k → Bool)
      (s : Finset (Fin (n + 1)) × Finset (Fin k)) : Bool :=
    decide ((∃ x ∈ s.1, x ∈ U) ∨ ∃ i ∈ s.2, v i = true)
  let collCollect (L : List ℕ) (s : ℕ → Finset (Fin (n + 1)) × Finset (Fin k)) :
      Finset (Fin (n + 1)) × Finset (Fin k) :=
    ⟨L.toFinset.biUnion (fun j => (s j).1), L.toFinset.biUnion (fun j => (s j).2)⟩
  have collCollect_true (U : Finset (Fin (n + 1))) (v : Fin k → Bool)
      (L : List ℕ) (s : ℕ → Finset (Fin (n + 1)) × Finset (Fin k)) :
      collVal U v (collCollect L s) = true ↔ ∃ j ∈ L, collVal U v (s j) = true := by
    simp only [collVal, collCollect, decide_eq_true_eq, Finset.mem_biUnion, List.mem_toFinset]
    constructor
    · rintro (⟨x, ⟨j, hj, hxj⟩, hxU⟩ | ⟨i, ⟨j, hj, hij⟩, hvi⟩)
      · exact ⟨j, hj, Or.inl ⟨x, hxj, hxU⟩⟩
      · exact ⟨j, hj, Or.inr ⟨i, hij, hvi⟩⟩
    · rintro ⟨j, hj, ⟨x, hxj, hxU⟩ | ⟨i, hij, hvi⟩⟩
      · exact Or.inl ⟨x, ⟨j, hj, hxj⟩, hxU⟩
      · exact Or.inr ⟨i, ⟨j, hj, hij⟩, hvi⟩
  let inp (U : Finset (Fin (n + 1))) : List Bool :=
    List.ofFn (fun i : Fin n => decide (Fin.castSucc i ∈ U))
  have inp_len (U : Finset (Fin (n + 1))) : (inp U).length = n := by simp [inp]
  let collOrig (U : Finset (Fin (n + 1))) (w : ℕ) : Bool :=
    (wiresFrom C.gates (inp U)).getD w false
  have coll_gate (U : Finset (Fin (n + 1))) (j : ℕ) (h : j < C.gates.length) :
      collOrig U (n + j) = C.gates[j].op.eval (C.gates[j].inputs.map
        (fun i => if i < n + j then collOrig U i else false)) := by
    have := getD_wiresFrom_gate C.gates (inp U) j h
    rw [inp_len] at this
    exact this
  let collV (U : Finset (Fin (n + 1))) (j : Fin k) : Bool := collOrig U (n + ord j)
  have coll_prior : ∀ w : ℕ,
      (∀ i < w, ∃ s : Finset (Fin (n + 1)) × Finset (Fin k), (∀ j ∈ s.2, n + ord j ≤ i) ∧
        ∀ U : Finset (Fin (n + 1)), collVal U (collV U) s = collOrig U i) →
      ∃ f : ℕ → Finset (Fin (n + 1)) × Finset (Fin k), (∀ i j, j ∈ (f i).2 → n + ord j < w) ∧
        ∀ i (U : Finset (Fin (n + 1))), collVal U (collV U) (f i) =
          if i < w then collOrig U i else false := by
    intro w ih
    let f (i : ℕ) : Finset (Fin (n + 1)) × Finset (Fin k) :=
      if hi : i < w then (ih i hi).choose else (∅, ∅)
    refine ⟨f, ?_, ?_⟩
    · intro i j hj
      by_cases hi : i < w
      · simp only [f, dite_eq_left hi] at hj
        exact Nat.lt_of_le_of_lt ((ih i hi).choose_spec.1 _ hj) hi
      · simp [f, hi] at hj
    · intro i U
      by_cases hi : i < w
      · simpa only [f, dite_eq_left hi, ite_eq_left hi] using (ih i hi).choose_spec.2 U
      · simp [f, hi, collVal]
  have coll_wires : ∀ w : ℕ,
      ∃ s : Finset (Fin (n + 1)) × Finset (Fin k), (∀ j ∈ s.2, n + ord j ≤ w) ∧
        ∀ U : Finset (Fin (n + 1)), collVal U (collV U) s = collOrig U w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases hinput : w < n
      · let p : Fin (n + 1) := Fin.castSucc ⟨w, hinput⟩
        refine ⟨({p}, ∅), by simp, ?_⟩
        intro U
        change collVal U (collV U) ({p}, ∅) = (wiresFrom C.gates (inp U)).getD w false
        rw [getD_wiresFrom_lt _ _ _ (by rw [inp_len]; exact hinput)]
        rw [List.getD_eq_getElem _ _ (by rw [inp_len]; exact hinput)]
        simp [collVal, p, inp]
      · let j := w - n
        have hw : n + j = w := by dsimp [j]; omega
        by_cases hj : j < C.gates.length
        · obtain h | h := (hMono C.gates[j] (List.getElem_mem hj)).1
          · obtain ⟨z, hz⟩ := allAnd j hj h
            exact ⟨(∅, {z}), by simp [hz, hw], fun U => by simp [collVal, collV, hz, hw]⟩
          · obtain ⟨f, hf, he⟩ := coll_prior w ih
            refine ⟨collCollect C.gates[j].inputs f, ?_, ?_⟩
            · intro z hz
              obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
              exact Nat.le_of_lt (hf i z hi)
            · intro U
              rw [← hw, coll_gate U j hj, show C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.or from h, op_or_eval]
              apply Bool.eq_iff_iff.mpr
              rw [collCollect_true]
              simp only [List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
              simp_rw [he, hw]
        · refine ⟨(∅, ∅), by simp, ?_⟩
          intro U
          change collVal U (collV U) (∅, ∅) = (wiresFrom C.gates (inp U)).getD w false
          rw [List.getD_eq_default _ _ (by rw [length_wiresFrom, inp_len]; omega)]
          simp [collVal]
  have coll_sides (i : Fin k) :
      ∃ l r : Finset (Fin (n + 1)) × Finset (Fin k),
        (∀ z ∈ l.2, z < i) ∧ (∀ z ∈ r.2, z < i) ∧
        ∀ U : Finset (Fin (n + 1)), U.Nonempty →
          (collVal U (collV U) l && collVal U (collV U) r) = collV U i := by
    obtain ⟨h, hop⟩ := ok i
    let g := C.gates[ord i]
    have hlen := (hMono g (List.getElem_mem h)).2
    obtain ⟨f, hf, he⟩ := coll_prior (n + ord i) (fun w _ => coll_wires w)
    have ltj (a : ℕ) (z : Fin k) (hz : z ∈ (f a).2) : z < i :=
      (ord_lt_iff z i).mp (Nat.lt_of_add_lt_add_left (hf _ _ hz))
    have gate (U : Finset (Fin (n + 1))) :
        collV U i = (g.inputs.map fun j => collVal U (collV U) (f j)).all id := by
      change collOrig U (n + ord i) = _
      rw [coll_gate U (ord i) h, hop, op_and_eval]
      simp only [he, g]
    cases hL : g.inputs with
    | nil =>
      refine ⟨(Finset.univ, ∅), (Finset.univ, ∅), by simp, by simp, ?_⟩
      intro U hu
      rw [gate, hL]
      simpa [collVal] using (show ∃ x, x ∈ U from hu)
    | cons a L =>
      cases L with
      | nil =>
        refine ⟨f a, f a, ltj a, ltj a, ?_⟩
        intro U _
        simp [gate, hL]
      | cons b L =>
        have hem : L = [] := by rw [hL] at hlen; simpa using hlen
        subst L
        refine ⟨f a, f b, ltj a, ltj b, ?_⟩
        intro U _
        simp [gate, hL]
  choose lSide rSide hlSide hrSide hvSide using coll_sides
  obtain ⟨oSide, _, hoSide⟩ := coll_wires C.output
  let D0 : PEqualNP.AndCount.AndCountCircuit (n + 1) :=
    ⟨k, fun i => (lSide i).1, fun i => (lSide i).2, fun i => (rSide i).1, fun i => (rSide i).2,
      oSide.1, oSide.2⟩
  have hD0WF : D0.WellFormed := fun i => ⟨hlSide i, hrSide i⟩
  have hD0Eval : ∀ U : Finset (Fin (n + 1)), U.Nonempty → D0.eval U = collVal U (collV U) oSide := by
    intro U hU
    have fuel (d : ℕ) : ∀ i : Fin k, i.val < d → D0.gateValFuel U d i = collV U i := by
      induction d with
      | zero => intro i; omega
      | succ d ih =>
        intro i hd
        have eqSide (s : Finset (Fin (n + 1)) × Finset (Fin k)) (hs : ∀ z ∈ s.2, z < i) :
            PEqualNP.AndCount.AndCountCircuit.sideTrue U s.1 s.2 i (D0.gateValFuel U d) = collVal U (collV U) s := by
          rw [sideTrue_def]
          dsimp only [collVal]
          congr 1
          apply propext
          apply or_congr_right
          constructor
          · rintro ⟨j, hj, hji, hval⟩
            exact ⟨j, hj, (ih j (by have := hji; change j.val < i.val at this; omega)).symm.trans hval⟩
          · rintro ⟨j, hj, hval⟩
            have hji := hs j hj
            exact ⟨j, hj, hji, (ih j (by change j.val < i.val at hji; omega)).trans hval⟩
        rw [gateValFuel_succ]
        dsimp only [D0]
        rw [eqSide _ (hlSide i), eqSide _ (hrSide i), hvSide i U hU]
    have gate (i : Fin k) : D0.gateVal U i = collV U i := by
      rw [gateVal_def]
      exact fuel k i i.isLt
    rw [eval_def]
    simp only [gate, collVal, D0]
  refine ⟨D0, hD0WF, ?_, ?_⟩
  · change k ≤ _
    exact hAndCard.le
  · intro x5
    have hU : (Insert.insert (Fin.last n) (Finset.map Fin.castSuccEmb x5) : Finset (Fin (n + 1))).Nonempty :=
      Finset.insert_nonempty _ _
    rw [hD0Eval _ hU, hoSide]
    have hmem (i : Fin n) :
        (Fin.castSucc i ∈ (Insert.insert (Fin.last n) (Finset.map Fin.castSuccEmb x5) : Finset (Fin (n + 1)))) ↔ i ∈ x5 := by
      rw [Finset.mem_insert]
      constructor
      · rintro (h | h)
        · exact absurd h (Fin.castSucc_ne_last i)
        · exact (Finset.mem_map' Fin.castSuccEmb).mp h
      · intro h
        exact Or.inr ((Finset.mem_map' Fin.castSuccEmb).mpr h)
    have hinp : inp (Insert.insert (Fin.last n) (Finset.map Fin.castSuccEmb x5)) =
        List.ofFn (fun i : Fin n => decide (i ∈ x5)) := by
      dsimp only [inp]
      congr 1
      funext i
      exact decide_eq_decide.mpr (hmem i)
    change (wiresFrom C.gates (inp (Insert.insert (Fin.last n) (Finset.map Fin.castSuccEmb x5)))).getD C.output false =
      (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn (fun i : Fin n => decide (i ∈ x5)))).getD C.output false
    rw [hinp]
