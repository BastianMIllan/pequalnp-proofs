import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5300

open PEqualNP.CircuitLowerBounds

def Inv (x x' w w' : List Bool) : Prop :=
  w.length = w'.length ∧ x.length ≤ w.length ∧
  (∀ i, x.length ≤ i → w.getD i false = w'.getD i false) ∧
  (∀ i, i < x.length → w.getD i false = x.getD i false ∧ w'.getD i false = x'.getD i false)

def Good (x x' : List Bool) (g : Gate) : Prop :=
  (∀ i ∈ g.inputs, i < x.length → x.getD i false = x'.getD i false) ∨
  ((∀ i ∈ g.inputs, i < x.length) ∧
    g.op.eval (g.inputs.map fun i => x.getD i false) =
      g.op.eval (g.inputs.map fun i => x'.getD i false))

theorem getD_snoc (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false = if i < w.length then w.getD i false
      else if i = w.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, i - w.length = k + 1 := ⟨i - w.length - 1, by omega⟩
    rw [hk]; simp

theorem fold_inv (x x' : List Bool) :
    ∀ (gs : List Gate), (∀ g ∈ gs, Good x x' g) → ∀ w w', Inv x x' w w' →
      Inv x x' (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  intro gs
  induction gs with
  | nil => intro _ w w' h; exact h
  | cons g gs ih =>
    intro hg w w' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hx, hhi, hlo⟩ := h
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      rcases hg g (List.mem_cons_self) with h1 | ⟨h2, h3⟩
      · congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hlt : i < x.length
        · rw [(hlo i hlt).1, (hlo i hlt).2]; exact h1 i hi hlt
        · exact hhi i (by omega)
      · have e1 : (g.inputs.map fun i => w.getD i false) =
            (g.inputs.map fun i => x.getD i false) :=
          List.map_congr_left (fun i hi => (hlo i (h2 i hi)).1)
        have e2 : (g.inputs.map fun i => w'.getD i false) =
            (g.inputs.map fun i => x'.getD i false) :=
          List.map_congr_left (fun i hi => (hlo i (h2 i hi)).2)
        rw [e1, e2]; exact h3
    refine ⟨by simp [hl], by simp; omega, ?_, ?_⟩
    · intro i hi
      rw [getD_snoc, getD_snoc, hv, ← hl]
      split_ifs with h1 h2
      · exact hhi i hi
      · rfl
      · rfl
    · intro i hi
      rw [getD_snoc, getD_snoc, if_pos (by omega), if_pos (by omega)]
      exact hlo i hi

def inp (c a b : Bool) : List Bool :=
  [a, c, false, !c, b, false, false, false, false, !a]

def shp (s : Fin 4) : List ℕ := [[0, 4], [4, 0], [9, 4], [4, 9]].getD s.val []

def opb (bo : Bool) : GateOp := if bo then GateOp.and else GateOp.or

def gv (bo : Bool) (s : Fin 4) (c a b : Bool) : Bool :=
  (opb bo).eval ((shp s).map fun i => (inp c a b).getD i false)

set_option maxRecDepth 100000 in
theorem finite_choice : ∀ (bo4 bo5 r4 r5 : Bool) (s4 s5 : Fin 4),
    ∃ c a b a' b' : Bool, (if c = true then a else b) ≠ (if c = true then a' else b') ∧
      (r4 = false → a = a') ∧ (r4 = true → gv bo4 s4 c a b = gv bo4 s4 c a' b') ∧
      (r5 = false → a = a') ∧ (r5 = true → gv bo5 s5 c a b = gv bo5 s5 c a' b') := by
  unfold gv opb shp inp
  decide

theorem shape_of (g : Gate) (hf : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
    g.inputs.length ≤ 2) (hn : g.op = GateOp.not → g.inputs.length ≤ 1)
    (h09 : 0 ∈ g.inputs ∨ 9 ∈ g.inputs) (h4 : 4 ∈ g.inputs) :
    ∃ bo s, g = ⟨opb bo, shp s⟩ := by
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, hlen⟩ := hf
  simp only at hop hlen hn h09 h4
  have hl2 : l.length = 2 := by
    rcases l with _ | ⟨p, _ | ⟨q, l⟩⟩
    · simp at h4
    · simp at h4 h09; omega
    · simp at hlen ⊢; omega
  have hop' : op = GateOp.and ∨ op = GateOp.or := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have := hn h; omega
  obtain ⟨bo, hbo⟩ : ∃ bo, op = opb bo := by
    rcases hop' with h | h
    · exact ⟨true, by simp [opb, h]⟩
    · exact ⟨false, by simp [opb, h]⟩
  subst hbo
  rcases l with _ | ⟨p, _ | ⟨q, _ | ⟨r, l⟩⟩⟩
  · simp at hl2
  · simp at hl2
  · simp at h4 h09
    have hpq : (p = 0 ∧ q = 4) ∨ (p = 4 ∧ q = 0) ∨ (p = 9 ∧ q = 4) ∨ (p = 4 ∧ q = 9) := by
      omega
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨bo, 0, rfl⟩
    · exact ⟨bo, 1, rfl⟩
    · exact ⟨bo, 2, rfl⟩
    · exact ⟨bo, 3, rfl⟩
  · simp at hl2

theorem agree4 (c a b b' : Bool) (i : ℕ) (hi : i ≠ 4) :
    (inp c a b).getD i false = (inp c a b').getD i false := by
  by_cases h : i < 10
  · unfold inp; interval_cases i <;> simp_all
  · rw [List.getD_eq_default _ _ (by simp [inp]; omega),
      List.getD_eq_default _ _ (by simp [inp]; omega)]

theorem agree049 (c a b a' b' : Bool) (i : ℕ) (h0 : i ≠ 0) (h4 : i ≠ 4) (h9 : i ≠ 9) :
    (inp c a b).getD i false = (inp c a' b').getD i false := by
  by_cases h : i < 10
  · unfold inp; interval_cases i <;> simp_all
  · rw [List.getD_eq_default _ _ (by simp [inp]; omega),
      List.getD_eq_default _ _ (by simp [inp]; omega)]

theorem no_direct (i : ℕ) (hi : i < 10) :
    ∃ c a b : Bool, (inp c a b).getD i false ≠ (if c = true then a else b) := by
  unfold inp
  interval_cases i <;> decide

theorem shp_lt (s : Fin 4) : ∀ i ∈ shp s, i < 10 := by
  fin_cases s <;> simp [shp]

end PEqualNP.Outside.L_meta_5300

open PEqualNP.Outside.L_meta_5300 in
theorem PEqualNP.Outside.L_meta_5300 : ∀ (x1 x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : ℕ),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x7 → (∀ x9 ∈ x7.gates, x9.op = PEqualNP.CircuitLowerBounds.GateOp.not → x9.inputs.length ≤ (1 : ℕ)) → (∀ x10 ∈ x1 ++ x2 ++ x3, (0 : ℕ) ∉ x10.inputs ∧ (9 : ℕ) ∉ x10.inputs) → (∀ x11 ∈ [x4, x5], (0 : ℕ) ∈ x11.inputs ∨ (9 : ℕ) ∈ x11.inputs) → (∀ (x12 x13 x14 : Bool), x7.eval [x13, x12, Bool.false, !x12, x14, Bool.false, Bool.false, Bool.false, Bool.false, !x13] = if x12 = Bool.true then x13 else x14) → ∃ x13 ∈ x1 ++ x2 ++ x3, (4 : ℕ) ∈ x13.inputs := by
  intro x1 x2 x3 x4 x5 x6 x7 hf hn h09 hlit hev
  by_contra hno
  push Not at hno
  have m4 : x4 ∈ x7.gates := by
    show x4 ∈ x1 ++ x4 :: (x2 ++ x5 :: x3)
    simp
  have m5 : x5 ∈ x7.gates := by
    show x5 ∈ x1 ++ x4 :: (x2 ++ x5 :: x3)
    simp
  have k4 : ∃ bo s, (4 ∈ x4.inputs → x4 = ⟨opb bo, shp s⟩) := by
    by_cases h : 4 ∈ x4.inputs
    · obtain ⟨bo, s, e⟩ := shape_of x4 (hf x4 m4) (hn x4 m4) (hlit x4 (by simp)) h
      exact ⟨bo, s, fun _ => e⟩
    · exact ⟨true, 0, fun h' => absurd h' h⟩
  have k5 : ∃ bo s, (4 ∈ x5.inputs → x5 = ⟨opb bo, shp s⟩) := by
    by_cases h : 4 ∈ x5.inputs
    · obtain ⟨bo, s, e⟩ := shape_of x5 (hf x5 m5) (hn x5 m5) (hlit x5 (by simp)) h
      exact ⟨bo, s, fun _ => e⟩
    · exact ⟨true, 0, fun h' => absurd h' h⟩
  obtain ⟨bo4, s4, e4⟩ := k4
  obtain ⟨bo5, s5, e5⟩ := k5
  obtain ⟨c, a, b, a', b', hne, f4, t4, f5, t5⟩ :=
    finite_choice bo4 bo5 (decide (4 ∈ x4.inputs)) (decide (4 ∈ x5.inputs)) s4 s5
  have hgood : ∀ g ∈ x7.gates, Good (inp c a b) (inp c a' b') g := by
    intro g hg
    have hg2 : g ∈ x1 ++ x4 :: (x2 ++ x5 :: x3) := hg
    have hg' : g ∈ x1 ++ x2 ++ x3 ∨ g = x4 ∨ g = x5 := by
      simp only [List.mem_append, List.mem_cons] at hg2
      rcases hg2 with h | h | h | h | h
      · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ h))
      · exact Or.inr (Or.inl h)
      · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ h))
      · exact Or.inr (Or.inr h)
      · exact Or.inl (List.mem_append_right _ h)
    rcases hg' with hg' | rfl | rfl
    · left
      intro i hi _
      obtain ⟨n0, n9⟩ := h09 g hg'
      exact agree049 c a b a' b' i (by rintro rfl; exact n0 hi)
        (by rintro rfl; exact hno g hg' hi) (by rintro rfl; exact n9 hi)
    · by_cases h : 4 ∈ g.inputs
      · right
        have e := e4 h
        have tt := t4 (by simp [h])
        rw [e]
        refine ⟨fun i hi => by simpa [inp] using shp_lt s4 i hi, ?_⟩
        exact tt
      · left
        have ha := f4 (by simp [h])
        subst ha
        intro i hi _
        exact agree4 c a b b' i (by rintro rfl; exact h hi)
    · by_cases h : 4 ∈ g.inputs
      · right
        have e := e5 h
        have tt := t5 (by simp [h])
        rw [e]
        refine ⟨fun i hi => by simpa [inp] using shp_lt s5 i hi, ?_⟩
        exact tt
      · left
        have ha := f5 (by simp [h])
        subst ha
        intro i hi _
        exact agree4 c a b b' i (by rintro rfl; exact h hi)
  have hinv := fold_inv (inp c a b) (inp c a' b') x7.gates hgood (inp c a b) (inp c a' b')
    ⟨rfl, le_refl _, fun i hi => by
      rw [List.getD_eq_default _ _ hi, List.getD_eq_default _ _ (by simpa [inp] using hi)],
     fun i _ => ⟨rfl, rfl⟩⟩
  have hx6 : x7.output = x6 := rfl
  by_cases hlt : x6 < 10
  · obtain ⟨c0, a0, b0, hbad⟩ := no_direct x6 hlt
    have hinv0 := fold_inv (inp c0 a0 b0) (inp c0 a0 b0) x7.gates
      (fun g _ => Or.inl (fun _ _ _ => rfl)) (inp c0 a0 b0) (inp c0 a0 b0)
      ⟨rfl, le_refl _, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩
    obtain ⟨_, _, _, hlo⟩ := hinv0
    have h0 := hev c0 a0 b0
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires at h0
    rw [hx6] at h0
    have := (hlo x6 (by simp [inp]; omega)).1
    simp only [inp] at this hbad
    rw [this] at h0
    exact hbad h0
  · have heq : x7.eval (inp c a b) = x7.eval (inp c a' b') := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
      obtain ⟨_, _, hhi, _⟩ := hinv
      exact hhi _ (by rw [hx6]; simp [inp]; omega)
    have h1 := hev c a b
    have h2 := hev c a' b'
    simp only [inp] at heq
    rw [h1, h2] at heq
    exact hne heq
