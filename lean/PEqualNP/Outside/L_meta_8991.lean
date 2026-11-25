import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8991

open PEqualNP.CircuitLowerBounds

-- dual rail: every original gate j becomes a positive gate (wire 2n+2j) and a negative gate
-- (wire 2n+2j+1); constants (wires not yet built, NOT of nothing) are folded into the gates.

def val (u : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr k => u.getD k false

def rt : Bool ⊕ ℕ → Option ℕ
  | Sum.inl _ => none
  | Sum.inr k => some k

def mkAnd (l : List (Bool ⊕ ℕ)) : Gate :=
  if (Sum.inl false : Bool ⊕ ℕ) ∈ l then ⟨GateOp.or, []⟩ else ⟨GateOp.and, l.filterMap rt⟩

def mkOr (l : List (Bool ⊕ ℕ)) : Gate :=
  if (Sum.inl true : Bool ⊕ ℕ) ∈ l then ⟨GateOp.and, []⟩ else ⟨GateOp.or, l.filterMap rt⟩

def pos (n i : ℕ) : ℕ := if i < n then i else 2 * n + 2 * (i - n)

def neg (n i : ℕ) : ℕ := if i < n then n + i else 2 * n + 2 * (i - n) + 1

def src (n j : ℕ) (b : Bool) (i : ℕ) : Bool ⊕ ℕ :=
  if i < n + j then Sum.inr (if b then pos n i else neg n i) else Sum.inl (!b)

def posGate (n j : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => mkAnd (g.inputs.map (src n j true))
  | GateOp.or => mkOr (g.inputs.map (src n j true))
  | GateOp.not => mkAnd ((g.inputs.take 1).map (src n j false))
  | _ => mkAnd []

def negGate (n j : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => mkOr (g.inputs.map (src n j false))
  | GateOp.or => mkAnd (g.inputs.map (src n j false))
  | GateOp.not => mkOr ((g.inputs.take 1).map (src n j true))
  | _ => mkAnd []

def dr (n : ℕ) : ℕ → List Gate → List Gate
  | _, [] => []
  | j, g :: gs => posGate n j g :: negGate n j g :: dr n (j + 1) gs

def R (n j : ℕ) (w w' : List Bool) : Prop :=
  ∀ i < n + j, w'.getD (pos n i) false = w.getD i false ∧ w'.getD (neg n i) false = !w.getD i false

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem all_false (u : List Bool) (l : List (Bool ⊕ ℕ)) (h : (Sum.inl false : Bool ⊕ ℕ) ∈ l) :
    (l.map (val u)).all id = false := by
  rw [Bool.eq_false_iff]
  intro h2
  rw [List.all_eq_true] at h2
  have := h2 _ (List.mem_map.2 ⟨_, h, rfl⟩)
  simp [val] at this

theorem all_true (u : List Bool) : ∀ (l : List (Bool ⊕ ℕ)), (Sum.inl false : Bool ⊕ ℕ) ∉ l →
    ((l.filterMap rt).map fun i => u.getD i false).all id = (l.map (val u)).all id
  | [], _ => rfl
  | Sum.inl c :: t, h => by
    have ht : (Sum.inl false : Bool ⊕ ℕ) ∉ t := fun hh => h (List.mem_cons_of_mem _ hh)
    cases c
    · exact absurd List.mem_cons_self h
    · show ((t.filterMap rt).map fun i => u.getD i false).all id = (true && (t.map (val u)).all id)
      rw [Bool.true_and]
      exact all_true u t ht
  | Sum.inr k :: t, h => by
    have ht : (Sum.inl false : Bool ⊕ ℕ) ∉ t := fun hh => h (List.mem_cons_of_mem _ hh)
    show (u.getD k false && ((t.filterMap rt).map fun i => u.getD i false).all id) =
      (u.getD k false && (t.map (val u)).all id)
    rw [all_true u t ht]

theorem any_true (u : List Bool) (l : List (Bool ⊕ ℕ)) (h : (Sum.inl true : Bool ⊕ ℕ) ∈ l) :
    (l.map (val u)).any id = true := by
  rw [List.any_eq_true]
  exact ⟨_, List.mem_map.2 ⟨_, h, rfl⟩, rfl⟩

theorem any_false (u : List Bool) : ∀ (l : List (Bool ⊕ ℕ)), (Sum.inl true : Bool ⊕ ℕ) ∉ l →
    ((l.filterMap rt).map fun i => u.getD i false).any id = (l.map (val u)).any id
  | [], _ => rfl
  | Sum.inl c :: t, h => by
    have ht : (Sum.inl true : Bool ⊕ ℕ) ∉ t := fun hh => h (List.mem_cons_of_mem _ hh)
    cases c
    · show ((t.filterMap rt).map fun i => u.getD i false).any id = (false || (t.map (val u)).any id)
      rw [Bool.false_or]
      exact any_false u t ht
    · exact absurd List.mem_cons_self h
  | Sum.inr k :: t, h => by
    have ht : (Sum.inl true : Bool ⊕ ℕ) ∉ t := fun hh => h (List.mem_cons_of_mem _ hh)
    show (u.getD k false || ((t.filterMap rt).map fun i => u.getD i false).any id) =
      (u.getD k false || (t.map (val u)).any id)
    rw [any_false u t ht]

theorem evalAnd (u : List Bool) (l : List (Bool ⊕ ℕ)) :
    (mkAnd l).op.eval ((mkAnd l).inputs.map fun i => u.getD i false) = (l.map (val u)).all id := by
  unfold mkAnd
  split_ifs with h
  · exact (all_false u l h).symm
  · exact all_true u l h

theorem evalOr (u : List Bool) (l : List (Bool ⊕ ℕ)) :
    (mkOr l).op.eval ((mkOr l).inputs.map fun i => u.getD i false) = (l.map (val u)).any id := by
  unfold mkOr
  split_ifs with h
  · exact (any_true u l h).symm
  · exact any_false u l h

theorem mkAnd_ok (l : List (Bool ⊕ ℕ)) :
    (mkAnd l).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (mkAnd l).inputs.length ≤ l.length := by
  unfold mkAnd
  split_ifs
  · simp
  · simp [List.length_filterMap_le]

theorem mkOr_ok (l : List (Bool ⊕ ℕ)) :
    (mkOr l).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (mkOr l).inputs.length ≤ l.length := by
  unfold mkOr
  split_ifs
  · simp
  · simp [List.length_filterMap_le]

theorem posGate_cases (n j : ℕ) (g : Gate) : ∃ l : List (Bool ⊕ ℕ), l.length ≤ g.inputs.length ∧
    (posGate n j g = mkAnd l ∨ posGate n j g = mkOr l) := by
  unfold posGate
  split
  all_goals first
    | exact ⟨_, by simp <;> omega, Or.inl rfl⟩
    | exact ⟨_, by simp <;> omega, Or.inr rfl⟩

theorem negGate_cases (n j : ℕ) (g : Gate) : ∃ l : List (Bool ⊕ ℕ), l.length ≤ g.inputs.length ∧
    (negGate n j g = mkAnd l ∨ negGate n j g = mkOr l) := by
  unfold negGate
  split
  all_goals first
    | exact ⟨_, by simp <;> omega, Or.inl rfl⟩
    | exact ⟨_, by simp <;> omega, Or.inr rfl⟩

theorem gate_ok (g0 : Gate) (k : ℕ) (h : ∃ l : List (Bool ⊕ ℕ), l.length ≤ k ∧ (g0 = mkAnd l ∨ g0 = mkOr l))
    (hk : k ≤ 2) : g0.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g0.inputs.length ≤ 2 := by
  obtain ⟨l, hl, h | h⟩ := h
  · subst h
    exact ⟨(mkAnd_ok l).1, by have := (mkAnd_ok l).2; omega⟩
  · subst h
    exact ⟨(mkOr_ok l).1, by have := (mkOr_ok l).2; omega⟩

theorem posGate_and (n j : ℕ) (g : Gate) (h : g.op = GateOp.and) :
    posGate n j g = mkAnd (g.inputs.map (src n j true)) := by simp only [posGate, h]
theorem posGate_or (n j : ℕ) (g : Gate) (h : g.op = GateOp.or) :
    posGate n j g = mkOr (g.inputs.map (src n j true)) := by simp only [posGate, h]
theorem posGate_not (n j : ℕ) (g : Gate) (h : g.op = GateOp.not) :
    posGate n j g = mkAnd ((g.inputs.take 1).map (src n j false)) := by simp only [posGate, h]
theorem negGate_and (n j : ℕ) (g : Gate) (h : g.op = GateOp.and) :
    negGate n j g = mkOr (g.inputs.map (src n j false)) := by simp only [negGate, h]
theorem negGate_or (n j : ℕ) (g : Gate) (h : g.op = GateOp.or) :
    negGate n j g = mkAnd (g.inputs.map (src n j false)) := by simp only [negGate, h]
theorem negGate_not (n j : ℕ) (g : Gate) (h : g.op = GateOp.not) :
    negGate n j g = mkOr ((g.inputs.take 1).map (src n j true)) := by simp only [negGate, h]

theorem val_src (n j : ℕ) (b : Bool) (i : ℕ) (w w' : List Bool) (hw : w.length = n + j)
    (hR : R n j w w') :
    val w' (src n j b i) = (if b then w.getD i false else !w.getD i false) := by
  by_cases h : i < n + j
  · cases b
    · rw [src, if_pos h]
      exact (hR i h).2
    · rw [src, if_pos h]
      exact (hR i h).1
  · have hd : w.getD i false = false := List.getD_eq_default _ _ (by omega)
    cases b
    · rw [src, if_neg h, hd] <;> rfl
    · rw [src, if_neg h, hd] <;> rfl

theorem val_src_append (n j : ℕ) (b : Bool) (i : ℕ) (w' t : List Bool)
    (hw' : w'.length = 2 * n + 2 * j) :
    val (w' ++ t) (src n j b i) = val w' (src n j b i) := by
  by_cases h : i < n + j
  · rw [src, if_pos h]
    cases b
    · show (w' ++ t).getD (neg n i) false = w'.getD (neg n i) false
      apply List.getD_append
      rw [hw']
      unfold neg
      split_ifs <;> omega
    · show (w' ++ t).getD (pos n i) false = w'.getD (pos n i) false
      apply List.getD_append
      rw [hw']
      unfold pos
      split_ifs <;> omega
  · rw [src, if_neg h]
    rfl

theorem notAny (f : ℕ → Bool) : ∀ l : List ℕ, (l.map fun i => !f i).any id = !((l.map f).all id)
  | [] => rfl
  | a :: t => by
    show (!f a || (t.map fun i => !f i).any id) = !(f a && (t.map f).all id)
    rw [notAny f t]
    cases f a <;> rfl

theorem notAll (f : ℕ → Bool) : ∀ l : List ℕ, (l.map fun i => !f i).all id = !((l.map f).any id)
  | [] => rfl
  | a :: t => by
    show (!f a && (t.map fun i => !f i).all id) = !(f a || (t.map f).any id)
    rw [notAll f t]
    cases f a <;> rfl

theorem pq (n j : ℕ) (g : Gate) (w w' : List Bool) (hw : w.length = n + j)
    (hw' : w'.length = 2 * n + 2 * j) (hR : R n j w w')
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (t : List Bool) :
    (posGate n j g).op.eval ((posGate n j g).inputs.map fun i => w'.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) ∧
    (negGate n j g).op.eval ((negGate n j g).inputs.map fun i => (w' ++ t).getD i false) =
      !g.op.eval (g.inputs.map fun i => w.getD i false) := by
  have mT : ∀ l : List ℕ, (l.map (src n j true)).map (val w') = l.map (fun i => w.getD i false) := by
    intro l
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    rw [Function.comp_apply, val_src n j true i w w' hw hR]
    rfl
  have mF : ∀ l : List ℕ, (l.map (src n j false)).map (val w') = l.map (fun i => !w.getD i false) := by
    intro l
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    rw [Function.comp_apply, val_src n j false i w w' hw hR]
    rfl
  have mA : ∀ (b : Bool) (l : List ℕ),
      (l.map (src n j b)).map (val (w' ++ t)) = (l.map (src n j b)).map (val w') := by
    intro b l
    apply List.map_congr_left
    intro s hs
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hs
    exact val_src_append n j b i w' t hw'
  rcases hop with h | h | h
  · rw [posGate_and n j g h, negGate_and n j g h, evalAnd, evalOr, mA, mT, mF, h]
    exact ⟨rfl, notAny _ _⟩
  · rw [posGate_or n j g h, negGate_or n j g h, evalOr, evalAnd, mA, mT, mF, h]
    exact ⟨rfl, notAll _ _⟩
  · rw [posGate_not n j g h, negGate_not n j g h, evalAnd, evalOr, mA, mT, mF, h]
    cases g.inputs with
    | nil => exact ⟨rfl, rfl⟩
    | cons a t =>
      show (!w.getD a false && true) = !w.getD a false ∧ (w.getD a false || false) = !!w.getD a false
      cases w.getD a false <;> exact ⟨rfl, rfl⟩

theorem getD_app2 (a : List Bool) (x y : Bool) (k : ℕ) (hk : k < a.length) :
    ((a ++ [x]) ++ [y]).getD k false = a.getD k false := by
  rw [List.getD_append (a ++ [x]) [y] false k (by simp; omega), List.getD_append a [x] false k hk]

theorem getD_at0 (a : List Bool) (x y : Bool) : ((a ++ [x]) ++ [y]).getD a.length false = x := by
  rw [List.getD_append (a ++ [x]) [y] false a.length (by simp),
    List.getD_append_right a [x] false a.length (le_refl _)]
  simp

theorem getD_at1 (a : List Bool) (x y : Bool) :
    ((a ++ [x]) ++ [y]).getD (a.length + 1) false = y := by
  rw [List.getD_append_right (a ++ [x]) [y] false (a.length + 1) (by simp)]
  simp

theorem getD_last (a : List Bool) (x : Bool) : (a ++ [x]).getD a.length false = x := by
  rw [List.getD_append_right a [x] false a.length (le_refl _)]
  simp

theorem stepR (n j : ℕ) (g : Gate) (w w' : List Bool) (hw : w.length = n + j)
    (hw' : w'.length = 2 * n + 2 * j) (hR : R n j w w')
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    R n (j + 1) (stp w g) (stp (stp w' (posGate n j g)) (negGate n j g)) := by
  intro i hi
  have hpq := pq n j g w w' hw hw' hR hop
    [(posGate n j g).op.eval ((posGate n j g).inputs.map fun i => w'.getD i false)]
  unfold stp
  rcases Nat.lt_or_ge i (n + j) with hi' | hi'
  · have h1 : pos n i < w'.length := by rw [hw']; unfold pos; split_ifs <;> omega
    have h2 : neg n i < w'.length := by rw [hw']; unfold neg; split_ifs <;> omega
    have h3 : i < w.length := by omega
    rw [getD_app2 _ _ _ _ h1, getD_app2 _ _ _ _ h2, List.getD_append w _ false i h3]
    exact hR i hi'
  · have hi2 : i = n + j := by omega
    subst hi2
    have h1 : pos n (n + j) = w'.length := by rw [hw']; unfold pos; split_ifs <;> omega
    have h2 : neg n (n + j) = w'.length + 1 := by rw [hw']; unfold neg; split_ifs <;> omega
    rw [h1, h2, getD_at0, getD_at1, ← hw, getD_last]
    exact hpq

theorem fold (n : ℕ) : ∀ (gs : List Gate) (j : ℕ) (w w' : List Bool),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    w.length = n + j → w'.length = 2 * n + 2 * j → R n j w w' →
    (gs.foldl stp w).length = n + (j + gs.length) ∧
    ((dr n j gs).foldl stp w').length = 2 * n + 2 * (j + gs.length) ∧
    R n (j + gs.length) (gs.foldl stp w) ((dr n j gs).foldl stp w')
  | [], j, w, w', _, hw, hw', hR => by
    simp only [dr, List.foldl_nil, List.length_nil, Nat.add_zero]
    exact ⟨hw, hw', hR⟩
  | g :: gs, j, w, w', hop, hw, hw', hR => by
    have h := fold n gs (j + 1) (stp w g) (stp (stp w' (posGate n j g)) (negGate n j g))
      (fun g' hg' => hop g' (List.mem_cons.2 (Or.inr hg')))
      (by simp only [stp, List.length_append, List.length_singleton]; omega)
      (by simp only [stp, List.length_append, List.length_singleton]; omega)
      (stepR n j g w w' hw hw' hR (hop g (List.mem_cons.2 (Or.inl rfl))))
    simp only [dr, List.foldl_cons, List.length_cons]
    have e : j + 1 + gs.length = j + (gs.length + 1) := by omega
    rw [e] at h
    exact h

theorem dr_length (n : ℕ) : ∀ (gs : List Gate) (j : ℕ), (dr n j gs).length = 2 * gs.length
  | [], _ => rfl
  | g :: gs, j => by
    simp only [dr, List.length_cons, dr_length n gs (j + 1)]
    omega

theorem dr_mono (n : ℕ) : ∀ (gs : List Gate) (j : ℕ), (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∀ g ∈ dr n j gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
  | [], _, _, g, hg => by simp [dr] at hg
  | g0 :: gs, j, h, g, hg => by
    simp only [dr, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · exact gate_ok _ _ (posGate_cases n j g0) (h g0 (List.mem_cons.2 (Or.inl rfl)))
    · exact gate_ok _ _ (negGate_cases n j g0) (h g0 (List.mem_cons.2 (Or.inl rfl)))
    · exact dr_mono n gs (j + 1) (fun g' hg' => h g' (List.mem_cons.2 (Or.inr hg'))) g hg

theorem getD_ofFn {m : ℕ} (f : Fin m → Bool) (i : ℕ) (h : i < m) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem Rinit (n : ℕ) (x : Fin n → Bool) :
    R n 0 (List.ofFn x) (List.ofFn x ++ List.ofFn fun i => !x i) := by
  intro i hi
  have hin : i < n := by omega
  have hp : pos n i = i := by unfold pos; simp [hin]
  have hq : neg n i = n + i := by unfold neg; simp [hin]
  rw [hp, hq]
  have a1 : (List.ofFn x ++ List.ofFn fun i => !x i).getD i false = (List.ofFn x).getD i false :=
    List.getD_append _ _ _ _ (by simp; omega)
  have a2 : (List.ofFn x ++ List.ofFn fun i => !x i).getD (n + i) false =
      (List.ofFn fun i => !x i).getD (n + i - (List.ofFn x).length) false :=
    List.getD_append_right _ _ _ _ (by simp)
  rw [a1, a2, List.length_ofFn, Nat.add_sub_cancel_left, getD_ofFn _ _ hin, getD_ofFn _ _ hin]
  exact ⟨rfl, rfl⟩

theorem eval_eq (n : ℕ) (C : Circuit)
    (hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (x : Fin n → Bool) :
    (⟨dr n 0 C.gates, pos n C.output⟩ : Circuit).eval (List.ofFn x ++ List.ofFn fun i => !x i) =
      C.eval (List.ofFn x) := by
  obtain ⟨hl, hl', hR⟩ := fold n C.gates 0 (List.ofFn x) (List.ofFn x ++ List.ofFn fun i => !x i)
    hop (by simp) (by simp <;> omega) (Rinit n x)
  show ((dr n 0 C.gates).foldl stp (List.ofFn x ++ List.ofFn fun i => !x i)).getD (pos n C.output) false =
    (C.gates.foldl stp (List.ofFn x)).getD C.output false
  rcases Nat.lt_or_ge C.output (n + (0 + C.gates.length)) with h | h
  · exact (hR _ h).1
  · have e1 : ((dr n 0 C.gates).foldl stp (List.ofFn x ++ List.ofFn fun i => !x i)).getD
        (pos n C.output) false = false :=
      List.getD_eq_default _ _ (by rw [hl']; unfold pos; split_ifs <;> omega)
    have e2 : (C.gates.foldl stp (List.ofFn x)).getD C.output false = false :=
      List.getD_eq_default _ _ (by rw [hl]; omega)
    rw [e1, e2]

end PEqualNP.Outside.L_meta_8991

theorem PEqualNP.Outside.L_meta_8991 : ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.HasCircuitSize n f s → PEqualNP.Represents.HasLitSize n f (2 * s) := by
  intro n s f hf
  obtain ⟨C, hF, hs, hC⟩ := hf
  unfold PEqualNP.MetaComplexity.FanInTwo at hF
  have hop : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
    intro g hg
    have := (hF g hg).1
    simpa using this
  refine ⟨⟨PEqualNP.Outside.L_meta_8991.dr n 0 C.gates, PEqualNP.Outside.L_meta_8991.pos n C.output⟩,
    ?_, ?_, ?_⟩
  · unfold PEqualNP.MetaComplexity.Monotone2
    intro g hg
    exact PEqualNP.Outside.L_meta_8991.dr_mono n C.gates 0 (fun g hg => (hF g hg).2) g hg
  · show (PEqualNP.Outside.L_meta_8991.dr n 0 C.gates).length ≤ 2 * s
    rw [PEqualNP.Outside.L_meta_8991.dr_length]
    have : C.gates.length ≤ s := hs
    omega
  · intro x
    rw [← hC x]
    exact PEqualNP.Outside.L_meta_8991.eval_eq n C hop x
