import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6814

open PEqualNP.CircuitLowerBounds

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepF x := rfl

theorem pre (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl stepF w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (stepF w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [stepF]

theorem getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl stepF x).getD i false = x.getD i false := by
  obtain ⟨t, ht, _⟩ := pre gs x
  rw [ht]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_ge (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (gs.foldl stepF x).getD i false = false := by
  obtain ⟨t, ht, hl⟩ := pre gs x
  rw [ht]
  apply List.getD_eq_default
  simp
  omega

theorem gate_val (gs : List Gate) : ∀ (x : List Bool) (j : ℕ), j < gs.length →
    (gs.foldl stepF x).getD (x.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval
        ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
          if i < x.length + j then (gs.foldl stepF x).getD i false else false) := by
  induction gs with
  | nil => intro x j hj; simp at hj
  | cons g gs ih =>
    intro x j hj
    rcases j with _ | j
    · simp only [List.getD_cons_zero, List.foldl_cons]
      obtain ⟨t, ht, _⟩ := pre gs (stepF x g)
      rw [ht]
      have e1 : (stepF x g ++ t).getD (x.length + 0) false =
          g.op.eval (g.inputs.map fun i => x.getD i false) := by
        simp [stepF, List.getD_eq_getElem?_getD, List.getElem?_append_left, List.getElem?_append_right]
      rw [e1]
      congr 1
      apply List.map_congr_left
      intro i hi
      by_cases h : i < x.length + 0
      · rw [if_pos h]
        have h' : i < x.length := by omega
        simp [stepF, List.getD_eq_getElem?_getD, List.getElem?_append_left h']
      · rw [if_neg h]
        apply List.getD_eq_default
        omega
    · simp only [List.getD_cons_succ, List.foldl_cons, List.length_cons] at hj ⊢
      have hl : (stepF x g).length = x.length + 1 := by simp [stepF]
      have := ih (stepF x g) j (by omega)
      rw [hl] at this
      rw [show x.length + (j + 1) = x.length + 1 + j by omega]
      exact this

theorem supp (gs : List Gate) (n : ℕ) (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ j, ∀ W : Finset ℕ, (∀ w ∈ W, w < n + j ∨ n + gs.length ≤ w) →
      ∃ S : Finset ℕ, S.card ≤ W.card + j ∧ (∀ s ∈ S, s < n) ∧
        ∀ x y : List Bool, x.length = n → y.length = n → (∀ i ∈ S, x.getD i false = y.getD i false) →
          ∀ w ∈ W, (gs.foldl stepF x).getD w false = (gs.foldl stepF y).getD w false := by
  intro j
  induction j with
  | zero =>
    intro W hW
    refine ⟨W.filter (fun w => w < n), by simpa using Finset.card_filter_le W _, ?_, ?_⟩
    · intro s hs
      exact (Finset.mem_filter.mp hs).2
    · intro x y hx hy hS w hw
      rcases hW w hw with h1 | h1
      · rw [getD_lt gs x w (by omega), getD_lt gs y w (by omega)]
        exact hS w (Finset.mem_filter.mpr ⟨hw, by omega⟩)
      · rw [getD_ge gs x w (by omega), getD_ge gs y w (by omega)]
  | succ j ih =>
    intro W hW
    by_cases hc : j < gs.length ∧ n + j ∈ W
    · obtain ⟨hj, hjW⟩ := hc
      have hg : gs.getD j ⟨GateOp.or, []⟩ ∈ gs := by
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      have hlen := hfan _ hg
      obtain ⟨S, hSc, hSn, hSa⟩ := ih (W.erase (n + j) ∪
          (gs.getD j ⟨GateOp.or, []⟩).inputs.toFinset.filter (fun i => i < n + j)) (by
        intro w hw
        rcases Finset.mem_union.mp hw with h1 | h1
        · obtain ⟨h2, h3⟩ := Finset.mem_erase.mp h1
          rcases hW w h3 with h4 | h4
          · left; omega
          · right; exact h4
        · left
          exact (Finset.mem_filter.mp h1).2)
      refine ⟨S, ?_, hSn, ?_⟩
      · have c1 := Finset.card_union_le (W.erase (n + j))
          ((gs.getD j ⟨GateOp.or, []⟩).inputs.toFinset.filter (fun i => i < n + j))
        have c2 := Finset.card_erase_of_mem hjW
        have c3 : ((gs.getD j ⟨GateOp.or, []⟩).inputs.toFinset.filter (fun i => i < n + j)).card ≤
            (gs.getD j ⟨GateOp.or, []⟩).inputs.length :=
          le_trans (Finset.card_filter_le _ _) (List.toFinset_card_le _)
        have c4 : 0 < W.card := Finset.card_pos.mpr ⟨_, hjW⟩
        omega
      · intro x y hx hy hS w hw
        by_cases hwj : w = n + j
        · subst hwj
          have gx := gate_val gs x j hj
          have gy := gate_val gs y j hj
          rw [hx] at gx
          rw [hy] at gy
          rw [gx, gy]
          congr 1
          apply List.map_congr_left
          intro i hi
          by_cases h : i < n + j
          · rw [if_pos h, if_pos h]
            exact hSa x y hx hy hS i (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hi, h⟩))
          · rw [if_neg h, if_neg h]
        · exact hSa x y hx hy hS w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwj, hw⟩))
    · obtain ⟨S, hSc, hSn, hSa⟩ := ih W (by
        intro w hw
        rcases hW w hw with h1 | h1
        · by_cases h2 : w = n + j
          · subst h2
            right
            have : ¬ j < gs.length := fun h3 => hc ⟨h3, hw⟩
            omega
          · left; omega
        · right; exact h1)
      exact ⟨S, by omega, hSn, hSa⟩

theorem main (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hp : ∀ i : Fin n, ∃ q : Fin n → Bool, f (Function.update q i true) ≠ f (Function.update q i false))
    (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (h : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) : n ≤ C.size + 1 := by
  obtain ⟨S, hSc, hSn, hSa⟩ := supp C.gates n (fun g hg => (hM g hg).2)
    C.gates.length {C.output} (by
      intro w hw
      rw [Finset.mem_singleton] at hw
      subst hw
      omega)
  by_contra hlt
  have hex : ∃ i, i < n ∧ i ∉ S := by
    by_contra hno
    push Not at hno
    have hsub : Finset.range n ⊆ S := by
      intro i hi
      exact hno i (Finset.mem_range.mp hi)
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    simp [Circuit.size] at hSc hlt
    omega
  obtain ⟨i, hin, hiS⟩ := hex
  obtain ⟨q, hq⟩ := hp ⟨i, hin⟩
  apply hq
  rw [← h, ← h]
  simp only [Circuit.eval, wires_eq]
  apply hSa _ _ (by simp) (by simp) _ C.output (Finset.mem_singleton_self _)
  intro k hk
  have hkn := hSn k hk
  have hki : k ≠ i := fun e => hiS (e ▸ hk)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  have hne : (⟨k, hkn⟩ : Fin n) ≠ ⟨i, hin⟩ := fun e => hki (Fin.mk.inj e)
  simp [hkn, Function.update_of_ne hne]

theorem getD_snoc (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false = if i < w.length then w.getD i false else if i = w.length then v else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem mono_fold (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w w' : List Bool), w.length = w'.length →
      (∀ i, w.getD i false = true → w'.getD i false = true) →
      ∀ i, (gs.foldl stepF w).getD i false = true → (gs.foldl stepF w').getD i false = true := by
  induction gs with
  | nil =>
    intro w w' _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w w' hlen hle
    simp only [List.foldl_cons]
    apply ih (fun g1 hg1 => hg g1 (List.mem_cons_of_mem _ hg1)) (stepF w g) (stepF w' g) (by simp [stepF, hlen])
    intro i hi
    simp only [stepF, getD_snoc] at hi ⊢
    rw [← hlen]
    split_ifs at hi ⊢ with h1 h2
    · exact hle i hi
    · have hop := hg g (by simp)
      rcases hop with hop | hop
      · rw [hop] at hi ⊢
        simp only [GateOp.eval, List.all_eq_true, List.mem_map] at hi ⊢
        rintro b ⟨a, ha, rfl⟩
        exact hle a (hi _ ⟨a, ha, rfl⟩)
      · rw [hop] at hi ⊢
        simp only [GateOp.eval, List.any_eq_true, List.mem_map] at hi ⊢
        obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := hi
        exact ⟨_, ⟨a, ha, rfl⟩, hle a hb⟩

theorem app_le (n m : ℕ) (X X' : Finset (Fin n)) (Y Y' : Finset (Fin m)) (hX : X ⊆ X') (hY : Y ⊆ Y')
    (k : Fin (n + m)) :
    Fin.append (fun p : Fin n => decide (p ∈ X)) (fun l : Fin m => decide (l ∈ Y)) k = true →
      Fin.append (fun p : Fin n => decide (p ∈ X')) (fun l : Fin m => decide (l ∈ Y')) k = true := by
  refine Fin.addCases (fun p => ?_) (fun l => ?_) k
  · simp only [Fin.append_left, decide_eq_true_eq]
    exact fun h => hX h
  · simp only [Fin.append_right, decide_eq_true_eq]
    exact fun h => hY h

theorem updL (n m : ℕ) (a : Fin n → Bool) (b : Fin m → Bool) (p : Fin n) (v : Bool) :
    Function.update (Fin.append a b) (Fin.castAdd m p) v = Fin.append (Function.update a p v) b := by
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · by_cases e : k = p
    · subst e
      simp
    · have : Fin.castAdd m k ≠ Fin.castAdd m p := fun h => e (Fin.castAdd_injective _ _ h)
      simp [Function.update_of_ne this, Function.update_of_ne e]
  · have : Fin.natAdd n k ≠ Fin.castAdd m p := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [Function.update_of_ne this]

theorem updR (n m : ℕ) (a : Fin n → Bool) (b : Fin m → Bool) (p : Fin m) (v : Bool) :
    Function.update (Fin.append a b) (Fin.natAdd n p) v = Fin.append a (Function.update b p v) := by
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · have : Fin.castAdd m k ≠ Fin.natAdd n p := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [Function.update_of_ne this]
  · by_cases e : k = p
    · subst e
      simp
    · have : Fin.natAdd n k ≠ Fin.natAdd n p := fun h => e (Fin.natAdd_injective _ _ h)
      simp [Function.update_of_ne this, Function.update_of_ne e]

theorem inc (n m : ℕ) (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    PEqualNP.GenericRejection.incidenceInput X Y =
      List.ofFn (Fin.append (fun p : Fin n => decide (p ∈ X)) (fun l : Fin m => decide (l ∈ Y))) := by
  rw [List.ofFn_fin_append]
  rfl

theorem updS (n : ℕ) (p : Fin n) (v : Bool) :
    Function.update (fun k : Fin n => decide (k ∈ (∅ : Finset (Fin n)))) p v =
      fun k : Fin n => decide (k ∈ (if v then ({p} : Finset (Fin n)) else ∅)) := by
  funext k
  by_cases e : k = p
  · subst e
    cases v <;> simp
  · cases v <;> simp [Function.update_of_ne e, e]

theorem updZ (n : ℕ) (Z : Finset (Fin n)) (p : Fin n) (hp : p ∉ Z) (v : Bool) :
    Function.update (fun k : Fin n => decide (k ∈ Z)) p v =
      fun k : Fin n => decide (k ∈ (if v then insert p Z else Z)) := by
  funext k
  by_cases e : k = p
  · subst e
    cases v <;> simp [hp]
  · cases v <;> simp [Function.update_of_ne e, e]

theorem eval_mono (n m : ℕ) (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (X X' : Finset (Fin n)) (Y Y' : Finset (Fin m)) (hX : X ⊆ X') (hY : Y ⊆ Y') :
    C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = true →
      C.eval (PEqualNP.GenericRejection.incidenceInput X' Y') = true := by
  unfold Circuit.eval
  rw [wires_eq, wires_eq]
  apply mono_fold C.gates (fun g hg => by simpa using (hM g hg).1) _ _
    (by simp [PEqualNP.GenericRejection.incidenceInput])
  intro i hi
  rw [inc] at hi ⊢
  by_cases h : i < n + m
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h] at hi ⊢
    exact app_le n m X X' Y Y' hX hY _ hi
  · simp [List.getD_eq_getElem?_getD, h] at hi

end PEqualNP.Outside.L_meta_6814

theorem PEqualNP.Outside.L_meta_6814 : ∀ (x1 : ℕ) (x2 : Fin x1 → Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin x1), ∃ (x5 : Fin x1), x4 ∈ x2 x5) → (∀ (x5 : Fin x1), (x2 x5).Nonempty) → PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.GenericRejection.RightOnIncidentPairs x2 x3 → (∀ (x8 : Finset (Fin x1)), x8.card ≤ (1 : ℕ) → x3.eval (PEqualNP.GenericRejection.incidenceInput (PEqualNP.GenericRejection.zeroSet x2 x8) x8) = Bool.false) → x1 + x1 ≤ x3.size + (1 : ℕ) := by
  intro x1 x2 x3 hcov hne hM hR hF
  refine PEqualNP.Outside.L_meta_6814.main (x1 + x1) (fun x => x3.eval (List.ofFn x)) ?_ x3 hM
    (fun _ => rfl)
  intro i
  refine Fin.addCases (fun p => ?_) (fun l => ?_) i
  · obtain ⟨l, hl⟩ := hcov p
    have hpZ : p ∉ PEqualNP.GenericRejection.zeroSet x2 {l} := by
      simp [PEqualNP.GenericRejection.zeroSet, hl]
    refine ⟨Fin.append (fun k : Fin x1 => decide (k ∈ PEqualNP.GenericRejection.zeroSet x2 {l}))
      (fun k : Fin x1 => decide (k ∈ ({l} : Finset (Fin x1)))), ?_⟩
    have h1 : x3.eval (PEqualNP.GenericRejection.incidenceInput
        (insert p (PEqualNP.GenericRejection.zeroSet x2 {l})) {l}) = true :=
      PEqualNP.Outside.L_meta_6814.eval_mono x1 x1 x3 hM {p} _ {l} {l}
        (by simp) (Finset.Subset.refl _) (hR l p hl)
    have h2 := hF {l} (by simp)
    rw [PEqualNP.Outside.L_meta_6814.inc] at h1 h2
    simp only [PEqualNP.Outside.L_meta_6814.updL,
      PEqualNP.Outside.L_meta_6814.updZ x1 (PEqualNP.GenericRejection.zeroSet x2 {l}) p hpZ]
    simp only [if_true, Bool.false_eq_true, if_false]
    rw [h1, h2]
    simp
  · obtain ⟨p, hp⟩ := hne l
    refine ⟨Fin.append (fun k : Fin x1 => decide (k ∈ PEqualNP.GenericRejection.zeroSet x2 ∅))
      (fun k : Fin x1 => decide (k ∈ (∅ : Finset (Fin x1)))), ?_⟩
    have h1 : x3.eval (PEqualNP.GenericRejection.incidenceInput
        (PEqualNP.GenericRejection.zeroSet x2 ∅) {l}) = true :=
      PEqualNP.Outside.L_meta_6814.eval_mono x1 x1 x3 hM {p} _ {l} {l}
        (by simp [PEqualNP.GenericRejection.zeroSet]) (Finset.Subset.refl _) (hR l p hp)
    have h2 := hF ∅ (by simp)
    rw [PEqualNP.Outside.L_meta_6814.inc] at h1 h2
    simp only [PEqualNP.Outside.L_meta_6814.updR, PEqualNP.Outside.L_meta_6814.updS]
    simp only [if_true, Bool.false_eq_true, if_false]
    rw [h1, h2]
    simp
