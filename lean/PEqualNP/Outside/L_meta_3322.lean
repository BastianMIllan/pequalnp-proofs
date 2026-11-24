import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3322

open PEqualNP.CircuitLowerBounds

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

def wm (σ : Equiv.Perm (Fin 14)) (v : ℕ) : ℕ := wmap 14 14 σ v

lemma wm_lt_of (σ : Equiv.Perm (Fin 14)) (v : ℕ) (hv : v < 14) : wm σ v = (σ ⟨v, hv⟩ : ℕ) := by
  unfold wm wmap; rw [dif_pos hv]

lemma wm_14 (σ : Equiv.Perm (Fin 14)) : wm σ 14 = 14 := by
  unfold wm wmap; simp

lemma wm_lt (σ : Equiv.Perm (Fin 14)) (v : ℕ) (hv : v < 15) : wm σ v < 15 := by
  by_cases h : v < 14
  · rw [wm_lt_of σ v h]; have := (σ ⟨v, h⟩).2; omega
  · have : v = 14 := by omega
    subst this; rw [wm_14]; omega

lemma wm_mul (σ τ : Equiv.Perm (Fin 14)) (v : ℕ) (hv : v < 15) :
    wm σ (wm τ v) = wm (σ * τ) v := by
  by_cases h : v < 14
  · rw [wm_lt_of τ v h, wm_lt_of σ _ (τ ⟨v, h⟩).2, wm_lt_of _ v h]
    simp [Equiv.Perm.mul_apply]
  · have : v = 14 := by omega
    subst this; rw [wm_14, wm_14, wm_14]

lemma wm_inj (σ : Equiv.Perm (Fin 14)) (u v : ℕ) (hu : u < 15) (hv : v < 15)
    (h : wm σ u = wm σ v) : u = v := by
  by_cases h1 : u < 14 <;> by_cases h2 : v < 14
  · rw [wm_lt_of σ u h1, wm_lt_of σ v h2] at h
    have := σ.injective (Fin.ext h)
    simpa using this
  · have : v = 14 := by omega
    subst this; rw [wm_lt_of σ u h1, wm_14] at h; have := (σ ⟨u, h1⟩).2; omega
  · have : u = 14 := by omega
    subst this; rw [wm_lt_of σ v h2, wm_14] at h; have := (σ ⟨v, h2⟩).2; omega
  · omega

lemma x9_eq (σ : Equiv.Perm (Fin 14)) (x : Fin 15) :
    (if x < (14 : Fin 15) then ((σ (Fin.ofNat 14 (x : ℕ)) : Fin 14) : ℕ) else 14) = wm σ x.val := by
  by_cases h : x.val < 14
  · have hx : x < (14 : Fin 15) := by rw [Fin.lt_def]; simpa using h
    rw [if_pos hx, wm_lt_of σ _ h]
    congr 2
    ext
    simp [Nat.mod_eq_of_lt h]
  · have hx : ¬ x < (14 : Fin 15) := by rw [Fin.lt_def]; simpa using h
    rw [if_neg hx]
    have : x.val = 14 := by omega
    rw [this, wm_14]

lemma evswap (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (p q : Bool) :
    op.eval [p, q] = op.eval [q, p] := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]

lemma getD_ofFn (y : Fin 14 → Bool) (i : Fin 14) : (List.ofFn y).getD i.val false = y i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

end PEqualNP.Outside.L_meta_3322

open PEqualNP.Outside.L_meta_3322 in
theorem PEqualNP.Outside.L_meta_3322 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if x10 < (14 : Fin (15 : ℕ)) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  classical
  intro f C hAO hnd hs1 hs2 hf
  dsimp only
  obtain ⟨gs, out⟩ := C
  obtain ⟨hAnd, hRB, hLen⟩ := hAO
  rcases gs with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hs1
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hs1
  have hl0 := hLen g0 (by simp)
  have hl1 := hLen g1 (by simp)
  have ho0 := hAnd g0 (by simp)
  have ho1 := hAnd g1 (by simp)
  have hn0 := hnd g0 (by simp)
  have hn1 := hnd g1 (by simp)
  have hr0 := hRB 0 (by simp)
  have hr1 := hRB 1 (by simp)
  obtain ⟨op0, ins0⟩ := g0
  obtain ⟨op1, ins1⟩ := g1
  dsimp only at hl0 hl1
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hl0
  obtain ⟨c, d, rfl⟩ := List.length_eq_two.mp hl1
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt] at hr0 hr1
  simp at hn0 hn1 ho0 ho1
  obtain ⟨ha, hb⟩ := hr0
  obtain ⟨hc, hd⟩ := hr1
  set A : Fin 14 := ⟨a, ha⟩ with hA
  set B : Fin 14 := ⟨b, hb⟩ with hB
  let S : Finset (Equiv.Perm (Fin 14)) :=
    Finset.univ.filter (fun σ => ∀ y : Fin 14 → Bool, f (y ∘ σ) = f y)
  let keyf : Equiv.Perm (Fin 14) → ℕ := fun σ =>
    ((15 : ℕ) * min ((σ A : Fin 14) : ℕ) (σ B) + max ((σ A : Fin 14) : ℕ) (σ B)) * 225 +
      ((15 : ℕ) * min (wm σ c) (wm σ d) + max (wm σ c) (wm σ d))
  have h1S : (1 : Equiv.Perm (Fin 14)) ∈ S := by simp [S]
  obtain ⟨τ, hτS, hτmin⟩ := S.exists_min_image keyf ⟨1, h1S⟩
  have hτ : ∀ y : Fin 14 → Bool, f (y ∘ τ) = f y := by simpa [S] using hτS
  have hAB : τ A ≠ τ B := by
    intro h
    have := τ.injective h
    simp [A, B] at this
    exact hn0 this
  obtain ⟨x10, x11, hlt1, h1⟩ : ∃ x10 x11 : Fin 14, x10 < x11 ∧
      ((x10 = τ A ∧ x11 = τ B) ∨ (x10 = τ B ∧ x11 = τ A)) := by
    rcases lt_or_gt_of_ne hAB with h | h
    · exact ⟨_, _, h, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, _, h, Or.inr ⟨rfl, rfl⟩⟩
  have hCD : wm τ c ≠ wm τ d := by
    intro h
    exact hn1 (wm_inj τ c d hc hd h)
  obtain ⟨x12, x13, hlt2, h2⟩ : ∃ x12 x13 : Fin 15, x12 < x13 ∧
      ((x12.val = wm τ c ∧ x13.val = wm τ d) ∨ (x12.val = wm τ d ∧ x13.val = wm τ c)) := by
    rcases lt_or_gt_of_ne hCD with h | h
    · exact ⟨⟨_, wm_lt τ c hc⟩, ⟨_, wm_lt τ d hd⟩, h, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨⟨_, wm_lt τ d hd⟩, ⟨_, wm_lt τ c hc⟩, h, Or.inr ⟨rfl, rfl⟩⟩
  refine ⟨x10, x11, x12, x13, op0, op1,
    ⟨rest.map (relGate 14 14 τ), wmap 14 14 τ out⟩, hlt1, hlt2, ho0, ho1, ?_, ?_, ?_, ?_⟩
  · -- symmetry breaking
    intro σ hσ
    have hστ : σ * τ ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      intro y
      rw [Equiv.Perm.coe_mul]
      have e : y ∘ (⇑σ ∘ ⇑τ) = (y ∘ ⇑σ) ∘ ⇑τ := rfl
      rw [e, hτ, hσ]
    have hk := hτmin _ hστ
    simp only [keyf, Equiv.Perm.mul_apply] at hk
    rw [← wm_mul σ τ c hc, ← wm_mul σ τ d hd] at hk
    rw [x9_eq σ x12, x9_eq σ x13]
    rcases h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases h2 with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;>
      rw [e1, e2, e3, e4] <;> omega
  · -- monotone
    intro g hg
    rw [List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    have := hAnd g' (by simp [hg'])
    have hl := hLen g' (by simp [hg'])
    refine ⟨?_, ?_⟩
    · simp only [relGate]; rcases this with h | h <;> simp [h]
    · simp [relGate, hl]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hs2 ⊢
    omega
  · intro y
    have hR0 := rel_init 14 14 τ y
    have hR1 := rel_step 14 14 τ _ _ ⟨op0, [a, b]⟩ hR0
    have hR2 := rel_step 14 14 τ _ _ ⟨op1, [c, d]⟩ hR1
    have hR := (rel_fold 14 14 τ rest _ _ hR2).2.2 out
    have hC := hf (y ∘ τ)
    rw [hτ] at hC
    have hwa : wmap 14 14 τ a = ((τ A : Fin 14) : ℕ) := wm_lt_of τ a ha
    have hwb : wmap 14 14 τ b = ((τ B : Fin 14) : ℕ) := wm_lt_of τ b hb
    have hstep0 : step (List.ofFn y) (relGate 14 14 τ ⟨op0, [a, b]⟩)
        = List.ofFn y ++ [op0.eval [y x10, y x11]] := by
      simp only [step, relGate, List.map_cons, List.map_nil, hwa, hwb, getD_ofFn]
      rcases h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]
      · rw [e1, e2, evswap op0 ho0]
    have hstep1 : step (List.ofFn y ++ [op0.eval [y x10, y x11]]) (relGate 14 14 τ ⟨op1, [c, d]⟩)
        = (List.ofFn y ++ [op0.eval [y x10, y x11]]) ++
          [op1.eval [(List.ofFn y ++ [op0.eval [y x10, y x11]]).getD x12 false,
            (List.ofFn y ++ [op0.eval [y x10, y x11]]).getD x13 false]] := by
      simp only [step, relGate, List.map_cons, List.map_nil]
      have ec : wmap 14 14 τ c = wm τ c := rfl
      have ed : wmap 14 14 τ d = wm τ d := rfl
      rw [ec, ed]
      rcases h2 with ⟨e3, e4⟩ | ⟨e3, e4⟩
      · rw [e3, e4]
      · rw [e3, e4, evswap op1 ho1]
    rw [hstep0, hstep1] at hR
    have hout : PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨rest.map (relGate 14 14 τ), wmap 14 14 τ out⟩
        ((List.ofFn y ++ [op0.eval [y x10, y x11]]) ++
          [op1.eval [(List.ofFn y ++ [op0.eval [y x10, y x11]]).getD x12 false,
            (List.ofFn y ++ [op0.eval [y x10, y x11]]).getD x13 false]])
        = ((rest.map (relGate 14 14 τ)).foldl step
          ((List.ofFn y ++ [op0.eval [y x10, y x11]]) ++
          [op1.eval [(List.ofFn y ++ [op0.eval [y x10, y x11]]).getD x12 false,
            (List.ofFn y ++ [op0.eval [y x10, y x11]]).getD x13 false]])).getD
          (wmap 14 14 τ out) false := rfl
    rw [hout, hR]
    exact hC
