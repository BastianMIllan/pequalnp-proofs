import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3097

open PEqualNP.CircuitLowerBounds

def stepO (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def mg (σ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map σ⟩

theorem len_stepO (W : List Bool) (g : Gate) : (stepO W g).length = W.length + 1 := by
  simp [stepO]

theorem getD_stepO_lt (W : List Bool) (g : Gate) (i : ℕ) (h : i < W.length) :
    (stepO W g).getD i false = W.getD i false := by
  simp only [stepO, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_stepO_eq (W : List Bool) (g : Gate) :
    (stepO W g).getD W.length false = g.op.eval (g.inputs.map fun i => W.getD i false) := by
  simp [stepO, List.getD_eq_getElem?_getD]

theorem getD_stepO_gt (W : List Bool) (g : Gate) (i : ℕ) (h : W.length < i) :
    (stepO W g).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [len_stepO]; omega)]
  rfl

theorem pre_fold (gs : List Gate) : ∀ W : List Bool, ∀ i < W.length,
    (gs.foldl stepO W).getD i false = W.getD i false := by
  induction gs with
  | nil => intro W i _; rfl
  | cons g gs ih =>
    intro W i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by rw [len_stepO]; omega)]
    exact getD_stepO_lt W g i hi

theorem gen (σ : ℕ → ℕ) (r : Bool → Bool → Prop) (hf : r false false)
    (htr : ∀ a b c, r a b → r b c → r a c) (F : List Bool) :
    ∀ (gs : List Gate) (W V : List Bool), W.length = V.length → gs.foldl stepO W = F →
      (∀ i, r (W.getD i false) (V.getD i false)) →
      (∀ g ∈ gs, ∀ A B : ℕ → Bool, (∀ ii ∈ g.inputs, r (A ii) (B (σ ii))) →
        r (g.op.eval (g.inputs.map A)) (g.op.eval ((g.inputs.map σ).map B))) →
      (∀ k (hk : k < gs.length), ∀ ii ∈ gs[k].inputs, σ ii = ii ∨
        (ii < W.length + k ∧ σ ii < W.length + k ∧ r (F.getD ii false) (F.getD (σ ii) false))) →
      ∀ i, r ((gs.foldl stepO W).getD i false) (((gs.map (mg σ)).foldl stepO V).getD i false) := by
  intro gs
  induction gs with
  | nil =>
    intro W V _ _ hWV _ _
    simpa using hWV
  | cons g gs ih =>
    intro W V hl hF hWV hg hgood
    simp only [List.map_cons, List.foldl_cons]
    apply ih (stepO W g) (stepO V (mg σ g))
    · rw [len_stepO, len_stepO, hl]
    · simpa using hF
    · intro i
      rcases lt_trichotomy i W.length with h | h | h
      · rw [getD_stepO_lt W g i h, getD_stepO_lt V _ i (hl ▸ h)]
        exact hWV i
      · subst h
        rw [getD_stepO_eq, hl, getD_stepO_eq]
        apply hg g (by simp)
        intro ii hii
        rcases hgood 0 (by simp) ii (by simpa using hii) with he | ⟨h1, h2, h3⟩
        · rw [he]
          exact hWV ii
        · have e1 : W.getD ii false = F.getD ii false := by
            rw [← hF]
            exact (pre_fold _ W ii (by simpa using h1)).symm
          have e2 : W.getD (σ ii) false = F.getD (σ ii) false := by
            rw [← hF]
            exact (pre_fold _ W (σ ii) (by simpa using h2)).symm
          rw [e1]
          exact htr _ _ _ h3 (by rw [← e2]; exact hWV _)
      · rw [getD_stepO_gt W g i h, getD_stepO_gt V _ i (hl ▸ h)]
        exact hf
    · intro g' hg'
      exact hg g' (List.mem_cons_of_mem _ hg')
    · intro k hk ii hii
      have := hgood (k + 1) (by simp; omega) ii (by simpa using hii)
      rw [len_stepO]
      rcases this with h | ⟨a, b, c⟩
      · exact Or.inl h
      · exact Or.inr ⟨by omega, by omega, c⟩

theorem gate_eq (σ : ℕ → ℕ) (g : Gate) (A B : ℕ → Bool) (h : ∀ ii ∈ g.inputs, A ii = B (σ ii)) :
    g.op.eval (g.inputs.map A) = g.op.eval ((g.inputs.map σ).map B) := by
  rw [List.map_map]
  congr 1
  exact List.map_congr_left h

theorem gate_imp (σ : ℕ → ℕ) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (A B : ℕ → Bool) (h : ∀ ii ∈ g.inputs, A ii = true → B (σ ii) = true) :
    g.op.eval (g.inputs.map A) = true → g.op.eval ((g.inputs.map σ).map B) = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.map_map, List.all_map, List.all_eq_true, Function.comp, id]
    intro hA ii hii
    exact h ii hii (hA ii hii)
  · rw [hop]
    simp only [GateOp.eval, List.map_map, List.any_map, List.any_eq_true, Function.comp, id]
    rintro ⟨ii, hii, ha⟩
    exact ⟨ii, hii, h ii hii ha⟩

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hk]

end PEqualNP.Outside.L_meta_3097

theorem PEqualNP.Outside.L_meta_3097 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (w w' : ℕ),
  PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
  (∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → w' < n + k) →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = true →
    (C.wires (List.ofFn x)).getD w' false = true) →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w' false = true →
    (C.wires (List.ofFn x)).getD w false = true ∨ PEqualNP.MetaComplexity.circuitFun n C x = true) →
  PEqualNP.MetaComplexity.circuitFun n
      ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun ii => if ii = w then w' else ii) } : PEqualNP.CircuitLowerBounds.Gate)),
         output := if C.output = w then w' else C.output } : PEqualNP.CircuitLowerBounds.Circuit)
    = PEqualNP.MetaComplexity.circuitFun n C ∧
  ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun ii => if ii = w then w' else ii) } : PEqualNP.CircuitLowerBounds.Gate)),
      output := if C.output = w then w' else C.output } : PEqualNP.CircuitLowerBounds.Circuit).size = C.size := by
  intro n C w w' hM hR hw' h1 h2
  refine ⟨?_, by simp [PEqualNP.CircuitLowerBounds.Circuit.size]⟩
  funext x
  change ((C.gates.map (PEqualNP.Outside.L_meta_3097.mg (fun ii => if ii = w then w' else ii))).foldl
      PEqualNP.Outside.L_meta_3097.stepO (List.ofFn x)).getD (if C.output = w then w' else C.output) false
    = (C.gates.foldl PEqualNP.Outside.L_meta_3097.stepO (List.ofFn x)).getD C.output false
  have h1x := h1 x
  have h2x := h2 x
  change (C.gates.foldl PEqualNP.Outside.L_meta_3097.stepO (List.ofFn x)).getD w false = true →
    (C.gates.foldl PEqualNP.Outside.L_meta_3097.stepO (List.ofFn x)).getD w' false = true at h1x
  change (C.gates.foldl PEqualNP.Outside.L_meta_3097.stepO (List.ofFn x)).getD w' false = true →
    (C.gates.foldl PEqualNP.Outside.L_meta_3097.stepO (List.ofFn x)).getD w false = true ∨
    (C.gates.foldl PEqualNP.Outside.L_meta_3097.stepO (List.ofFn x)).getD C.output false = true at h2x
  generalize hF : C.gates.foldl PEqualNP.Outside.L_meta_3097.stepO (List.ofFn x) = F at h1x h2x ⊢
  have hop : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have := (hM g hg).1
    simpa using this
  have good : ∀ (r : Bool → Bool → Prop), r (F.getD w false) (F.getD w' false) →
      ∀ k (hk : k < C.gates.length), ∀ ii ∈ C.gates[k].inputs,
        (fun ii => if ii = w then w' else ii) ii = ii ∨
        (ii < (List.ofFn x).length + k ∧ (fun ii => if ii = w then w' else ii) ii < (List.ofFn x).length + k ∧
          r (F.getD ii false) (F.getD ((fun ii => if ii = w then w' else ii) ii) false)) := by
    intro r hr k hk ii hii
    by_cases he : ii = w
    · subst he
      right
      have hR' := hR k hk ii (by rw [PEqualNP.Outside.L_meta_3097.gateAt_eq C k hk]; exact hii)
      have hw'' := hw' k hk (by rw [PEqualNP.Outside.L_meta_3097.gateAt_eq C k hk]; exact hii)
      simp only [if_pos rfl, List.length_ofFn]
      exact ⟨hR', hw'', hr⟩
    · left
      simp only [if_neg he]
  cases hfx : F.getD C.output false
  · have hE : F.getD w false = F.getD w' false := by
      cases ha : F.getD w false <;> cases hb : F.getD w' false
      · rfl
      · rcases h2x hb with h | h
        · rw [ha] at h
          exact absurd h (by simp)
        · rw [hfx] at h
          exact absurd h (by simp)
      · rw [ha, hb] at h1x
        exact absurd (h1x rfl) (by simp)
      · rfl
    have key := PEqualNP.Outside.L_meta_3097.gen (fun ii => if ii = w then w' else ii) (fun a b => a = b) rfl
      (fun a b c h h' => h.trans h') F C.gates (List.ofFn x) (List.ofFn x) rfl hF (fun i => rfl)
      (fun g _ A B h => PEqualNP.Outside.L_meta_3097.gate_eq _ g A B h) (good (fun a b => a = b) hE)
    rw [hF] at key
    by_cases ho : C.output = w
    · rw [if_pos ho, ← key w', ← hE, ← ho, hfx]
    · rw [if_neg ho, ← key C.output, hfx]
  · have key := PEqualNP.Outside.L_meta_3097.gen (fun ii => if ii = w then w' else ii)
      (fun a b => a = true → b = true) (fun h => h)
      (fun a b c h h' t => h' (h t)) F C.gates (List.ofFn x) (List.ofFn x) rfl hF (fun i t => t)
      (fun g hg A B h => PEqualNP.Outside.L_meta_3097.gate_imp _ g (hop g hg) A B h)
      (good (fun a b => a = true → b = true) h1x)
    rw [hF] at key
    by_cases ho : C.output = w
    · rw [if_pos ho]
      exact key w' (h1x (ho ▸ hfx))
    · rw [if_neg ho]
      exact key C.output hfx
