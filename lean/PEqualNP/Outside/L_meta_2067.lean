import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2067

open PEqualNP.CircuitLowerBounds

def sf {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun l g => l ++ [f l g]) init

theorem sf_append {α : Type} (f : List α → Gate → α) (gs gs' : List Gate) (init : List α) :
    sf f (gs ++ gs') init = sf f gs' (sf f gs init) := by
  simp [sf, List.foldl_append]

theorem sf_prefix {α : Type} (f : List α → Gate → α) (gs : List Gate) : ∀ init : List α,
    ∃ t : List α, sf f gs init = init ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [sf], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [f w g])
    refine ⟨f w g :: t, ?_, by simp [hl]⟩
    have : sf f (g :: gs) w = sf f gs (w ++ [f w g]) := rfl
    rw [this, ht]; simp

theorem sf_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) :
    (sf f gs init).length = init.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := sf_prefix f gs init
  rw [ht]; simp [hl]

theorem sf_at {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) (d : α)
    (j : ℕ) (g : Gate) (hg : gs[j]? = some g) :
    (sf f gs init).getD (init.length + j) d = f (sf f (gs.take j) init) g ∧
    ∀ i < init.length + j, (sf f (gs.take j) init).getD i d = (sf f gs init).getD i d := by
  obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.mp hg
  have hd : gs.drop j = g :: gs.drop (j+1) := by
    rw [List.drop_eq_getElem_cons hj, hgj]
  have hP : (sf f (gs.take j) init).length = init.length + j := by
    rw [sf_length, List.length_take]; omega
  have hs : sf f gs init = sf f (gs.drop (j+1))
      (sf f (gs.take j) init ++ [f (sf f (gs.take j) init) g]) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [sf_append, hd]; rfl
  obtain ⟨t, ht, _⟩ := sf_prefix f (gs.drop (j+1))
    (sf f (gs.take j) init ++ [f (sf f (gs.take j) init) g])
  rw [hs, ht]
  refine ⟨?_, ?_⟩
  · rw [List.getD_append _ _ _ _ (by simp [hP])]
    rw [← hP]; simp
  · intro i hi
    rw [List.append_assoc, List.getD_append _ _ _ _ (by omega)]

theorem wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = sf (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) C.gates x := rfl

theorem wire_gate (C : Circuit) (x : List Bool) (n : ℕ) (hx : x.length = n) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hrb : ∀ i ∈ g.inputs, i < n + j) :
    (C.wires x).getD (n + j) false
      = g.op.eval (g.inputs.map fun i => (C.wires x).getD i false) := by
  obtain ⟨h1, h2⟩ := sf_at (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates x false j g hg
  rw [wires_eq, ← hx, h1]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h2 i (by rw [hx]; exact hrb i hi)

theorem wire_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  rw [wires_eq]
  obtain ⟨t, ht, _⟩ := sf_prefix (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates x
  rw [ht, List.getD_append _ _ _ _ hi]

theorem wire_out (C : Circuit) (x : List Bool) (w : ℕ) (hw : x.length + C.gates.length ≤ w) :
    (C.wires x).getD w false = false := by
  rw [wires_eq]
  apply List.getD_eq_default
  rw [sf_length]; exact hw

def coneF (cs : List (List ℕ)) (g : Gate) : List ℕ :=
  (g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
    (fun w => (w - 26) :: cs.getD (w - 26) [])

theorem cones_eq (C : Circuit) : PEqualNP.EdgeOwnership.cones 26 C = sf coneF C.gates [] := rfl

theorem cone_step (C : Circuit) (j i : ℕ) (g : Gate) (hg : C.gates[j]? = some g)
    (hin : 26 + i ∈ g.inputs) (hij : i < j) :
    PEqualNP.EdgeOwnership.InCone 26 C i j ∧
      ∀ k, PEqualNP.EdgeOwnership.InCone 26 C k i → PEqualNP.EdgeOwnership.InCone 26 C k j := by
  obtain ⟨hj, _⟩ := List.getElem?_eq_some_iff.mp hg
  obtain ⟨h1, h2⟩ := sf_at coneF C.gates [] [] j g hg
  simp only [List.length_nil, Nat.zero_add] at h1 h2
  have hP : (sf coneF (C.gates.take j) []).length = j := by
    rw [sf_length, List.length_take]; simp; omega
  unfold PEqualNP.EdgeOwnership.InCone
  rw [cones_eq, h1]
  have hmem : 26 + i ∈ g.inputs.filter
      (fun w => decide (26 ≤ w ∧ w < 26 + (sf coneF (C.gates.take j) []).length)) := by
    rw [List.mem_filter]; refine ⟨hin, ?_⟩; rw [hP]; simp; omega
  refine ⟨?_, ?_⟩
  · unfold coneF
    rw [List.mem_flatMap]
    exact ⟨26 + i, hmem, by simp⟩
  · intro k hk
    have hk' : k ∈ (sf coneF (C.gates.take j) []).getD i [] := by rw [h2 i hij]; exact hk
    unfold coneF
    rw [List.mem_flatMap]
    refine ⟨26 + i, hmem, ?_⟩
    have : 26 + i - 26 = i := by omega
    rw [this]
    exact List.mem_cons_of_mem _ hk'

theorem ofFn_getD (f : Fin 26 → Bool) (i : ℕ) (hi : i < 26) :
    (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]

def Pure (C : Circuit) (w : ℕ) : Prop :=
  w < 26 ∨ (w - 26 < C.gates.length ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - 26)).op ≠ GateOp.and ∧
    ∀ k, PEqualNP.EdgeOwnership.InCone 26 C k (w - 26) →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op ≠ GateOp.and)

theorem gateAt_of (C : Circuit) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem?_getD, hg]; rfl

theorem gateAt_out (C : Circuit) (k : ℕ) (hk : C.gates.length ≤ k) :
    (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.or := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_default _ _ hk]

theorem mem_filter_gen {α : Type} (p : α → Prop) (inst : DecidablePred p) (s : Finset α) (a : α)
    (ha : a ∈ s) (hp : p a) : a ∈ @Finset.filter α p inst s := Finset.mem_filter.mpr ⟨ha, hp⟩

theorem ap_zero (C : Circuit) (h : PEqualNP.TopForm.andPairs 26 C = 0) (k j : ℕ)
    (hj : j < C.gates.length)
    (hja : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and)
    (hc : PEqualNP.EdgeOwnership.InCone 26 C k j) :
    (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op ≠ GateOp.and := by
  by_cases hk : k < C.gates.length
  · intro hka
    unfold PEqualNP.TopForm.andPairs at h
    rw [Finset.card_eq_zero] at h
    have h1 : (k, j) ∈ (∅ : Finset (ℕ × ℕ)) := by
      rw [← h]
      exact mem_filter_gen _ _ _ _ (by simp [hk, hj]) ⟨hka, hja, hc⟩
    simp at h1
  · rw [gateAt_out C k (by omega)]; exact fun h0 => by cases h0

def W (C : Circuit) (f : Fin 26 → Bool) (w : ℕ) : Bool := (C.wires (List.ofFn f)).getD w false

def yv (a b : Fin 13) : Fin 26 → Bool :=
  fun i => decide (i = Fin.castAdd 13 a) || decide (i = Fin.natAdd 13 b)
def zv (a : Fin 13) : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 a)
def uv (b : Fin 13) : Fin 26 → Bool := fun i => decide (i = Fin.natAdd 13 b)

theorem W_input (C : Circuit) (f : Fin 26 → Bool) (w : ℕ) (hw : w < 26) :
    W C f w = f ⟨w, hw⟩ := by
  unfold W
  rw [wire_input C _ w (by simp; omega)]
  exact ofFn_getD f w hw

theorem W_gate (C : Circuit) (f : Fin 26 → Bool) (j : ℕ) (g : Gate) (a b : ℕ)
    (hg : C.gates[j]? = some g) (hab : g.inputs = [a, b]) (ha : a < 26 + j) (hb : b < 26 + j) :
    W C f (26 + j) = g.op.eval [W C f a, W C f b] := by
  unfold W
  rw [wire_gate C (List.ofFn f) 26 (by simp) j g hg (by rw [hab]; intro i hi; simp at hi; omega),
    hab]
  rfl

theorem W_out (C : Circuit) (f : Fin 26 → Bool) (w : ℕ) (hw : 26 + C.gates.length ≤ w) :
    W C f w = false := by
  unfold W
  exact wire_out C _ w (by simp; omega)

theorem eval_and (p q : Bool) : GateOp.and.eval [p, q] = (p && q) := by
  simp [GateOp.eval]

theorem eval_or (p q : Bool) : GateOp.or.eval [p, q] = (p || q) := by
  simp [GateOp.eval]

theorem or_case : ∀ ya yb za zb ua ub xa xb : Bool,
    (ya = true → za = false → ua = false → xa = true) →
    (yb = true → zb = false → ub = false → xb = true) →
    (ya || yb) = true → (za || zb) = false → (ua || ub) = false → (xa || xb) = true := by
  decide

theorem and_case : ∀ za zb ua ub : Bool,
    ((za || ua) && (zb || ub)) = true → (za && zb) = false → (ua && ub) = false →
    (za && ub || ua && zb) = true := by
  decide

theorem or_mix : ∀ za zb ua ub : Bool,
    ((za || ua) || (zb || ub)) = ((za || zb) || (ua || ub)) := by
  decide

theorem main (x1 : Finset (Fin 13)) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin (13 : ℕ)) (x5 : ℕ → Bool)
    (hgate : ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x7 → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x9 : ℕ) (x10 : ℕ), x7.inputs = [x9, x10] ∧ x9 ≠ x10 ∧ x9 < (26 : ℕ) + x6 ∧ x10 < (26 : ℕ) + x6)
    (hcomp : ∀ (x7 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x8 - x9 ∈ x1 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true)
    (hAP : PEqualNP.TopForm.andPairs (26 : ℕ) x2 = (0 : ℕ))
    (hinc : x3 - x4 ∈ x1)
    (hx5 : ∀ (x10 : Fin (13 : ℕ)), x5 ↑x10 = Bool.false ∧ x5 ((13 : ℕ) + ↑x10) = Decidable.decide (x10 = x4))
    (hrec : have x11 : List Bool := x2.wires (List.ofFn fun (x11 : Fin (26 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (13 : ℕ) x3));               ∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 x15 : ℕ), x2.gates[x12]? = Option.some x13 → x13.inputs = [x14, x15] → (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x12) = (x11.getD x14 Bool.false && x5 x15 || x5 x14 && x11.getD x15 Bool.false)) ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x12) = (x5 x14 || x5 x15))) :
    x5 x2.output = Bool.true := by
  dsimp only at hrec
  have key : ∀ w, (Pure x2 w → x5 w = W x2 (uv x4) w ∧
      W x2 (yv x3 x4) w = (W x2 (zv x3) w || W x2 (uv x4) w)) ∧
      (W x2 (yv x3 x4) w = true → W x2 (zv x3) w = false → W x2 (uv x4) w = false →
        x5 w = true) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
    by_cases hw : w < 26
    · have hY := W_input x2 (yv x3 x4) w hw
      have hZ := W_input x2 (zv x3) w hw
      have hU := W_input x2 (uv x4) w hw
      have hYZU : W x2 (yv x3 x4) w = (W x2 (zv x3) w || W x2 (uv x4) w) := by
        rw [hY, hZ, hU]; rfl
      have hx5w : x5 w = W x2 (uv x4) w := by
        rw [hU]
        by_cases hw13 : w < 13
        · have h0 := (hx5 ⟨w, hw13⟩).1
          simp only at h0
          rw [h0]
          simp [uv, Fin.ext_iff] <;> omega
        · have h0 := (hx5 ⟨w - 13, by omega⟩).2
          have e : 13 + (w - 13) = w := by omega
          simp only [e] at h0
          rw [h0]
          simp [uv, Fin.ext_iff] <;> omega
      refine ⟨fun _ => ⟨hx5w, hYZU⟩, ?_⟩
      intro h1 h2 h3
      rw [hYZU, h2, h3] at h1
      exact absurd h1 (by decide)
    · by_cases hwm : w < 26 + x2.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
        have hjm : j < x2.gates.length := by omega
        obtain ⟨g, hg⟩ : ∃ g, x2.gates[j]? = some g := ⟨x2.gates[j], List.getElem?_eq_getElem hjm⟩
        obtain ⟨hop, a, b, hab, _, ha, hb⟩ := hgate j g hg
        have hga := gateAt_of x2 j g hg
        have hrj := hrec j g a b hg hab
        have wY := W_gate x2 (yv x3 x4) j g a b hg hab ha hb
        have wZ := W_gate x2 (zv x3) j g a b hg hab ha hb
        have wU := W_gate x2 (uv x4) j g a b hg hab ha hb
        have hj26 : 26 + j - 26 = j := by omega
        have pureOf : ∀ c, c < 26 + j → c ∈ g.inputs →
            (∀ k, PEqualNP.EdgeOwnership.InCone 26 x2 k j →
              (PEqualNP.MetaComplexity.NestedCover.gateAt x2 k).op ≠ GateOp.and) →
            Pure x2 c := by
          intro c hc hcin hcone
          by_cases hc26 : c < 26
          · exact Or.inl hc26
          · right
            obtain ⟨i, rfl⟩ : ∃ i, c = 26 + i := ⟨c - 26, by omega⟩
            have e : 26 + i - 26 = i := by omega
            rw [e]
            obtain ⟨hc1, hc2⟩ := cone_step x2 j i g hg hcin (by omega)
            exact ⟨by omega, hcone i hc1, fun k hk => hcone k (hc2 k hk)⟩
        have hain : a ∈ g.inputs := by rw [hab]; simp
        have hbin : b ∈ g.inputs := by rw [hab]; simp
        rcases hop with hand | hor
        · have hcone : ∀ k, PEqualNP.EdgeOwnership.InCone 26 x2 k j →
              (PEqualNP.MetaComplexity.NestedCover.gateAt x2 k).op ≠ GateOp.and :=
            fun k hk => ap_zero x2 hAP k j hjm (by rw [hga]; exact hand) hk
          obtain ⟨xa, ya⟩ := (ih a (by omega)).1 (pureOf a ha hain hcone)
          obtain ⟨xb, yb⟩ := (ih b (by omega)).1 (pureOf b hb hbin hcone)
          have h5 : x5 (26 + j) = (W x2 (zv x3) a && x5 b || x5 a && W x2 (zv x3) b) :=
            hrj.1 hand
          refine ⟨fun hp => ?_, fun h1 h2 h3 => ?_⟩
          · exfalso
            rcases hp with hp | hp
            · omega
            · rw [hj26, hga] at hp; exact hp.2.1 hand
          · rw [wY, hand, eval_and, ya, yb] at h1
            rw [wZ, hand, eval_and] at h2
            rw [wU, hand, eval_and] at h3
            rw [h5, xa, xb]
            exact and_case _ _ _ _ h1 h2 h3
        · have h5 : x5 (26 + j) = (x5 a || x5 b) := hrj.2 hor
          refine ⟨fun hp => ?_, fun h1 h2 h3 => ?_⟩
          · rcases hp with hp | hp
            · omega
            rw [hj26] at hp
            obtain ⟨xa, ya⟩ := (ih a (by omega)).1 (pureOf a ha hain hp.2.2)
            obtain ⟨xb, yb⟩ := (ih b (by omega)).1 (pureOf b hb hbin hp.2.2)
            rw [h5, xa, xb, wY, wZ, wU, hor, eval_or, eval_or, eval_or, ya, yb]
            exact ⟨rfl, or_mix _ _ _ _⟩
          · rw [wY, hor, eval_or] at h1
            rw [wZ, hor, eval_or] at h2
            rw [wU, hor, eval_or] at h3
            rw [h5]
            exact or_case _ _ _ _ _ _ _ _ (ih a (by omega)).2 (ih b (by omega)).2 h1 h2 h3
      · have hYo := W_out x2 (yv x3 x4) w (by omega)
        refine ⟨fun hp => ?_, fun h1 _ _ => ?_⟩
        · rcases hp with hp | hp
          · omega
          · omega
        · rw [hYo] at h1; exact absurd h1 (by decide)
  have hY : W x2 (yv x3 x4) x2.output = true :=
    (hcomp (yv x3 x4)).2 ⟨x3, x4, hinc, by simp [yv], by simp [yv]⟩
  have hZ : W x2 (zv x3) x2.output = false := by
    cases h : W x2 (zv x3) x2.output
    · rfl
    · obtain ⟨p, l, _, _, hl⟩ := (hcomp (zv x3)).1 h
      have := x3.isLt
      simp [zv, Fin.ext_iff] at hl
      omega
  have hU : W x2 (uv x4) x2.output = false := by
    cases h : W x2 (uv x4) x2.output
    · rfl
    · obtain ⟨p, l, _, hp, _⟩ := (hcomp (uv x4)).1 h
      have := p.isLt
      simp [uv, Fin.ext_iff] at hp
      omega
  exact (key x2.output).2 hY hZ hU

end PEqualNP.Outside.L_meta_2067

theorem PEqualNP.Outside.L_meta_2067 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin (13 : ℕ)) (x5 : ℕ → Bool),   (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x7 → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x9 : ℕ) (x10 : ℕ), x7.inputs = [x9, x10] ∧ x9 ≠ x10 ∧ x9 < (26 : ℕ) + x6 ∧ x10 < (26 : ℕ) + x6) →     (∀ (x7 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x8 - x9 ∈ x1 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →       PEqualNP.TopForm.andPairs (26 : ℕ) x2 = (0 : ℕ) →         x3 - x4 ∈ x1 →           (∀ (x10 : Fin (13 : ℕ)), x5 ↑x10 = Bool.false ∧ x5 ((13 : ℕ) + ↑x10) = Decidable.decide (x10 = x4)) →             (have x11 : List Bool := x2.wires (List.ofFn fun (x11 : Fin (26 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (13 : ℕ) x3));               ∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 x15 : ℕ), x2.gates[x12]? = Option.some x13 → x13.inputs = [x14, x15] → (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x12) = (x11.getD x14 Bool.false && x5 x15 || x5 x14 && x11.getD x15 Bool.false)) ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x12) = (x5 x14 || x5 x15))) →               x5 x2.output = Bool.true := by
  intro x1 x2 x3 x4 x5 h1 h2 h3 h4 h5 h6
  exact PEqualNP.Outside.L_meta_2067.main x1 x2 x3 x4 x5 h1 h2 h3 h4 h5 h6
