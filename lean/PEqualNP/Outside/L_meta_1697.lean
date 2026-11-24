import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1697
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def rl (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

def rc (ρ : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (rl ρ), ρ C.output⟩

theorem step (ρ : ℕ → ℕ) (n : ℕ) (hlt : ∀ i, i < n → ρ i < n) (hge : ∀ i, n ≤ i → ρ i = i)
    (w w' : List Bool) (v : Bool) (hl : w.length = w'.length) (hn : n ≤ w.length)
    (h : ∀ i, w'.getD (ρ i) false = w.getD i false) (i : ℕ) :
    (w' ++ [v]).getD (ρ i) false = (w ++ [v]).getD i false := by
  by_cases hi : i = w.length
  · have e1 : (w ++ [v]).getD i false = v := by rw [hi]; exact getD_snoc_eq _ _ _
    have e2 : (w' ++ [v]).getD (ρ i) false = v := by
      rw [hge i (by omega), hi, hl]; exact getD_snoc_eq _ _ _
    rw [e1, e2]
  · have hr : ρ i ≠ w'.length := by
      by_cases hin : i < n
      · have := hlt i hin; omega
      · rw [hge i (by omega)]; omega
    rw [getD_snoc_ne _ _ _ _ hr, getD_snoc_ne _ _ _ _ hi]; exact h i

theorem rel_wires (ρ : ℕ → ℕ) (n : ℕ) (hlt : ∀ i, i < n → ρ i < n) (hge : ∀ i, n ≤ i → ρ i = i)
    (gs : List Gate) :
    ∀ w w' : List Bool, w.length = w'.length → n ≤ w.length →
      (∀ i, w'.getD (ρ i) false = w.getD i false) →
      ∀ i, (wiresFrom (gs.map (rl ρ)) w').getD (ρ i) false = (wiresFrom gs w).getD i false := by
  induction gs with
  | nil => intro w w' _ _ h i; exact h i
  | cons g gs ih =>
    intro w w' hl hn h
    have e : g.op.eval ((g.inputs.map ρ).map fun i => w'.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      rw [List.map_map]
      exact congrArg g.op.eval (List.map_congr_left (fun a _ => h a))
    show ∀ i, (wiresFrom (gs.map (rl ρ))
        (w' ++ [g.op.eval ((g.inputs.map ρ).map fun i => w'.getD i false)])).getD (ρ i) false
        = (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false
    rw [e]
    exact ih _ _ (by simp [hl]) (by simp; omega)
      (step ρ n hlt hge w w' _ hl hn h)

theorem fan_rc (ρ : ℕ → ℕ) (C : Circuit) (h : FanInTwo C) : FanInTwo (rc ρ C) := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  have := h g0 hg0
  exact ⟨this.1, by simpa [rl] using this.2⟩

def u (y : Fin 9 → Bool) (i : ℕ) : Bool := (List.ofFn y).getD i false

theorem u_eq (y : Fin 9 → Bool) (i : ℕ) : u y i = if h : i < 9 then y ⟨i, h⟩ else false := by
  unfold u
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> rfl

def lift (σ : Fin 9 → Fin 9) : ℕ → ℕ := fun i => if h : i < 9 then (σ ⟨i, h⟩).val else i

theorem lift_lt (σ : Fin 9 → Fin 9) : ∀ i, i < 9 → lift σ i < 9 := by
  intro i hi
  simp only [lift, dif_pos hi]
  exact (σ ⟨i, hi⟩).isLt

theorem lift_ge (σ : Fin 9 → Fin 9) : ∀ i, 9 ≤ i → lift σ i = i := by
  intro i hi
  simp only [lift, dif_neg (not_lt.mpr hi)]

theorem base (σ : Fin 9 → Fin 9) (y : Fin 9 → Bool) (i : ℕ) :
    u y (lift σ i) = u (fun k => y (σ k)) i := by
  rw [u_eq, u_eq]
  by_cases hi : i < 9
  · simp [lift, hi]
  · simp [lift, hi]

theorem rc_wires (C : Circuit) (σ : Fin 9 → Fin 9) (y : Fin 9 → Bool) (i : ℕ) :
    ((rc (lift σ) C).wires (List.ofFn y)).getD (lift σ i) false
      = (C.wires (List.ofFn fun k => y (σ k))).getD i false := by
  rw [wires_eq, wires_eq]
  exact rel_wires (lift σ) 9 (lift_lt σ) (lift_ge σ) C.gates (List.ofFn fun k => y (σ k))
    (List.ofFn y) (by simp) (by simp) (fun i => base σ y i) i

def fP : (Fin 9 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

theorem transport (C : Circuit) (hC : FanInTwo C) (σ : Fin 9 → Fin 9)
    (hσ : ∀ y : Fin 9 → Bool, fP (fun k => y (σ k)) = fP y)
    (hf : circuitFun 9 C = fP) (h : (Fin 9 → Bool) → Bool)
    (hw : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = h y)
    (Q : ∀ C' : Circuit, FanInTwo C' →
      (∀ y : Fin 9 → Bool, (C'.wires (List.ofFn y)).getD 9 false = h (fun k => y (σ k))) →
      circuitFun 9 C' = fP → 16 ≤ C'.size) : 16 ≤ C.size := by
  have key := rc_wires C σ
  have h9 : lift σ 9 = 9 := lift_ge σ 9 (le_refl 9)
  have := Q (rc (lift σ) C) (fan_rc _ C hC) (fun y => by
      have k9 := key y 9
      rw [h9] at k9
      rw [k9, hw]) (by
      funext y
      exact (key y C.output).trans ((congrFun hf (fun k => y (σ k))).trans (hσ y)))
  simpa [rc, Circuit.size] using this

def gf (g : Gate) (y : Fin 9 → Bool) : Bool := g.op.eval (g.inputs.map fun i => u y i)

theorem u_cases (i : ℕ) : (∃ a : Fin 9, ∀ y : Fin 9 → Bool, u y i = y a) ∨
    (∀ y : Fin 9 → Bool, u y i = false) := by
  by_cases h : i < 9
  · exact Or.inl ⟨⟨i, h⟩, fun y => by rw [u_eq, dif_pos h]⟩
  · exact Or.inr (fun y => by rw [u_eq, dif_neg h])

theorem classify (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2)
    (hA : ∃ x y : Fin 9 → Bool, gf g x ≠ gf g y)
    (hB : ∀ i : Fin 9, ∃ x : Fin 9 → Bool, x i ≠ gf g x) :
    (∃ a : Fin 9, ∀ y, gf g y = !(y a)) ∨
    (∃ a b : Fin 9, a ≠ b ∧ ∀ y, gf g y = (y a && y b)) ∨
    (∃ a b : Fin 9, a ≠ b ∧ ∀ y, gf g y = (y a || y b)) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  match ins, hlen with
  | [], _ =>
    exfalso
    obtain ⟨x, y, h⟩ := hA
    rcases hop with rfl | rfl | rfl <;> simp [gf, GateOp.eval] at h
  | [i], _ =>
    rcases u_cases i with ⟨a, ha⟩ | ha <;> rcases hop with rfl | rfl | rfl
    all_goals first
      | (exfalso; obtain ⟨x, y, h⟩ := hA; simp [gf, GateOp.eval, ha] at h; done)
      | (exfalso; obtain ⟨x, h⟩ := hB a; simp [gf, GateOp.eval, ha] at h; done)
      | (refine Or.inl ⟨a, fun y => ?_⟩; simp [gf, GateOp.eval, ha]; done)
  | [i, j], _ =>
    rcases u_cases i with ⟨a, ha⟩ | ha <;> rcases u_cases j with ⟨b, hb⟩ | hb <;>
      rcases hop with rfl | rfl | rfl
    all_goals first
      | (exfalso; obtain ⟨x, y, h⟩ := hA; simp [gf, GateOp.eval, ha, hb] at h; done)
      | (exfalso; obtain ⟨x, h⟩ := hB a; simp [gf, GateOp.eval, ha, hb] at h; done)
      | (exfalso; obtain ⟨x, h⟩ := hB b; simp [gf, GateOp.eval, ha, hb] at h; done)
      | (refine Or.inl ⟨a, fun y => ?_⟩; simp [gf, GateOp.eval, ha, hb]; done)
      | (by_cases hab : a = b
         · exfalso; subst hab; obtain ⟨x, h⟩ := hB a; simp [gf, GateOp.eval, ha, hb] at h; done
         · first
           | (refine Or.inr (Or.inl ⟨a, b, hab, fun y => ?_⟩); simp [gf, GateOp.eval, ha, hb]; done)
           | (refine Or.inr (Or.inr ⟨a, b, hab, fun y => ?_⟩); simp [gf, GateOp.eval, ha, hb]; done))
  | _ :: _ :: _ :: _, hl => exact absurd hl (by simp)

theorem first_wire (g : Gate) (gs : List Gate) (y : Fin 9 → Bool) :
    (wiresFrom (g :: gs) (List.ofFn y)).getD 9 false = gf g y := by
  show (wiresFrom gs (List.ofFn y ++ [g.op.eval (g.inputs.map fun i => (List.ofFn y).getD i false)])).getD 9 false = _
  rw [getD_wiresFrom _ _ _ (by simp)]
  have := getD_snoc_eq (List.ofFn y) (g.op.eval (g.inputs.map fun i => (List.ofFn y).getD i false)) false
  rw [List.length_ofFn] at this
  exact this

def mk (l : List ℕ) : Fin 9 → Fin 9 := fun i => ⟨l.getD i.val 0 % 9, Nat.mod_lt _ (by norm_num)⟩

theorem inv0 (y : Fin 9 → Bool) : fP (fun k => y (mk [0, 1, 2, 3, 4, 5, 6, 7, 8] k)) = fP y := by
  have B : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool, ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by decide
  exact B (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)

theorem inv1 (y : Fin 9 → Bool) : fP (fun k => y (mk [0, 5, 8, 3, 4, 1, 7, 6, 2] k)) = fP y := by
  have B : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool, ((a0 && a5) || (a5 && a8) || (a8 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a1) || (a5 && a7) || (a8 && a6) || (a3 && a2) || (a1 && a6) || (a7 && a2) || (a2 && a1)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by decide
  exact B (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)

theorem inv2 (y : Fin 9 → Bool) : fP (fun k => y (mk [1, 0, 5, 8, 6, 2, 4, 7, 3] k)) = fP y := by
  have B : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool, ((a1 && a0) || (a0 && a5) || (a5 && a8) || (a8 && a6) || (a6 && a1) || (a1 && a2) || (a0 && a4) || (a5 && a7) || (a8 && a3) || (a2 && a7) || (a4 && a3) || (a3 && a2)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by decide
  exact B (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)

theorem inv3 (y : Fin 9 → Bool) : fP (fun k => y (mk [1, 2, 3, 8, 6, 0, 7, 4, 5] k)) = fP y := by
  have B : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool, ((a1 && a2) || (a2 && a3) || (a3 && a8) || (a8 && a6) || (a6 && a1) || (a1 && a0) || (a2 && a7) || (a3 && a4) || (a8 && a5) || (a0 && a4) || (a7 && a5) || (a5 && a0)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by decide
  exact B (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)

theorem inv4 (y : Fin 9 → Bool) : fP (fun k => y (mk [2, 1, 0, 5, 7, 3, 6, 4, 8] k)) = fP y := by
  have B : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool, ((a2 && a1) || (a1 && a0) || (a0 && a5) || (a5 && a7) || (a7 && a2) || (a2 && a3) || (a1 && a6) || (a0 && a4) || (a5 && a8) || (a3 && a4) || (a6 && a8) || (a8 && a3)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by decide
  exact B (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)

theorem inv5 (y : Fin 9 → Bool) : fP (fun k => y (mk [2, 3, 8, 5, 7, 1, 4, 6, 0] k)) = fP y := by
  have B : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool, ((a2 && a3) || (a3 && a8) || (a8 && a5) || (a5 && a7) || (a7 && a2) || (a2 && a1) || (a3 && a4) || (a8 && a6) || (a5 && a0) || (a1 && a6) || (a4 && a0) || (a0 && a1)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by decide
  exact B (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)

theorem inv6 (y : Fin 9 → Bool) : fP (fun k => y (mk [3, 2, 1, 0, 4, 8, 7, 6, 5] k)) = fP y := by
  have B : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool, ((a3 && a2) || (a2 && a1) || (a1 && a0) || (a0 && a4) || (a4 && a3) || (a3 && a8) || (a2 && a7) || (a1 && a6) || (a0 && a5) || (a8 && a6) || (a7 && a5) || (a5 && a8)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by decide
  exact B (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)

theorem inv7 (y : Fin 9 → Bool) : fP (fun k => y (mk [3, 8, 5, 0, 4, 2, 6, 7, 1] k)) = fP y := by
  have B : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool, ((a3 && a8) || (a8 && a5) || (a5 && a0) || (a0 && a4) || (a4 && a3) || (a3 && a2) || (a8 && a6) || (a5 && a7) || (a0 && a1) || (a2 && a7) || (a6 && a1) || (a1 && a2)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by decide
  exact B (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)

theorem inv8 (y : Fin 9 → Bool) : fP (fun k => y (mk [5, 0, 1, 2, 7, 8, 4, 6, 3] k)) = fP y := by
  have B : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool, ((a5 && a0) || (a0 && a1) || (a1 && a2) || (a2 && a7) || (a7 && a5) || (a5 && a8) || (a0 && a4) || (a1 && a6) || (a2 && a3) || (a8 && a6) || (a4 && a3) || (a3 && a8)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by decide
  exact B (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)

theorem inv9 (y : Fin 9 → Bool) : fP (fun k => y (mk [5, 8, 3, 2, 7, 0, 6, 4, 1] k)) = fP y := by
  have B : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool, ((a5 && a8) || (a8 && a3) || (a3 && a2) || (a2 && a7) || (a7 && a5) || (a5 && a0) || (a8 && a6) || (a3 && a4) || (a2 && a1) || (a0 && a4) || (a6 && a1) || (a1 && a0)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by decide
  exact B (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)

theorem inv10 (y : Fin 9 → Bool) : fP (fun k => y (mk [8, 3, 2, 1, 6, 5, 4, 7, 0] k)) = fP y := by
  have B : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool, ((a8 && a3) || (a3 && a2) || (a2 && a1) || (a1 && a6) || (a6 && a8) || (a8 && a5) || (a3 && a4) || (a2 && a7) || (a1 && a0) || (a5 && a7) || (a4 && a0) || (a0 && a5)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by decide
  exact B (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)

theorem inv11 (y : Fin 9 → Bool) : fP (fun k => y (mk [8, 5, 0, 1, 6, 3, 7, 4, 2] k)) = fP y := by
  have B : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool, ((a8 && a5) || (a5 && a0) || (a0 && a1) || (a1 && a6) || (a6 && a8) || (a8 && a3) || (a5 && a7) || (a0 && a4) || (a1 && a2) || (a3 && a4) || (a7 && a2) || (a2 && a3)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by decide
  exact B (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)


def autsL : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8], [0, 5, 8, 3, 4, 1, 7, 6, 2], [1, 0, 5, 8, 6, 2, 4, 7, 3], [1, 2, 3, 8, 6, 0, 7, 4, 5], [2, 1, 0, 5, 7, 3, 6, 4, 8], [2, 3, 8, 5, 7, 1, 4, 6, 0], [3, 2, 1, 0, 4, 8, 7, 6, 5], [3, 8, 5, 0, 4, 2, 6, 7, 1], [5, 0, 1, 2, 7, 8, 4, 6, 3], [5, 8, 3, 2, 7, 0, 6, 4, 1], [8, 3, 2, 1, 6, 5, 4, 7, 0], [8, 5, 0, 1, 6, 3, 7, 4, 2]]

theorem hinv : ∀ l ∈ autsL, ∀ y : Fin 9 → Bool, fP (fun k => y (mk l k)) = fP y := by
  intro l hl y
  simp only [autsL, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [inv0 y, inv1 y, inv2 y, inv3 y, inv4 y, inv5 y, inv6 y, inv7 y, inv8 y, inv9 y, inv10 y, inv11 y]

set_option maxRecDepth 8000 in
theorem hnotc : ∀ a : Fin 9, ∃ l ∈ autsL, mk l a = 0 ∨ mk l a = 4 := by decide

set_option maxRecDepth 8000 in
theorem hpairc : ∀ a b : Fin 9, a ≠ b → ∃ l ∈ autsL, (mk l a = 0 ∧ mk l b = 1) ∨ (mk l a = 1 ∧ mk l b = 0) ∨ (mk l a = 0 ∧ mk l b = 2) ∨ (mk l a = 2 ∧ mk l b = 0) ∨ (mk l a = 0 ∧ mk l b = 3) ∨ (mk l a = 3 ∧ mk l b = 0) ∨ (mk l a = 0 ∧ mk l b = 4) ∨ (mk l a = 4 ∧ mk l b = 0) ∨ (mk l a = 0 ∧ mk l b = 6) ∨ (mk l a = 6 ∧ mk l b = 0) ∨ (mk l a = 4 ∧ mk l b = 6) ∨ (mk l a = 6 ∧ mk l b = 4) := by decide

theorem single_false : ∀ o : Fin 9, fP (fun k => decide (k = o)) = false := by decide

end PEqualNP.Outside.L_meta_1697

open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1697

theorem PEqualNP.Outside.L_meta_1697 : (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true)) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 2)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 := by
  intro H N0 N4 A01 A02 A03 A04 A06 A46 O01 O02 O03 O04 O06 O46 hH
  obtain ⟨C, hC2, hsz, hev⟩ := hH
  classical
  have hex : ∃ s, ∃ D : Circuit, FanInTwo D ∧ D.size = s ∧ circuitFun 9 D = fP :=
    ⟨C.size, C, hC2, rfl, funext hev⟩
  obtain ⟨D, hD2, hDs, hDf⟩ := Nat.find_spec hex
  have hmin : IsMinimalCircuit 9 D :=
    ⟨hD2, fun E hE hEf => by rw [hDs]; exact Nat.find_min' hex ⟨E, hE, rfl, hEf.trans hDf⟩⟩
  have hDle : D.size ≤ 15 := by
    rw [hDs]; exact (Nat.find_min' hex ⟨C, hC2, rfl, funext hev⟩).trans hsz
  have hnc : ∃ x y : Fin 9 → Bool, circuitFun 9 D x ≠ circuitFun 9 D y :=
    ⟨fun _ => true, fun _ => false, by rw [hDf]; decide⟩
  obtain ⟨ha, hb, -, -⟩ := H 9 D hmin hnc
  suffices h16 : 16 ≤ D.size by omega
  rcases hg : D.gates with _ | ⟨g, gs⟩
  · exfalso
    have e : ∀ y, fP y = u y D.output := fun y => by
      rw [← hDf]
      show (D.wires (List.ofFn y)).getD D.output false = _
      rw [wires_eq, hg]; rfl
    by_cases ho : D.output < 9
    · have h1 := e (fun k => decide (k = ⟨D.output, ho⟩))
      rw [u_eq, dif_pos ho, single_false] at h1
      simp at h1
    · have h1 := e (fun _ => true)
      rw [u_eq, dif_neg ho] at h1
      exact absurd h1 (by decide)
  · have hgf : ∀ y, (D.wires (List.ofFn y)).getD 9 false = gf g y := fun y => by
      rw [wires_eq, hg]; exact first_wire g gs y
    have hlen : 0 < D.gates.length := by rw [hg]; simp
    have hA : ∃ x y : Fin 9 → Bool, gf g x ≠ gf g y := by
      obtain ⟨x, y, h⟩ := ha 0 hlen
      exact ⟨x, y, by rw [← hgf x, ← hgf y]; exact h⟩
    have hB : ∀ i : Fin 9, ∃ x : Fin 9 → Bool, x i ≠ gf g x := fun i => by
      obtain ⟨x, h⟩ := hb i.val 0 (by have := i.isLt; omega) hlen
      refine ⟨x, ?_⟩
      have e : (D.wires (List.ofFn x)).getD i.val false = x i := by
        rw [wires_eq, getD_wiresFrom _ _ _ (by simp)]
        exact (u_eq x i.val).trans (dif_pos i.isLt)
      rw [← hgf x, ← e]; exact h
    have hgm : g ∈ D.gates := by rw [hg]; simp
    rcases classify g (hD2 g hgm).1 (hD2 g hgm).2 hA hB with ⟨a, h⟩ | ⟨a, b, hab, h⟩ | ⟨a, b, hab, h⟩
    · obtain ⟨l, hl, hc⟩ := hnotc a
      rcases hc with e1 | e1
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => !(y a)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => N0 C' h1 (fun y => by rw [h2 y]; simp only [e1]) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => !(y a)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => N4 C' h1 (fun y => by rw [h2 y]; simp only [e1]) h3)
    · obtain ⟨l, hl, hc⟩ := hpairc a b hab
      rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a && y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => A01 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a && y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => A01 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]; exact Bool.and_comm _ _) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a && y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => A02 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a && y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => A02 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]; exact Bool.and_comm _ _) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a && y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => A03 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a && y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => A03 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]; exact Bool.and_comm _ _) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a && y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => A04 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a && y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => A04 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]; exact Bool.and_comm _ _) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a && y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => A06 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a && y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => A06 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]; exact Bool.and_comm _ _) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a && y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => A46 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a && y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => A46 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]; exact Bool.and_comm _ _) h3)

    · obtain ⟨l, hl, hc⟩ := hpairc a b hab
      rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a || y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => O01 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a || y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => O01 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]; exact Bool.or_comm _ _) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a || y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => O02 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a || y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => O02 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]; exact Bool.or_comm _ _) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a || y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => O03 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a || y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => O03 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]; exact Bool.or_comm _ _) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a || y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => O04 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a || y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => O04 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]; exact Bool.or_comm _ _) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a || y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => O06 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a || y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => O06 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]; exact Bool.or_comm _ _) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a || y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => O46 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]) h3)
      · exact transport D hD2 (mk l) (hinv l hl) hDf (fun y => (y a || y b)) (fun y => (hgf y).trans (h y)) (fun C' h1 h2 h3 => O46 C' h1 (fun y => by rw [h2 y]; simp only [e1, e2]; exact Bool.or_comm _ _) h3)

