import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2422

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gateAt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map fun i =>
          if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have hg : C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
  have h := foldl_step_gate C.gates (List.ofFn x) j _ hg
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h


lemma input_wire {n : ℕ} (C : Circuit) (z : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn z)).getD i false = z ⟨i, hi⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt _ _ i (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma path_true (n : ℕ) (C : Circuit) (R : ℕ → ℕ → Prop)
    (hR : R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = GateOp.or ∧
      ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs))
    (z : Fin n → Bool) (a b : ℕ) (hab : R a b) :
    (C.wires (List.ofFn z)).getD a false = true → (C.wires (List.ofFn z)).getD b false = true := by
  rw [hR] at hab
  induction hab with
  | refl => exact id
  | tail _ hst ih =>
    intro ha
    obtain ⟨hlt, rj, rfl, hrj, hop, hmem⟩ := hst
    rw [wires_gateAt C z rj hrj, hop]
    change (List.map _ _).any id = true
    rw [List.any_eq_true]
    refine ⟨_, List.mem_map_of_mem hmem, ?_⟩
    simp only [hlt, ↓reduceIte, id]
    exact ih ha

lemma and_true (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (z : Fin n → Bool)
    (j x y : ℕ) (hj : j < C.gates.length)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and)
    (hin : ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0 = x ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0 = y) ∨
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0 = y ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0 = x))
    (hx : (C.wires (List.ofFn z)).getD x false = true)
    (hy : (C.wires (List.ofFn z)).getD y false = true) :
    (C.wires (List.ofFn z)).getD (n + j) false = true := by
  obtain ⟨_, hRB, hlen⟩ := hC
  have ha : (C.wires (List.ofFn z)).getD
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) false = true := by
    rcases hin with ⟨h0, _⟩ | ⟨h0, _⟩ <;> rw [h0] <;> assumption
  have hb : (C.wires (List.ofFn z)).getD
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) false = true := by
    rcases hin with ⟨_, h1⟩ | ⟨_, h1⟩ <;> rw [h1] <;> assumption
  have hmem : PEqualNP.MetaComplexity.NestedCover.gateAt C j ∈ C.gates := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
  have h2len := hlen _ hmem
  have hback := hRB j hj
  rw [wires_gateAt C z j hj, hop]
  revert ha hb hback
  generalize (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = l at h2len ⊢
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp h2len
  intro ha hb hback
  have hra : a < n + j := hback a (by simp)
  have hrb : b < n + j := hback b (by simp)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at ha hb
  simp only [List.getD_eq_getElem?_getD] at ha hb
  change ([a, b].map _).all id = true
  simp [hra, hrb, ha, hb]

end PEqualNP.Outside.L_meta_2422

theorem PEqualNP.Outside.L_meta_2422 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ (g c cb : ℕ), (g < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 0 0) = c ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 1 0) = cb) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 0 0) = cb ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 1 0) = c))) → R (n + g) C.output → ∀ (p : Fin N) (l' : Fin M) (h1 a v h2 u b : ℕ), (h1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C h1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C h1).inputs.getD 0 0) = a ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C h1).inputs.getD 1 0) = v) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C h1).inputs.getD 0 0) = v ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C h1).inputs.getD 1 0) = a))) ∧ {x1 : Fin N | R (pw x1) a} = {p} → (∃ m1 : Fin M, R (lw m1) v ∧ ¬ I p m1) → R (n + h1) c → (h2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C h2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C h2).inputs.getD 0 0) = u ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C h2).inputs.getD 1 0) = b) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C h2).inputs.getD 0 0) = b ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C h2).inputs.getD 1 0) = u))) → {y1 : Fin M | R (lw y1) b} = {l'} → (∃ z1 : Fin N, R (pw z1) u ∧ ¬ I z1 l') → R (n + h2) cb → ¬ I p l' → ∀ m : Fin M, R (lw m) v → ¬ I p m → ∀ z : Fin N, R (pw z) u → ¬ I z l' → I z m := by
  intro n N M pw lw I C hC _ _ _ hpn hln hsound R hR g c cb hgate hRo p l' h1 a v h2 u b hh1 _ hRc hh2 hbset _ hRcb hpl' m hRm hpm z hRz hzl'
  obtain ⟨⟨hh1j, hh1op, hh1in⟩, haset⟩ := hh1
  obtain ⟨hgj, hgop, hgin⟩ := hgate
  obtain ⟨hh2j, hh2op, hh2in⟩ := hh2
  classical
  by_contra hzm
  have hRa : R (pw p) a := by
    have hp : p ∈ {x1 : Fin N | R (pw x1) a} := by rw [haset]; rfl
    exact hp
  have hRb : R (lw l') b := by
    have hl : l' ∈ {y1 : Fin M | R (lw y1) b} := by rw [hbset]; rfl
    exact hl
  let P : Finset (Fin N) := {p, z}
  let Y : Finset (Fin M) := {m, l'}
  have hPc : P.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  have hYc : Y.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  have hPY : ∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3 := by
    intro p3 hp3 l3 hl3
    simp only [P, Y, Finset.mem_insert, Finset.mem_singleton] at hp3 hl3
    rcases hp3 with rfl | rfl <;> rcases hl3 with rfl | rfl <;> assumption
  have hfalse := hsound P Y hPc hYc hPY
  let zf : Fin n → Bool := fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)
  have hpt : ∀ q ∈ P, (C.wires (List.ofFn zf)).getD (pw q) false = true := by
    intro q hq
    rw [PEqualNP.Outside.L_meta_2422.input_wire C _ _ (hpn q)]
    simp only [zf, decide_eq_true_eq, Finset.mem_union, Finset.mem_image]
    exact Or.inl ⟨q, hq, rfl⟩
  have hlt : ∀ q ∈ Y, (C.wires (List.ofFn zf)).getD (lw q) false = true := by
    intro q hq
    rw [PEqualNP.Outside.L_meta_2422.input_wire C _ _ (hln q)]
    simp only [zf, decide_eq_true_eq, Finset.mem_union, Finset.mem_image]
    exact Or.inr ⟨q, hq, rfl⟩
  have hpath := fun x y (hxy : R x y) => PEqualNP.Outside.L_meta_2422.path_true n C R hR zf x y hxy
  have wa := hpath _ _ hRa (hpt p (by simp [P]))
  have wv := hpath _ _ hRm (hlt m (by simp [Y]))
  have wu := hpath _ _ hRz (hpt z (by simp [P]))
  have wb := hpath _ _ hRb (hlt l' (by simp [Y]))
  have wh1 := PEqualNP.Outside.L_meta_2422.and_true n C hC zf h1 a v hh1j hh1op hh1in wa wv
  have wh2 := PEqualNP.Outside.L_meta_2422.and_true n C hC zf h2 u b hh2j hh2op hh2in wu wb
  have wc := hpath _ _ hRc wh1
  have wcb := hpath _ _ hRcb wh2
  have wg := PEqualNP.Outside.L_meta_2422.and_true n C hC zf g c cb hgj hgop hgin wc wcb
  have wo := hpath _ _ hRo wg
  unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval at hfalse
  change (C.wires (List.ofFn zf)).getD C.output false = false at hfalse
  rw [wo] at hfalse
  exact Bool.noConfusion hfalse
