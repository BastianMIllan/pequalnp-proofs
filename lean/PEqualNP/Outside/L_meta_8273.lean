import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8273
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem evalMono (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  intro h
  have hleg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    refine ⟨?_, (hC g hg).2⟩
    rcases (hC g hg).1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  exact mono2 C.gates hleg _ _ (by simp) (ofFn_mono n x y hxy) C.output h

theorem lastMono (m : ℕ) (a b : Fin m → Bool) (p q : Bool) (hab : ∀ i, a i = true → b i = true)
    (hpq : p = true → q = true) (k : Fin (m + 1)) :
    (Fin.lastCases p a k : Bool) = true → (Fin.lastCases q b k : Bool) = true := by
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp only [Fin.lastCases_last]; exact hpq
  · simp only [Fin.lastCases_castSucc]; exact hab i

theorem orMono (a b c d : Bool) (h1 : a = true → c = true) (h2 : b = true → d = true) :
    (a || b) = true → (c || d) = true := by
  intro h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · simp [h1 h]
  · simp [h2 h]

theorem fMono (x1 : Fin 42) (x2 x3 : Fin 43) (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (a b : Fin 42 → Bool)
    (hab : ∀ i, a i = true → b i = true) :
    C.eval (List.ofFn fun (k : Fin (43 + 1)) =>
      (Fin.lastCases ((fun (j : Fin (42 + 1)) => (Fin.lastCases (a 0 || a x1) a j : Bool)) x2 ||
        (fun (j : Fin (42 + 1)) => (Fin.lastCases (a 0 || a x1) a j : Bool)) x3)
        (fun (j : Fin (42 + 1)) => (Fin.lastCases (a 0 || a x1) a j : Bool)) k : Bool)) = true →
    C.eval (List.ofFn fun (k : Fin (43 + 1)) =>
      (Fin.lastCases ((fun (j : Fin (42 + 1)) => (Fin.lastCases (b 0 || b x1) b j : Bool)) x2 ||
        (fun (j : Fin (42 + 1)) => (Fin.lastCases (b 0 || b x1) b j : Bool)) x3)
        (fun (j : Fin (42 + 1)) => (Fin.lastCases (b 0 || b x1) b j : Bool)) k : Bool)) = true := by
  have h0 : (a 0 || a x1) = true → (b 0 || b x1) = true := orMono _ _ _ _ (hab 0) (hab x1)
  have h8 : ∀ j : Fin (42 + 1), (Fin.lastCases (a 0 || a x1) a j : Bool) = true →
      (Fin.lastCases (b 0 || b x1) b j : Bool) = true := fun j => lastMono 42 a b _ _ hab h0 j
  apply evalMono _ C hC
  intro k
  exact lastMono 43 _ _ _ _ h8 (orMono _ _ _ _ (h8 x2) (h8 x3)) k

theorem key (R : Fin 42 → Fin 42 → Prop) (f : (Fin 42 → Bool) → Bool)
    (hm : ∀ a b : Fin 42 → Bool, (∀ i, a i = true → b i = true) → f a = true → f b = true)
    (H1 : ∀ i j : Fin 42, R i j → f (fun k => decide (k = i ∨ k = j)) = true)
    (H2 : ∀ (A B : Fin 21 → Bool),
      (∀ u : Fin 21, A u = true ↔ ∀ v : Fin 21, B v = true → ¬ R (Fin.castAdd 21 u) (Fin.natAdd 21 v)) →
      (∀ v : Fin 21, B v = true ↔ ∀ u : Fin 21, A u = true → ¬ R (Fin.castAdd 21 u) (Fin.natAdd 21 v)) →
      f (fun k => Fin.addCases A B k) = false)
    (x : Fin 42 → Bool) : f x = true ↔ ∃ i j, R i j ∧ x i = true ∧ x j = true := by
  classical
  constructor
  · intro hfx
    by_contra hne
    let A : Fin 21 → Bool := fun u =>
      decide (∀ v : Fin 21, x (Fin.natAdd 21 v) = true → ¬ R (Fin.castAdd 21 u) (Fin.natAdd 21 v))
    let B : Fin 21 → Bool := fun v =>
      decide (∀ u : Fin 21, A u = true → ¬ R (Fin.castAdd 21 u) (Fin.natAdd 21 v))
    have hA : ∀ u : Fin 21, A u = true ↔ ∀ v : Fin 21, B v = true → ¬ R (Fin.castAdd 21 u) (Fin.natAdd 21 v) := by
      intro u
      constructor
      · intro hu v hv
        have := of_decide_eq_true hv
        exact this u hu
      · intro hu
        apply decide_eq_true
        intro v hxv
        apply hu v
        apply decide_eq_true
        intro u' hu'
        exact (of_decide_eq_true hu') v hxv
    have hB : ∀ v : Fin 21, B v = true ↔ ∀ u : Fin 21, A u = true → ¬ R (Fin.castAdd 21 u) (Fin.natAdd 21 v) := by
      intro v
      constructor
      · intro hv; exact of_decide_eq_true hv
      · intro hv; exact decide_eq_true hv
    have hfalse := H2 A B hA hB
    have hle : ∀ k : Fin (21 + 21), x k = true → (Fin.addCases A B k : Bool) = true := by
      intro k
      induction k using Fin.addCases with
      | left u =>
        intro hxu
        rw [Fin.addCases_left]
        apply decide_eq_true
        intro v hxv hR
        exact hne ⟨_, _, hR, hxu, hxv⟩
      | right v =>
        intro hxv
        rw [Fin.addCases_right]
        apply decide_eq_true
        intro u hu
        exact (of_decide_eq_true hu) v hxv
    have := hm x _ hle hfx
    rw [hfalse] at this
    exact absurd this (by simp)
  · rintro ⟨i, j, hR, hi, hj⟩
    apply hm _ _ _ (H1 i j hR)
    intro k hk
    have hk' := of_decide_eq_true hk
    rcases hk' with rfl | rfl
    · exact hi
    · exact hj

end PEqualNP.Outside.L_meta_8273

open PEqualNP.Outside.L_meta_8273 in
theorem PEqualNP.Outside.L_meta_8273 : ∀ (x1 : Fin (42 : ℕ)) (x2 x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop),   PEqualNP.MetaComplexity.Monotone2 x4 →     have x7 : (Fin (42 : ℕ) → Bool) → Bool := fun (x7 : Fin (42 : ℕ) → Bool) =>       have x8 : Fin (43 : ℕ) → Bool := fun (x8 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x7 (0 : Fin (42 : ℕ)) || x7 x1) x7 x8;       x4.eval (List.ofFn fun (x9 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x8 x2 || x8 x3) x8 x9);     ((∀ (x8 x9 : Fin (42 : ℕ)), x5 x8 x9 → (x7 fun (x11 : Fin (42 : ℕ)) => Decidable.decide (x11 = x8 ∨ x11 = x9)) = Bool.true) ∧         ∀ (x8 x9 : Fin (21 : ℕ) → Bool),           have x10 : Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x10 x11 : Fin (21 : ℕ)) => x5 (Fin.castAdd (21 : ℕ) x10) (Fin.natAdd (21 : ℕ) x11);           (∀ (x11 : Fin (21 : ℕ)), x8 x11 = Bool.true ↔ ∀ (x12 : Fin (21 : ℕ)), x9 x12 = Bool.true → ¬x10 x11 x12) → (∀ (x12 : Fin (21 : ℕ)), x9 x12 = Bool.true ↔ ∀ (x13 : Fin (21 : ℕ)), x8 x13 = Bool.true → ¬x10 x13 x12) → (x7 fun (x13 : Fin (42 : ℕ)) => Fin.addCases x8 x9 x13) = Bool.false) →       ∀ (x9 : Fin (42 : ℕ) → Bool), x7 x9 = Bool.true ↔ ∃ (x10 : Fin (42 : ℕ)) (x11 : Fin (42 : ℕ)), x5 x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true := by
  intro x1 x2 x3 x4 x5 hC x7 H x9
  exact key x5 x7 (fun a b hab => fMono x1 x2 x3 x4 hC a b hab) H.1 H.2 x9
