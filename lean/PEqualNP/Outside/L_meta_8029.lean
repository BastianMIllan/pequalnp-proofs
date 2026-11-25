import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8029
open PEqualNP.CircuitLowerBounds

def E : List (Fin 11 × Fin 11) := [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
  (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

def M : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540,
  582, 596, 1066, 1186, 1288, 1408, 1546]

def le (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i : ℕ, a.getD i false = true → b.getD i false = true

theorem key (l : List Bool) (v : Bool) (i : ℕ) :
    (l ++ [v]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then v else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have h3 : i - l.length ≠ 0 := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h3
    rw [hk]; simp

theorem step_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (a b : List Bool)
    (h : le a b) :
    le (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)])
      (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]) := by
  obtain ⟨hl, hp⟩ := h
  refine ⟨by simp [hl], ?_⟩
  intro i hi
  have hev : g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
    rcases hg with hg | hg
    · rw [hg]
      simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
      intro h j hj
      exact hp j (h j hj)
    · rw [hg]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
      rintro ⟨j, hj, h⟩
      exact ⟨j, hj, hp j h⟩
  rw [key] at hi ⊢
  rw [← hl]
  split_ifs at hi ⊢ with h1 h2
  · exact hp i hi
  · exact hev hi

theorem wires_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, le a b →
      le (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b) := by
  induction gs with
  | nil => intro a b h; exact h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (by simp [hg'])) _ _
      (step_mono g (hgs g (by simp)) a b h)

theorem le_ofFn (f g : Fin 11 → Bool) (h : ∀ i, f i = true → g i = true) :
    le (List.ofFn f) (List.ofFn g) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hi11 : i < 11
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi11, dite_true,
      Option.getD_some] at hi ⊢
    exact h _ hi
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi11] at hi

def enc : List Bool → ℕ
  | [] => 0
  | b :: a => 2 * enc a + (bif b then 1 else 0)

theorem enc_inv : ∀ a : List Bool, ∀ i : ℕ, (enc a).testBit i = a.getD i false := by
  intro a
  induction a with
  | nil => intro i; simp [enc]
  | cons b a ih =>
    intro i
    cases i with
    | zero =>
      rw [Nat.testBit_zero]
      cases b <;> simp [enc] <;> omega
    | succ i =>
      rw [Nat.testBit_add_one, List.getD_cons_succ, ← ih i]
      congr 1
      cases b <;> simp [enc] <;> omega

theorem enc_lt : ∀ a : List Bool, enc a < 2 ^ a.length := by
  intro a
  induction a with
  | nil => simp [enc]
  | cons b a ih =>
    simp only [List.length_cons, pow_succ]
    cases b <;> simp [enc] <;> omega

def good (n : ℕ) : Bool :=
  (E.any fun e => n.testBit e.1.val && n.testBit e.2.val) ||
    M.any fun m => (List.finRange 11).all fun i => !n.testBit i.val || m.testBit i.val

theorem allgood : (List.range (2 ^ 11)).all good = true := by decide +kernel

theorem cover (x : Fin 11 → Bool) (hf : (E.any fun e => x e.1 && x e.2) = false) :
    ∃ m ∈ M, ∀ i : Fin 11, x i = true → m.testBit i.val = true := by
  obtain ⟨n, hn⟩ : ∃ n, n = enc (List.ofFn x) := ⟨_, rfl⟩
  have hx : ∀ i : Fin 11, n.testBit i.val = x i := by
    intro i
    rw [hn, enc_inv]
    fin_cases i <;> first | rfl | simp [List.getD_eq_getElem?_getD]
  have hlt : n < 2 ^ 11 := by
    have := enc_lt (List.ofFn x)
    rw [List.length_ofFn] at this
    rw [hn]; exact this
  have hg := List.all_eq_true.mp allgood n (List.mem_range.mpr hlt)
  unfold good at hg
  simp only [hx] at hg
  rw [hf, Bool.false_or] at hg
  obtain ⟨m, hm, hall⟩ := List.any_eq_true.mp hg
  refine ⟨m, hm, fun i hi => ?_⟩
  have := List.all_eq_true.mp hall i (List.mem_finRange i)
  rw [hi] at this
  simpa using this

theorem main (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hacc : ∀ e ∈ E, C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput e.1 e.2)) = true)
    (hrej : ∀ m ∈ M, C.eval (List.ofFn fun i : Fin 11 => m.testBit i.val) = false) :
    PEqualNP.MetaComplexity.circuitFun 11 C = fun x => E.any fun e => x e.1 && x e.2 := by
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h := (hm g hg).1
    simpa using h
  have emono : ∀ a b : List Bool, le a b → C.eval a = true → C.eval b = true :=
    fun a b h ha => (wires_mono C.gates hops a b h).2 C.output ha
  funext x
  show C.eval (List.ofFn x) = E.any fun e => x e.1 && x e.2
  cases hf : (E.any fun e => x e.1 && x e.2)
  · obtain ⟨m, hmM, hsub⟩ := cover x hf
    have hr := hrej m hmM
    cases hc : C.eval (List.ofFn x)
    · rfl
    · have := emono _ _ (le_ofFn x (fun i => m.testBit i.val) hsub) hc
      rw [hr] at this
      exact absurd this (by simp)
  · obtain ⟨e, he, hx⟩ := List.any_eq_true.mp hf
    rw [Bool.and_eq_true] at hx
    apply emono _ _ (le_ofFn _ _ ?_) (hacc e he)
    intro i hi
    simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact hx.1
    · exact hx.2

end PEqualNP.Outside.L_meta_8029

theorem PEqualNP.Outside.L_meta_8029 : have x1 : List (Fin (11 : ℕ) × Fin (11 : ℕ)) := [((0 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), ((0 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((3 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))), ((3 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))), ((4 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), ((4 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((5 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), ((5 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((7 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), ((8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)))]; have x2 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → (∀ x5 ∈ x1, x3.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput x5.1 x5.2)) = Bool.true) → (∀ x6 ∈ x2, x3.eval (List.ofFn fun (x8 : Fin (11 : ℕ)) => x6.testBit ↑x8) = Bool.false) → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 = fun (x7 : Fin (11 : ℕ) → Bool) => x1.any fun (x8 : Fin (11 : ℕ) × Fin (11 : ℕ)) => x7 x8.1 && x7 x8.2 := by
  dsimp only
  intro C hm hacc hrej
  exact PEqualNP.Outside.L_meta_8029.main C hm hacc hrej
