import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8207

open PEqualNP.CircuitLowerBounds

def ext (N o : ℕ) : List Gate :=
  [⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [N, 10]⟩, ⟨GateOp.or, [N + 1, 3]⟩, ⟨GateOp.and, [N + 2, 20]⟩,
   ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [N + 4, 11]⟩, ⟨GateOp.or, [N + 5, 4]⟩, ⟨GateOp.and, [N + 6, 21]⟩,
   ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [N + 8, 12]⟩, ⟨GateOp.or, [N + 9, 5]⟩, ⟨GateOp.and, [N + 10, 22]⟩,
   ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [N + 12, 0]⟩, ⟨GateOp.or, [N + 13, 6]⟩, ⟨GateOp.and, [N + 14, 23]⟩,
   ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [N + 16, 1]⟩, ⟨GateOp.or, [N + 17, 7]⟩, ⟨GateOp.and, [N + 18, 24]⟩,
   ⟨GateOp.or, [12, 0]⟩, ⟨GateOp.or, [N + 20, 2]⟩, ⟨GateOp.or, [N + 21, 8]⟩, ⟨GateOp.and, [N + 22, 25]⟩,
   ⟨GateOp.or, [N + 3, N + 7]⟩, ⟨GateOp.or, [N + 24, N + 11]⟩, ⟨GateOp.or, [N + 25, N + 15]⟩,
   ⟨GateOp.or, [N + 26, N + 19]⟩, ⟨GateOp.or, [N + 27, N + 23]⟩, ⟨GateOp.or, [o, N + 28]⟩]

def S : List (ℕ × ℕ) :=
  [(7, 20), (8, 20), (10, 20), (3, 20), (8, 21), (9, 21), (11, 21), (4, 21),
   (9, 22), (10, 22), (12, 22), (5, 22), (10, 23), (11, 23), (0, 23), (6, 23),
   (11, 24), (12, 24), (1, 24), (7, 24), (12, 25), (0, 25), (2, 25), (8, 25)]

theorem ext_length (N o : ℕ) : (ext N o).length = 30 := rfl

theorem rdL (w l : List Bool) (i : ℕ) (h : i < w.length) : (w ++ l).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem rdN (w l : List Bool) (j : ℕ) : (w ++ l).getD (w.length + j) false = l.getD j false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

theorem rd0 (w l : List Bool) : (w ++ l).getD w.length false = l.getD 0 false := by
  simpa using rdN w l 0

theorem rd27 (w l : List Bool) (i : ℕ) (hi : i < 27) (h : 27 ≤ w.length) :
    (w ++ l).getD i false = w.getD i false := rdL w l i (by omega)

theorem dist (a b c : Bool) : ((a || b) && c) = ((a && c) || (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem wires_append (gs gs' : List Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs ++ gs', o'⟩ x = gs'.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (Circuit.wires ⟨gs, o⟩ x) := by
  simp only [Circuit.wires, List.foldl_append]

theorem wires_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

theorem wires_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    exact rdL _ _ i h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem core (w : List Bool) (o : ℕ) (h27 : 27 ≤ w.length) (ho : o < w.length) :
    ((ext w.length o).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD (w.length + 29) false
      = (w.getD o false || S.any fun p => w.getD p.1 false && w.getD p.2 false) := by
  have hro : ∀ l : List Bool, (w ++ l).getD o false = w.getD o false := fun l => rdL w l o ho
  have r : ∀ i, i < 27 → ∀ l : List Bool, (w ++ l).getD i false = w.getD i false :=
    fun i hi l => rdL w l i (by omega)
  simp only [ext, S, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.append_assoc,
    List.cons_append, List.nil_append, rd0, rdN, r 0 (by norm_num), r 1 (by norm_num), r 2 (by norm_num), r 3 (by norm_num), r 4 (by norm_num), r 5 (by norm_num), r 6 (by norm_num), r 7 (by norm_num), r 8 (by norm_num), r 9 (by norm_num), r 10 (by norm_num), r 11 (by norm_num), r 12 (by norm_num), r 13 (by norm_num), r 14 (by norm_num), r 15 (by norm_num), r 16 (by norm_num), r 17 (by norm_num), r 18 (by norm_num), r 19 (by norm_num), r 20 (by norm_num), r 21 (by norm_num), r 22 (by norm_num), r 23 (by norm_num), r 24 (by norm_num), r 25 (by norm_num), hro, GateOp.eval, List.any_cons,
    List.any_nil, List.all_cons, List.all_nil, id, Bool.or_false, Bool.and_true,
    List.getD_cons_succ, List.getD_cons_zero, dist, Bool.or_assoc]

theorem sem (gs : List Gate) (o : ℕ) (xs : List Bool) (hx : xs.length = 27) (ho : o < 27 + gs.length) :
    Circuit.eval ⟨gs ++ ext (27 + gs.length) o, 27 + gs.length + 29⟩ xs
      = (Circuit.eval ⟨gs, o⟩ xs || S.any fun p => xs.getD p.1 false && xs.getD p.2 false) := by
  have hlen : (Circuit.wires ⟨gs, o⟩ xs).length = 27 + gs.length := by
    show (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs).length = _
    rw [wires_length, hx]
  have hpre : ∀ i, i < 27 → (Circuit.wires ⟨gs, o⟩ xs).getD i false = xs.getD i false := by
    intro i hi
    show (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs).getD i false = _
    exact wires_prefix gs xs i (by omega)
  unfold Circuit.eval
  rw [wires_append gs _ o, ← hlen, core _ o (by omega) (by omega)]
  congr 1
  simp only [S, List.any_cons, List.any_nil, hpre 0 (by norm_num), hpre 1 (by norm_num), hpre 2 (by norm_num), hpre 3 (by norm_num), hpre 4 (by norm_num), hpre 5 (by norm_num), hpre 6 (by norm_num), hpre 7 (by norm_num), hpre 8 (by norm_num), hpre 9 (by norm_num), hpre 10 (by norm_num), hpre 11 (by norm_num), hpre 12 (by norm_num), hpre 20 (by norm_num), hpre 21 (by norm_num), hpre 22 (by norm_num), hpre 23 (by norm_num), hpre 24 (by norm_num), hpre 25 (by norm_num)]

theorem hrbext (N o : ℕ) (ho : o < N) (h27 : 27 ≤ N) :
    ∀ k, k < 30 → ∀ i ∈ ((ext N o).getD k ⟨GateOp.or, []⟩).inputs, i < N + k := by
  intro k hk i hi
  interval_cases k <;> simp [ext] at hi <;> omega

theorem ofFn_getD (x9 : Fin 26 → Bool) (f : Fin 27 → Bool) (hf : ∀ i : Fin 26, f i.castSucc = x9 i)
    (i : ℕ) (h : i < 26) : (List.ofFn f).getD i false = x9 ⟨i, h⟩ := by
  have e : (List.ofFn f).getD i false = f ⟨i, by omega⟩ := by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  rw [e]
  exact hf ⟨i, h⟩

set_option maxRecDepth 100000 in
theorem key1 : ∀ a b : Fin 13, (7 : ℕ) ≤ (b : ℕ) →
    (∃ d ∈ ({(0 : Fin 13), (1 : Fin 13), (3 : Fin 13), (9 : Fin 13)} : Finset (Fin 13)), a = b + d) →
    ((a : ℕ), 13 + (b : ℕ)) ∈ S := by
  decide

set_option maxRecDepth 100000 in
theorem key2 : ∀ p ∈ S, ∃ a b : Fin 13, (7 : ℕ) ≤ (b : ℕ) ∧
    (∃ d ∈ ({(0 : Fin 13), (1 : Fin 13), (3 : Fin 13), (9 : Fin 13)} : Finset (Fin 13)), a = b + d) ∧
    (a : ℕ) = p.1 ∧ 13 + (b : ℕ) = p.2 := by
  decide

end PEqualNP.Outside.L_meta_8207

theorem PEqualNP.Outside.L_meta_8207 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x3 : Fin (26 : ℕ) → Bool) (x4 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (x3 (0 : Fin (26 : ℕ)) || x3 (1 : Fin (26 : ℕ))) x3 x4; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x4 → x4.output < (27 : ℕ) + x4.size → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x8 ∧ x8.size ≤ x4.size + (30 : ℕ) ∧ ∀ (x9 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x8 (x3 x9) = Bool.true ↔ PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x4 (x3 x9) = Bool.true ∨ ∃ (x10 : Fin (13 : ℕ)) (x11 : Fin (13 : ℕ)), (7 : ℕ) ≤ ↑x11 ∧ x2 x10 x11 ∧ x9 (Fin.castAdd (13 : ℕ) x10) = Bool.true ∧ x9 (Fin.natAdd (13 : ℕ) x11) = Bool.true := by
  intro x1 x2 x3 C hmon hrb hout
  obtain ⟨gs, o⟩ := C
  change o < 27 + gs.length at hout
  refine ⟨⟨gs ++ PEqualNP.Outside.L_meta_8207.ext (27 + gs.length) o, 27 + gs.length + 29⟩, ?_, ?_, ?_, ?_⟩
  · have hext : ∀ g ∈ PEqualNP.Outside.L_meta_8207.ext (27 + gs.length) o,
        g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} :
          Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 := by
      simp [PEqualNP.Outside.L_meta_8207.ext]
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hmon g hg
    · exact hext g hg
  · intro j hj i hi
    change j < (gs ++ PEqualNP.Outside.L_meta_8207.ext (27 + gs.length) o).length at hj
    rw [List.length_append, PEqualNP.Outside.L_meta_8207.ext_length] at hj
    change i ∈ ((gs ++ PEqualNP.Outside.L_meta_8207.ext (27 + gs.length) o).getD j
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs at hi
    by_cases hjl : j < gs.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl,
        ← List.getD_eq_getElem?_getD] at hi
      exact hrb j hjl i hi
    · obtain ⟨k, rfl⟩ : ∃ k, j = gs.length + k := ⟨j - gs.length, by omega⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        ← List.getD_eq_getElem?_getD] at hi
      have := PEqualNP.Outside.L_meta_8207.hrbext (27 + gs.length) o hout (by omega) k (by omega) i hi
      omega
  · show (gs ++ PEqualNP.Outside.L_meta_8207.ext (27 + gs.length) o).length ≤ gs.length + 30
    rw [List.length_append, PEqualNP.Outside.L_meta_8207.ext_length]
  · intro x9
    have atom : ∀ i (h : i < 26), (List.ofFn (x3 x9)).getD i false = x9 ⟨i, h⟩ :=
      fun i h => PEqualNP.Outside.L_meta_8207.ofFn_getD x9 (x3 x9) (fun j => by simp [x3]) i h
    simp only [PEqualNP.MetaComplexity.circuitFun]
    rw [PEqualNP.Outside.L_meta_8207.sem gs o _ (List.length_ofFn) hout, Bool.or_eq_true]
    apply or_congr Iff.rfl
    constructor
    · intro h
      rw [List.any_eq_true] at h
      obtain ⟨⟨p1, p2⟩, hp, hv⟩ := h
      obtain ⟨a, b, hb, hab, h1, h2⟩ := PEqualNP.Outside.L_meta_8207.key2 _ hp
      simp only at h1 h2
      subst h1 h2
      rw [Bool.and_eq_true] at hv
      refine ⟨a, b, hb, hab, ?_, ?_⟩
      · exact (atom a.val (by have := a.isLt; omega)).symm.trans hv.1
      · exact (atom (13 + b.val) (by have := b.isLt; omega)).symm.trans hv.2
    · rintro ⟨a, b, hb, hab, h1, h2⟩
      rw [List.any_eq_true]
      refine ⟨((a : ℕ), 13 + (b : ℕ)), PEqualNP.Outside.L_meta_8207.key1 a b hb hab, ?_⟩
      rw [Bool.and_eq_true]
      exact ⟨(atom a.val (by have := a.isLt; omega)).trans h1,
        (atom (13 + b.val) (by have := b.isLt; omega)).trans h2⟩
