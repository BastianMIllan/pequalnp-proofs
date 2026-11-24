import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2101

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Point star: for each point p in 5..12, OR its four lines, AND with p, then OR the eight results.
def ptGates (k p a b c d : ℕ) : List Gate :=
  [⟨GateOp.or, [13 + a, 13 + b]⟩, ⟨GateOp.or, [26 + 4 * k, 13 + c]⟩,
   ⟨GateOp.or, [27 + 4 * k, 13 + d]⟩, ⟨GateOp.and, [p, 28 + 4 * k]⟩]

def gs : List Gate :=
  ptGates 0 5 5 4 2 9 ++ ptGates 1 6 6 5 3 10 ++ ptGates 2 7 7 6 4 11 ++
  ptGates 3 8 8 7 5 12 ++ ptGates 4 9 9 8 6 0 ++ ptGates 5 10 10 9 7 1 ++
  ptGates 6 11 11 10 8 2 ++ ptGates 7 12 12 11 9 3 ++
  [⟨GateOp.or, [29, 33]⟩, ⟨GateOp.or, [58, 37]⟩, ⟨GateOp.or, [59, 41]⟩,
   ⟨GateOp.or, [60, 45]⟩, ⟨GateOp.or, [61, 49]⟩, ⟨GateOp.or, [62, 53]⟩,
   ⟨GateOp.or, [63, 57]⟩]

def C : Circuit := ⟨gs, 64⟩

def orv (a b : Bool) : Bool := GateOp.eval GateOp.or [a, b]
def andv (a b : Bool) : Bool := GateOp.eval GateOp.and [a, b]

def pt (L : List Bool) (p a b c d : ℕ) : Bool :=
  andv (L.getD p false)
    (orv (orv (orv (L.getD (13 + a) false) (L.getD (13 + b) false)) (L.getD (13 + c) false))
      (L.getD (13 + d) false))

def G (L : List Bool) : Bool :=
  orv (orv (orv (orv (orv (orv (orv (pt L 5 5 4 2 9) (pt L 6 6 5 3 10)) (pt L 7 7 6 4 11))
    (pt L 8 8 7 5 12)) (pt L 9 9 8 6 0)) (pt L 10 10 9 7 1)) (pt L 11 11 10 8 2))
    (pt L 12 12 11 9 3)

theorem ofFn26 (x : Fin 26 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25] := by
  rfl

set_option maxHeartbeats 1000000 in
theorem eval_eq (x : Fin 26 → Bool) : circuitFun 26 C x = G (List.ofFn x) := by
  show C.eval (List.ofFn x) = G (List.ofFn x)
  rw [ofFn26]
  simp only [Circuit.eval, Circuit.wires, C, gs, ptGates, List.cons_append, List.nil_append,
    List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.getD_cons_succ,
    List.getD_cons_zero, Nat.reduceAdd, Nat.reduceMul, G, pt, orv, andv]

def E : List (ℕ × ℕ) :=
  [(5,5),(5,4),(5,2),(5,9),(6,6),(6,5),(6,3),(6,10),(7,7),(7,6),(7,4),(7,11),
   (8,8),(8,7),(8,5),(8,12),(9,9),(9,8),(9,6),(9,0),(10,10),(10,9),(10,7),(10,1),
   (11,11),(11,10),(11,8),(11,2),(12,12),(12,11),(12,9),(12,3)]

theorem G_eq (L : List Bool) :
    G L = E.any (fun e => L.getD e.1 false && L.getD (13 + e.2) false) := by
  simp only [G, pt, orv, andv, GateOp.eval, E, List.any_cons, List.any_nil, List.all_cons,
    List.all_nil, id, Bool.or_false, Bool.and_true, Bool.and_or_distrib_left, Bool.or_assoc]

def S : Finset (Fin 13) := {0, 1, 3, 9}

theorem key : ∀ a b : Fin 13, (5 ≤ a.val ∧ ∃ d ∈ S, a = b + d) ↔ (a.val, b.val) ∈ E := by
  decide

theorem bnd : ∀ e ∈ E, e.1 < 13 ∧ e.2 < 13 := by decide

theorem getD_ofFn (x : Fin 26 → Bool) (n : ℕ) (h : n < 26) :
    (List.ofFn x).getD n false = x ⟨n, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h)]
  simp only [Option.getD_some, List.getElem_ofFn]

theorem main (x : Fin 26 → Bool) : circuitFun 26 C x =
    decide (∃ a b : Fin 13, 5 ≤ a.val ∧ (∃ d ∈ S, a = b + d) ∧
      x (Fin.castAdd 13 a) = true ∧ x (Fin.natAdd 13 b) = true) := by
  rw [eval_eq, G_eq]
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨e, he, hf⟩
    obtain ⟨h1, h2⟩ := bnd e he
    have hk := (key ⟨e.1, h1⟩ ⟨e.2, h2⟩).mpr (by simpa using he)
    rw [Bool.and_eq_true, getD_ofFn x _ (by omega), getD_ofFn x _ (by omega)] at hf
    exact ⟨⟨e.1, h1⟩, ⟨e.2, h2⟩, hk.1, hk.2, hf.1, hf.2⟩
  · rintro ⟨a, b, h5, hd, ha, hb⟩
    refine ⟨(a.val, b.val), (key a b).mp ⟨h5, hd⟩, ?_⟩
    rw [Bool.and_eq_true, getD_ofFn x _ (by omega), getD_ofFn x _ (by omega)]
    exact ⟨ha, hb⟩

theorem mono : Monotone2 C := by
  intro g hg
  simp only [C, gs, ptGates, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> simp

theorem reads : NestedCover.ReadsBack 26 C := by
  unfold NestedCover.ReadsBack NestedCover.gateAt
  decide

theorem sz : C.size ≤ 39 := by decide

end PEqualNP.Outside.L_meta_2101

open PEqualNP.Outside.L_meta_2101 in
theorem PEqualNP.Outside.L_meta_2101 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 ∧       x1.size ≤ (39 : ℕ) ∧         have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         let x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 x4 : Fin (13 : ℕ)) => ∃ x5 ∈ x2, x3 = x4 + x5;         ∀ (x4 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 x4 = Decidable.decide (∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (5 : ℕ) ≤ ↑x5 ∧ x3 x5 x6 ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) := by
  exact ⟨C, mono, reads, sz, main⟩
