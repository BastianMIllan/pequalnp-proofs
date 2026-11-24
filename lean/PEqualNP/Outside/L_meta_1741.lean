import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1741
open PEqualNP.CircuitLowerBounds

def C0 : Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [46, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 48] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [51, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [54, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [55, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 56] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [58, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [63, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [66, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 68] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [70, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 72] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [75, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [78, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [79, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [80, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [81, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [82, 53] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 57] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [84, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [85, 65] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 69] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [87, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [88, 77] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [91, 90] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 92] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 93] }], output := 94 }

def F (f g : Fin 13 → Bool) : Bool := ((((((((((((((g 0 && (((f 0 || f 1) || f 3) || f 9)) || (g 1 && (((f 1 || f 2) || f 4) || f 10))) || (g 2 && (((f 2 || f 3) || f 5) || f 11))) || (g 3 && (((f 3 || f 4) || f 6) || f 12))) || (g 4 && (((f 0 || f 4) || f 5) || f 7))) || (g 5 && (((f 1 || f 5) || f 6) || f 8))) || (g 6 && (((f 2 || f 6) || f 7) || f 9))) || (g 7 && (((f 3 || f 7) || f 8) || f 10))) || (g 8 && (((f 4 || f 8) || f 9) || f 11))) || (g 9 && (((f 5 || f 9) || f 10) || f 12))) || (g 10 && (((f 0 || f 6) || f 10) || f 11))) || (g 11 && (((f 1 || f 7) || f 11) || f 12))) || (g 12 && (((f 0 || f 2) || f 8) || f 12))) || (f 0 && ((g 0 || g 4) || (g 10 && g 12))))

def inc (u l : Fin 13) : Bool := (u - l == 0 || u - l == 1 || u - l == 3 || u - l == 9)

theorem inc_spec : ∀ u l : Fin 13, (u - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))) ↔ inc u l = true := by decide

theorem ofFn13 (f : Fin 13 → Bool) : List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12] := by
  first
    | rfl
    | (simp [List.ofFn_succ]; rfl)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem evalF (f g : Fin 13 → Bool) : C0.eval (List.ofFn f ++ List.ofFn g) = F f g := by
  rw [ofFn13 f, ofFn13 g]
  first
    | (simp only [C0, F, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id, Bool.and_true, Bool.or_false]; done)
    | (simp only [C0, F, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id, Bool.and_true, Bool.or_false]; rfl)
    | (simp [C0, F, Circuit.eval, Circuit.wires, GateOp.eval]; done)
    | rfl

set_option maxRecDepth 100000 in
theorem key : ∀ a b c : Fin 13, F (fun u : Fin 13 => !(inc u a) && !(inc u b) && !(inc u c)) (fun v : Fin 13 => (v == a || v == b || v == c)) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pairsF : ∀ p l : Fin 13, inc p l = true →
     F (fun u : Fin 13 => decide (u = p)) (fun v : Fin 13 => decide (v = l)) = true := by
  decide +kernel

theorem pairs (p l : Fin 13) (h : p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))) :
     C0.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l))) = true :=
  (evalF _ _).trans (pairsF p l ((inc_spec p l).mp h))

set_option maxRecDepth 100000 in
theorem empF : F (fun u1 : Fin 13 => decide (∀ l ∈ (∅ : Finset (Fin 13)), u1 - l ∉ ({0, 1, 3, 9} : Finset (Fin 13))))
             (fun v1 : Fin 13 => decide (v1 ∈ (∅ : Finset (Fin 13)))) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem w92 : (∀ l : Fin 13, (C0.wires (List.replicate 13 false ++ List.ofFn (fun v2 : Fin 13 => decide (v2 = l)))).getD 92 false
       = decide (l = 0 ∨ l = 4)) ∧
  (C0.wires (List.replicate 13 false ++ List.ofFn (fun v3 : Fin 13 => decide (v3 = 10 ∨ v3 = 12)))).getD 92 false = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem shape1 : PEqualNP.MetaComplexity.NestedCover.ReadsBack (13 + 13) C0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem shape2 : ∀ g ∈ C0.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2 := by
  first
    | (simp [C0]; done)
    | decide +kernel

theorem three (Y : Finset (Fin 13)) (hY : Y.card ≤ 3) : Y = ∅ ∨ ∃ a b c : Fin 13, Y = {a, b, c} := by
  have h3 : Y.card = 0 ∨ Y.card = 1 ∨ Y.card = 2 ∨ Y.card = 3 := by omega
  rcases h3 with h | h | h | h
  · left; exact Finset.card_eq_zero.mp h
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact Or.inr ⟨a, a, a, by first | (simp; done) | (ext x; simp; done)⟩
  · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp h
    exact Or.inr ⟨a, a, b, by first | (simp; done) | (ext x; simp; done)⟩
  · obtain ⟨a, b, c, -, -, -, rfl⟩ := Finset.card_eq_three.mp h
    exact Or.inr ⟨a, b, c, rfl⟩

theorem small (Y : Finset (Fin 13)) (hY : Y.card ≤ 3) :
     C0.eval (List.ofFn (fun u1 : Fin 13 => decide (∀ l ∈ Y, u1 - l ∉ ({0, 1, 3, 9} : Finset (Fin 13))))
             ++ List.ofFn (fun v1 : Fin 13 => decide (v1 ∈ Y))) = false := by
  rcases three Y hY with rfl | ⟨a, b, c, rfl⟩
  · exact (evalF _ _).trans empF
  · have e1 : (fun u1 : Fin 13 => decide (∀ l ∈ ({a, b, c} : Finset (Fin 13)), u1 - l ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) = (fun u : Fin 13 => !(inc u a) && !(inc u b) && !(inc u c)) := by
      funext u
      have ha := inc_spec u a
      have hb := inc_spec u b
      have hc := inc_spec u c
      rw [Bool.eq_iff_iff]
      first
        | (simp only [inc_spec]; simp [and_assoc]; done)
        | (cases hA : inc u a <;> cases hB : inc u b <;> cases hC : inc u c <;> simp_all; done)
    have e2 : (fun v1 : Fin 13 => decide (v1 ∈ ({a, b, c} : Finset (Fin 13)))) = (fun v : Fin 13 => (v == a || v == b || v == c)) := by
      funext v
      rw [Bool.eq_iff_iff]
      first
        | (simp [or_assoc]; done)
        | (by_cases h1 : v = a <;> by_cases h2 : v = b <;> by_cases h3 : v = c <;> simp [h1, h2, h3]; done)
    rw [e1, e2]
    exact (evalF _ _).trans (key a b c)

end PEqualNP.Outside.L_meta_1741

theorem PEqualNP.Outside.L_meta_1741 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [46, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 48] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [51, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [54, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [55, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 56] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [58, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [63, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [66, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 68] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [70, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 72] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [75, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [78, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [79, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [80, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [81, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [82, 53] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 57] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [84, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [85, 65] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 69] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [87, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [88, 77] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [91, 90] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 92] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 93] }], output := 94 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 69 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (13 + 13) C ∧
  (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
     C.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l))) = true) ∧
  (∀ Y : Finset (Fin 13), Y.card ≤ 3 →
     C.eval (List.ofFn (fun u1 : Fin 13 => decide (∀ l ∈ Y, u1 - l ∉ ({0, 1, 3, 9} : Finset (Fin 13))))
             ++ List.ofFn (fun v1 : Fin 13 => decide (v1 ∈ Y))) = false) ∧
  (∀ l : Fin 13, (C.wires (List.replicate 13 false ++ List.ofFn (fun v2 : Fin 13 => decide (v2 = l)))).getD 92 false
       = decide (l = 0 ∨ l = 4)) ∧
  (C.wires (List.replicate 13 false ++ List.ofFn (fun v3 : Fin 13 => decide (v3 = 10 ∨ v3 = 12)))).getD 92 false = true := by
  intro C hC
  have hC' : C = PEqualNP.Outside.L_meta_1741.C0 := hC
  rw [hC']
  exact ⟨rfl, PEqualNP.Outside.L_meta_1741.shape1, PEqualNP.Outside.L_meta_1741.shape2, PEqualNP.Outside.L_meta_1741.pairs, PEqualNP.Outside.L_meta_1741.small, PEqualNP.Outside.L_meta_1741.w92.1, PEqualNP.Outside.L_meta_1741.w92.2⟩
