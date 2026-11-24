import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3247

open PEqualNP.CircuitLowerBounds

-- point p (wire p) is ORed with its three lines (wires 7 + l, p + l = 0, 1, 3 mod 7), then ANDed;
-- the seven ANDs are ORed together. Every gate is read by exactly one later gate.
def C27 : Circuit := ⟨[
  ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [14, 10]⟩, ⟨GateOp.and, [0, 15]⟩,
  ⟨GateOp.or, [13, 7]⟩, ⟨GateOp.or, [17, 9]⟩, ⟨GateOp.and, [1, 18]⟩,
  ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [20, 8]⟩, ⟨GateOp.and, [2, 21]⟩,
  ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [23, 7]⟩, ⟨GateOp.and, [3, 24]⟩,
  ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [26, 13]⟩, ⟨GateOp.and, [4, 27]⟩,
  ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [29, 12]⟩, ⟨GateOp.and, [5, 30]⟩,
  ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [32, 11]⟩, ⟨GateOp.and, [6, 33]⟩,
  ⟨GateOp.or, [16, 19]⟩, ⟨GateOp.or, [35, 22]⟩, ⟨GateOp.or, [36, 25]⟩,
  ⟨GateOp.or, [37, 28]⟩, ⟨GateOp.or, [38, 31]⟩, ⟨GateOp.or, [39, 34]⟩], 40⟩

def dG : Gate := ⟨GateOp.and, []⟩

theorem readOnceB : ((List.range 27).all fun k => (List.range 27).all fun k' =>
    (k == k') || ((C27.gates.getD k dG).inputs.all fun w =>
      decide (w < 14) || !((C27.gates.getD k' dG).inputs.contains w))) = true := by
  decide +kernel

theorem readOnce (k : ℕ) (hk : k < 27) (k' : ℕ) (hk' : k' < 27) (hne : k ≠ k') (w : ℕ) (hw : 14 ≤ w)
    (h1 : w ∈ (C27.gates.getD k dG).inputs) (h2 : w ∈ (C27.gates.getD k' dG).inputs) : False := by
  have H := readOnceB
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at H
  rcases H k hk k' hk' with h | h
  · exact hne h
  · have h3 := h w h1
    have hw2 : ¬ w < 14 := by omega
    simp_all

def A (a b : Bool) : Bool := a && (b && true)

def O (a b : Bool) : Bool := a || (b || false)

def E (y : Fin 14 → Bool) : Bool :=
  O (O (O (O (O (O (A (y 0) (O (O (y 7) (y 8)) (y 10))) (A (y 1) (O (O (y 13) (y 7)) (y 9)))) (A (y 2) (O (O (y 12) (y 13)) (y 8)))) (A (y 3) (O (O (y 11) (y 12)) (y 7)))) (A (y 4) (O (O (y 10) (y 11)) (y 13)))) (A (y 5) (O (O (y 9) (y 10)) (y 12)))) (A (y 6) (O (O (y 8) (y 9)) (y 11)))

set_option maxHeartbeats 1000000 in
theorem evalE (y : Fin 14 → Bool) : C27.eval (List.ofFn y) = E y := by
  simp [C27, Circuit.eval, Circuit.wires, E, A, O, GateOp.eval, List.ofFn_succ]

theorem iffE (y : Fin 14 → Bool) : E y = true ↔ ∃ p l : Fin 7, (p + l = 0 ∨ p + l = 1 ∨ p + l = 3) ∧
    y (Fin.castAdd 7 p) = true ∧ y (Fin.natAdd 7 l) = true := by
  simp only [E, A, O, Bool.and_true, Bool.or_false, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · intro hD
    rcases hD with ((((((⟨hp, (hl | hl) | hl⟩ | ⟨hp, (hl | hl) | hl⟩) | ⟨hp, (hl | hl) | hl⟩) |
      ⟨hp, (hl | hl) | hl⟩) | ⟨hp, (hl | hl) | hl⟩) | ⟨hp, (hl | hl) | hl⟩) | ⟨hp, (hl | hl) | hl⟩)
    · exact ⟨0, 0, by decide, hp, hl⟩
    · exact ⟨0, 1, by decide, hp, hl⟩
    · exact ⟨0, 3, by decide, hp, hl⟩
    · exact ⟨1, 6, by decide, hp, hl⟩
    · exact ⟨1, 0, by decide, hp, hl⟩
    · exact ⟨1, 2, by decide, hp, hl⟩
    · exact ⟨2, 5, by decide, hp, hl⟩
    · exact ⟨2, 6, by decide, hp, hl⟩
    · exact ⟨2, 1, by decide, hp, hl⟩
    · exact ⟨3, 4, by decide, hp, hl⟩
    · exact ⟨3, 5, by decide, hp, hl⟩
    · exact ⟨3, 0, by decide, hp, hl⟩
    · exact ⟨4, 3, by decide, hp, hl⟩
    · exact ⟨4, 4, by decide, hp, hl⟩
    · exact ⟨4, 6, by decide, hp, hl⟩
    · exact ⟨5, 2, by decide, hp, hl⟩
    · exact ⟨5, 3, by decide, hp, hl⟩
    · exact ⟨5, 5, by decide, hp, hl⟩
    · exact ⟨6, 1, by decide, hp, hl⟩
    · exact ⟨6, 2, by decide, hp, hl⟩
    · exact ⟨6, 4, by decide, hp, hl⟩
  · rintro ⟨p, l, h, hp, hl⟩
    fin_cases p <;> fin_cases l <;> simp_all

end PEqualNP.Outside.L_meta_3247

theorem PEqualNP.Outside.L_meta_3247 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size = 27 ∧ (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ u v : ℕ, g.inputs = [u, v] ∧ u ≠ v ∧ u < 14 + k ∧ v < 14 + k) ∧ C.output + 1 = 14 + C.size ∧ (∀ k : ℕ, k + 1 < C.size → ∃ (k' : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k']? = some g ∧ 14 + k ∈ g.inputs) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7, (p + l = 0 ∨ p + l = 1 ∨ p + l = 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧ ¬ (∃ j : ℕ, j < C.size ∧ (∀ i : Fin 14, (C.wires (List.ofFn (fun t : Fin 14 => decide (t = i)))).getD (14 + j) false = false) ∧ (∃ x : Fin 14 → Bool, (C.wires (List.ofFn x)).getD (14 + j) false = true ∧ ¬ ∃ p l : Fin 7, (p + l = 0 ∨ p + l = 1 ∨ p + l = 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧ ∃ (k k' : ℕ) (g g' : PEqualNP.CircuitLowerBounds.Gate), k ≠ k' ∧ C.gates[k]? = some g ∧ C.gates[k']? = some g' ∧ 14 + j ∈ g.inputs ∧ 14 + j ∈ g'.inputs) := by
  refine ⟨PEqualNP.Outside.L_meta_3247.C27, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · intro k g h
    obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp h
    change k < 27 at hk
    interval_cases k <;>
      exact ⟨by first | exact Or.inl rfl | exact Or.inr rfl, _, _, rfl, by decide, by decide, by decide⟩
  · intro k hk
    change k + 1 < 27 at hk
    have hk2 : k < 26 := by omega
    interval_cases k
    · exact ⟨1, _, rfl, by decide⟩
    · exact ⟨2, _, rfl, by decide⟩
    · exact ⟨21, _, rfl, by decide⟩
    · exact ⟨4, _, rfl, by decide⟩
    · exact ⟨5, _, rfl, by decide⟩
    · exact ⟨21, _, rfl, by decide⟩
    · exact ⟨7, _, rfl, by decide⟩
    · exact ⟨8, _, rfl, by decide⟩
    · exact ⟨22, _, rfl, by decide⟩
    · exact ⟨10, _, rfl, by decide⟩
    · exact ⟨11, _, rfl, by decide⟩
    · exact ⟨23, _, rfl, by decide⟩
    · exact ⟨13, _, rfl, by decide⟩
    · exact ⟨14, _, rfl, by decide⟩
    · exact ⟨24, _, rfl, by decide⟩
    · exact ⟨16, _, rfl, by decide⟩
    · exact ⟨17, _, rfl, by decide⟩
    · exact ⟨25, _, rfl, by decide⟩
    · exact ⟨19, _, rfl, by decide⟩
    · exact ⟨20, _, rfl, by decide⟩
    · exact ⟨26, _, rfl, by decide⟩
    · exact ⟨22, _, rfl, by decide⟩
    · exact ⟨23, _, rfl, by decide⟩
    · exact ⟨24, _, rfl, by decide⟩
    · exact ⟨25, _, rfl, by decide⟩
    · exact ⟨26, _, rfl, by decide⟩
  · intro x
    rw [PEqualNP.Outside.L_meta_3247.evalE]
    exact PEqualNP.Outside.L_meta_3247.iffE x
  · rintro ⟨j, -, -, -, k, k', g, g', hne, hk, hk', h1, h2⟩
    have ek : PEqualNP.Outside.L_meta_3247.C27.gates.getD k PEqualNP.Outside.L_meta_3247.dG = g := by
      rw [List.getD_eq_getElem?_getD, hk]; rfl
    have ek' : PEqualNP.Outside.L_meta_3247.C27.gates.getD k' PEqualNP.Outside.L_meta_3247.dG = g' := by
      rw [List.getD_eq_getElem?_getD, hk']; rfl
    have hkl : k < 27 := (List.getElem?_eq_some_iff.mp hk).1
    have hkl' : k' < 27 := (List.getElem?_eq_some_iff.mp hk').1
    exact PEqualNP.Outside.L_meta_3247.readOnce k hkl k' hkl' hne (14 + j) (by omega) (by rw [ek]; exact h1)
      (by rw [ek']; exact h2)
