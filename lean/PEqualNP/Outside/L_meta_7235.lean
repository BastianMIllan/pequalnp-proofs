import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7235

def edges : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]

theorem key : ∀ a b : Fin 14, ∃ p ∈ edges, p.1 < 14 ∧ p.2 < 14 ∧
    p.1 ≠ (a : ℕ) ∧ p.1 ≠ (b : ℕ) ∧ p.2 ≠ (a : ℕ) ∧ p.2 ≠ (b : ℕ) := by
  decide

end PEqualNP.Outside.L_meta_7235

theorem PEqualNP.Outside.L_meta_7235 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∨ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∧ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), x8 x12 ∧ x9 x2 x12 = Bool.true ∧ x9 x3 x12 = Bool.false) → (∃ (x13 : Fin (14 : ℕ) → Bool), x8 x13 ∧ x9 x3 x13 = Bool.true ∧ x9 x2 x13 = Bool.false) → x1.gates = [] → (26 : ℕ) ≤ x1.size := by
  intro x1 x2 x3 _ hx2 hx3 x7 x8 x9 h1 _ _ _ hg
  exfalso
  have hs : x1.size = 0 := by simp [PEqualNP.CircuitLowerBounds.Circuit.size, hg]
  rw [hs] at hx2 hx3
  have hw : ∀ y : List Bool, x1.wires y = y := by
    intro y
    simp [PEqualNP.CircuitLowerBounds.Circuit.wires, hg]
  obtain ⟨p, hp, hp1, hp2, ha1, hb1, ha2, hb2⟩ :=
    PEqualNP.Outside.L_meta_7235.key ⟨x2, by omega⟩ ⟨x3, by omega⟩
  let y : Fin 14 → Bool := fun i => decide ((i : ℕ) ≠ x2 ∧ (i : ℕ) ≠ x3)
  have hy : x8 y := by
    refine ⟨⟨p.1, hp1⟩, ⟨p.2, hp2⟩, ?_, ?_, ?_⟩
    · exact hp
    · simp [y, ha1, hb1]
    · simp [y, ha2, hb2]
  have e2 : x9 x2 y = false := by
    show (x1.wires (List.ofFn y)).getD x2 false = false
    rw [hw, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; omega), List.getElem_ofFn]
    simp [y]
  have e3 : x9 x3 y = false := by
    show (x1.wires (List.ofFn y)).getD x3 false = false
    rw [hw, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; omega), List.getElem_ofFn]
    simp [y]
  rcases h1 y hy with h | h
  · rw [e2] at h; exact Bool.false_ne_true h
  · rw [e3] at h; exact Bool.false_ne_true h
