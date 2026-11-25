import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10017

def rs : List (ℕ × ℕ) := [(731038543, 33687552), (1718640275, 12587008), (2074417601, 2097920), (577679598, 1073774600), (1418324203, 285278208), (916801338, 67633216), (1850422565, 134226944), (71267796, 536870929), (158770105, 262178), (1373277812, 1048708), (1240950810, 16402), (402653188, 1664941216), (12800, 1608533609), (83918848, 756489192), (34668544, 1378301404), (3080, 527972634), (537395216, 679195331), (4194624, 1272775509), (278529, 948559143), (8519808, 370837435), (1075871744, 1166457735), (38, 1704977420), (393898672, 4194464), (1960186460, 1064961), (134218768, 985444562), (16781344, 762496364), (943647046, 1610614784), (8388611, 327937550)]
def M : List ℕ := [1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736]
def fs (a : ℕ) : Finset (Fin 31) := Finset.univ.filter fun i => a.testBit i.val = true
theorem c1 : ∀ p ∈ rs, ∀ i j : Fin 31, p.1.testBit i.val = true → p.2.testBit j.val = true → (M.getD i.val 0).testBit j.val = false := by decide +kernel
theorem c2 : ∀ i j : Fin 31, (M.getD i.val 0).testBit j.val = false → ∃ p ∈ rs, p.1.testBit i.val = true ∧ p.2.testBit j.val = true := by decide +kernel

end PEqualNP.Outside.L_meta_10017

theorem PEqualNP.Outside.L_meta_10017 : ∃ L : List (Finset (Fin 31) × Finset (Fin 31)), L.length ≤ 28 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 31) (j : Fin 31), (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨PEqualNP.Outside.L_meta_10017.rs.map fun p => (PEqualNP.Outside.L_meta_10017.fs p.1, PEqualNP.Outside.L_meta_10017.fs p.2), by decide, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    exact PEqualNP.Outside.L_meta_10017.c1 p hp i j (by simpa [PEqualNP.Outside.L_meta_10017.fs] using hi) (by simpa [PEqualNP.Outside.L_meta_10017.fs] using hj)
  · intro i j h
    obtain ⟨p, hp, h1, h2⟩ := PEqualNP.Outside.L_meta_10017.c2 i j h
    exact ⟨_, List.mem_map.2 ⟨p, hp, rfl⟩, by simpa [PEqualNP.Outside.L_meta_10017.fs] using h1, by simpa [PEqualNP.Outside.L_meta_10017.fs] using h2⟩
