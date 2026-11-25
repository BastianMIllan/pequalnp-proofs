import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10015

def rs : List (ℕ × ℕ) := [(482382120, 17834336), (100704304, 478486752), (10036224, 270542043), (65877, 707723269), (4196802, 1138295312), (1082156160, 360744083), (2001576, 1343225898), (90708609, 20976168), (3833860, 1610754221), (1107497216, 1275209492), (587275788, 236982280), (158662682, 282706), (673451425, 547881218), (1444029443, 272903168), (570442056, 1246431552), (4196130, 31196230), (268578833, 843112993), (546308676, 45238409), (71565340, 136138801), (423657600, 51680160), (327418112, 69275492), (279071284, 67649700), (541851778, 1075418634), (1242456136, 1476429840), (1880098824, 1081178368), (1117818934, 75669508), (218714246, 553784336)]
def M : List ℕ := [1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736]
def fs (a : ℕ) : Finset (Fin 31) := Finset.univ.filter fun i => a.testBit i.val = true
theorem c1 : ∀ p ∈ rs, ∀ i j : Fin 31, p.1.testBit i.val = true → p.2.testBit j.val = true → (M.getD i.val 0).testBit j.val = false := by decide +kernel
theorem c2 : ∀ i j : Fin 31, (M.getD i.val 0).testBit j.val = false → ∃ p ∈ rs, p.1.testBit i.val = true ∧ p.2.testBit j.val = true := by decide +kernel

end PEqualNP.Outside.L_meta_10015

theorem PEqualNP.Outside.L_meta_10015 : ∃ L : List (Finset (Fin 31) × Finset (Fin 31)), L.length ≤ 27 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 31) (j : Fin 31), (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨PEqualNP.Outside.L_meta_10015.rs.map fun p => (PEqualNP.Outside.L_meta_10015.fs p.1, PEqualNP.Outside.L_meta_10015.fs p.2), by decide, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    exact PEqualNP.Outside.L_meta_10015.c1 p hp i j (by simpa [PEqualNP.Outside.L_meta_10015.fs] using hi) (by simpa [PEqualNP.Outside.L_meta_10015.fs] using hj)
  · intro i j h
    obtain ⟨p, hp, h1, h2⟩ := PEqualNP.Outside.L_meta_10015.c2 i j h
    exact ⟨_, List.mem_map.2 ⟨p, hp, rfl⟩, by simpa [PEqualNP.Outside.L_meta_10015.fs] using h1, by simpa [PEqualNP.Outside.L_meta_10015.fs] using h2⟩
