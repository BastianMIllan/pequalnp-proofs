import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1701
open PEqualNP.CircuitLowerBounds

def C0 : Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 48] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 54] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 57] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 63] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [65, 66] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 69] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 72] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 75] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 78] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [80, 81] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 84] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 87] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 90] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 93] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [101, 102] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [104, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [105, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [106, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [107, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [109, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [111, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [112, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [114, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [115, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [116, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [117, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [119, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [120, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [121, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [122, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [124, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [125, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [126, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [127, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [129, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [130, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [131, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [132, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [134, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [135, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [136, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [137, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [139, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [140, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [141, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [142, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [144, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [146, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [147, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [149, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [150, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [151, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [152, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [154, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [156, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [157, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [159, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [160, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [161, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [162, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [164, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [166, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [167, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [169, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [170, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [171, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [172, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [174, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [176, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [177, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [179, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [180, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [181, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [182, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [184, 185] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 186] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [188, 189] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 190] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [192, 193] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [196, 197] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 198] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [200, 201] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 202] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [204, 205] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 206] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [208, 209] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 210] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [212, 213] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [216, 217] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [220, 221] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 222] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [224, 225] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 226] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [228, 229] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 230] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [232, 233] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 234] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [236, 237] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 238] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [240, 241] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 242] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [244, 245] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 246] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [187, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [195, 199] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [203, 207] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [211, 215] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [219, 223] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [227, 231] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [235, 239] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [243, 247] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [248, 249] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [250, 251] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [252, 253] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [254, 255] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [256, 257] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [258, 259] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [260, 261] }], output := 262 }

def inc : List (ℕ × ℕ) := [(0, 0), (4, 0), (8, 0), (12, 0), (1, 1), (5, 1), (9, 1), (13, 1), (2, 2), (6, 2), (10, 2), (14, 2), (3, 3), (7, 3), (11, 3), (15, 3), (0, 4), (5, 4), (10, 4), (15, 4), (1, 5), (4, 5), (11, 5), (14, 5), (2, 6), (7, 6), (8, 6), (13, 6), (3, 7), (6, 7), (9, 7), (12, 7), (0, 8), (6, 8), (11, 8), (13, 8), (1, 9), (7, 9), (10, 9), (12, 9), (2, 10), (4, 10), (9, 10), (15, 10), (3, 11), (5, 11), (8, 11), (14, 11), (0, 12), (7, 12), (9, 12), (14, 12), (1, 13), (6, 13), (8, 13), (15, 13), (2, 14), (5, 14), (11, 14), (12, 14), (3, 15), (4, 15), (10, 15), (13, 15)]

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

def isAO : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

theorem c0_ops : ∀ g ∈ C0.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  have h : C0.gates.all (fun g => isAO g.op) = true := by decide +kernel
  intro g hg
  have h2 := List.all_eq_true.mp h g hg
  revert h2
  cases g.op <;> simp [isAO]

theorem eval_mono (a b : List Bool) (h : le a b) (ha : C0.eval a = true) : C0.eval b = true :=
  (wires_mono C0.gates c0_ops a b h).2 C0.output ha

theorem le_ofFn (f f' g g' : Fin 16 → Bool) (hf : ∀ i, f i = true → f' i = true)
    (hg : ∀ i, g i = true → g' i = true) :
    le (List.ofFn f ++ List.ofFn g) (List.ofFn f' ++ List.ofFn g') := by
  refine ⟨by simp, ?_⟩
  intro i hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn] at hi ⊢
  split_ifs at hi ⊢ with h1 h2
  · simp only [Option.getD_some] at hi ⊢
    exact hf _ hi
  · simp only [Option.getD_some] at hi ⊢
    exact hg _ hi
  · simp at hi

def inv (W : ℕ) (a : List Bool) : Prop := ∀ i : ℕ, W.testBit i = a.getD i false

def enc : List Bool → ℕ
  | [] => 0
  | b :: a => 2 * enc a + (bif b then 1 else 0)

theorem enc_inv : ∀ a : List Bool, inv (enc a) a := by
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

theorem step_inv (W : ℕ) (a : List Bool) (v : Bool) (h : inv W a) :
    inv (bif v then W ||| 2 ^ a.length else W) (a ++ [v]) := by
  intro i
  rw [key]
  cases v
  · simp only [cond_false]
    split_ifs with h1 h2
    · exact h i
    · rw [h i, List.getD_eq_default _ _ (by omega)]
    · rw [h i, List.getD_eq_default _ _ (by omega)]
  · simp only [cond_true]
    rw [Nat.testBit_or, Nat.testBit_two_pow, h i]
    split_ifs with h1 h2
    · simp [show ¬ a.length = i by omega]
    · simp [h2]
    · rw [List.getD_eq_default _ _ (by omega)]
      simp [show ¬ a.length = i by omega]

def run : List Gate → ℕ → ℕ → ℕ
  | [], _, W => W
  | g :: gs, n, W => bif g.op.eval (g.inputs.map (fun i => W.testBit i))
      then run gs (n + 1) (W ||| 2 ^ n) else run gs (n + 1) W

theorem cond_run (V : Bool) (gs : List Gate) (n W : ℕ) :
    (bif V then run gs (n + 1) (W ||| 2 ^ n) else run gs (n + 1) W) =
      run gs (n + 1) (bif V then W ||| 2 ^ n else W) := by
  cases V <;> rfl

theorem run_spec : ∀ (gs : List Gate) (a : List Bool) (W : ℕ), inv W a →
    inv (run gs a.length W)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a) := by
  intro gs
  induction gs with
  | nil => intro a W h; exact h
  | cons g gs ih =>
    intro a W h
    have hm : g.inputs.map (fun i => W.testBit i) = g.inputs.map (fun i => a.getD i false) := by
      apply List.map_congr_left
      intro i _
      exact h i
    simp only [run, List.foldl_cons]
    rw [hm, cond_run]
    have hlen : (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]).length = a.length + 1 := by
      simp
    rw [← hlen]
    exact ih _ _ (step_inv W a _ h)

def ev (x : List Bool) : Bool := (run C0.gates x.length (enc x)).testBit C0.output

theorem ev_eq (x : List Bool) : ev x = C0.eval x := by
  unfold ev Circuit.eval Circuit.wires
  exact run_spec C0.gates x (enc x) (enc_inv x) C0.output

theorem neg0' : ev (List.ofFn (fun _ : Fin 16 => false) ++
    List.ofFn (fun _ : Fin 16 => true)) = false := by
  decide +kernel

theorem neg0 : C0.eval (List.ofFn (fun _ : Fin 16 => false) ++
    List.ofFn (fun _ : Fin 16 => true)) = false := by
  rw [← ev_eq]; exact neg0'

theorem pos_0 : ∀ l : Fin 16, ((((0 : Fin 16)) : ℕ), (l : ℕ)) ∈ inc →
    ev (List.ofFn (fun u : Fin 16 => decide (u = (0 : Fin 16))) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  decide +kernel

theorem neg2_0 : ∀ b : Fin 16,
    ev (List.ofFn (fun u : Fin 16 => decide (u = (0 : Fin 16) ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((((0 : Fin 16)) : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  decide +kernel

theorem pos_1 : ∀ l : Fin 16, ((((1 : Fin 16)) : ℕ), (l : ℕ)) ∈ inc →
    ev (List.ofFn (fun u : Fin 16 => decide (u = (1 : Fin 16))) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  decide +kernel

theorem neg2_1 : ∀ b : Fin 16,
    ev (List.ofFn (fun u : Fin 16 => decide (u = (1 : Fin 16) ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((((1 : Fin 16)) : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  decide +kernel

theorem pos_2 : ∀ l : Fin 16, ((((2 : Fin 16)) : ℕ), (l : ℕ)) ∈ inc →
    ev (List.ofFn (fun u : Fin 16 => decide (u = (2 : Fin 16))) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  decide +kernel

theorem neg2_2 : ∀ b : Fin 16,
    ev (List.ofFn (fun u : Fin 16 => decide (u = (2 : Fin 16) ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((((2 : Fin 16)) : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  decide +kernel

theorem pos_3 : ∀ l : Fin 16, ((((3 : Fin 16)) : ℕ), (l : ℕ)) ∈ inc →
    ev (List.ofFn (fun u : Fin 16 => decide (u = (3 : Fin 16))) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  decide +kernel

theorem neg2_3 : ∀ b : Fin 16,
    ev (List.ofFn (fun u : Fin 16 => decide (u = (3 : Fin 16) ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((((3 : Fin 16)) : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  decide +kernel

theorem pos_4 : ∀ l : Fin 16, ((((4 : Fin 16)) : ℕ), (l : ℕ)) ∈ inc →
    ev (List.ofFn (fun u : Fin 16 => decide (u = (4 : Fin 16))) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  decide +kernel

theorem neg2_4 : ∀ b : Fin 16,
    ev (List.ofFn (fun u : Fin 16 => decide (u = (4 : Fin 16) ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((((4 : Fin 16)) : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  decide +kernel

theorem pos_5 : ∀ l : Fin 16, ((((5 : Fin 16)) : ℕ), (l : ℕ)) ∈ inc →
    ev (List.ofFn (fun u : Fin 16 => decide (u = (5 : Fin 16))) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  decide +kernel

theorem neg2_5 : ∀ b : Fin 16,
    ev (List.ofFn (fun u : Fin 16 => decide (u = (5 : Fin 16) ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((((5 : Fin 16)) : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  decide +kernel

theorem pos_6 : ∀ l : Fin 16, ((((6 : Fin 16)) : ℕ), (l : ℕ)) ∈ inc →
    ev (List.ofFn (fun u : Fin 16 => decide (u = (6 : Fin 16))) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  decide +kernel

theorem neg2_6 : ∀ b : Fin 16,
    ev (List.ofFn (fun u : Fin 16 => decide (u = (6 : Fin 16) ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((((6 : Fin 16)) : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  decide +kernel

theorem pos_7 : ∀ l : Fin 16, ((((7 : Fin 16)) : ℕ), (l : ℕ)) ∈ inc →
    ev (List.ofFn (fun u : Fin 16 => decide (u = (7 : Fin 16))) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  decide +kernel

theorem neg2_7 : ∀ b : Fin 16,
    ev (List.ofFn (fun u : Fin 16 => decide (u = (7 : Fin 16) ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((((7 : Fin 16)) : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  decide +kernel

theorem pos_8 : ∀ l : Fin 16, ((((8 : Fin 16)) : ℕ), (l : ℕ)) ∈ inc →
    ev (List.ofFn (fun u : Fin 16 => decide (u = (8 : Fin 16))) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  decide +kernel

theorem neg2_8 : ∀ b : Fin 16,
    ev (List.ofFn (fun u : Fin 16 => decide (u = (8 : Fin 16) ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((((8 : Fin 16)) : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  decide +kernel

theorem pos_9 : ∀ l : Fin 16, ((((9 : Fin 16)) : ℕ), (l : ℕ)) ∈ inc →
    ev (List.ofFn (fun u : Fin 16 => decide (u = (9 : Fin 16))) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  decide +kernel

theorem neg2_9 : ∀ b : Fin 16,
    ev (List.ofFn (fun u : Fin 16 => decide (u = (9 : Fin 16) ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((((9 : Fin 16)) : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  decide +kernel

theorem pos_10 : ∀ l : Fin 16, ((((10 : Fin 16)) : ℕ), (l : ℕ)) ∈ inc →
    ev (List.ofFn (fun u : Fin 16 => decide (u = (10 : Fin 16))) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  decide +kernel

theorem neg2_10 : ∀ b : Fin 16,
    ev (List.ofFn (fun u : Fin 16 => decide (u = (10 : Fin 16) ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((((10 : Fin 16)) : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  decide +kernel

theorem pos_11 : ∀ l : Fin 16, ((((11 : Fin 16)) : ℕ), (l : ℕ)) ∈ inc →
    ev (List.ofFn (fun u : Fin 16 => decide (u = (11 : Fin 16))) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  decide +kernel

theorem neg2_11 : ∀ b : Fin 16,
    ev (List.ofFn (fun u : Fin 16 => decide (u = (11 : Fin 16) ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((((11 : Fin 16)) : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  decide +kernel

theorem pos_12 : ∀ l : Fin 16, ((((12 : Fin 16)) : ℕ), (l : ℕ)) ∈ inc →
    ev (List.ofFn (fun u : Fin 16 => decide (u = (12 : Fin 16))) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  decide +kernel

theorem neg2_12 : ∀ b : Fin 16,
    ev (List.ofFn (fun u : Fin 16 => decide (u = (12 : Fin 16) ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((((12 : Fin 16)) : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  decide +kernel

theorem pos_13 : ∀ l : Fin 16, ((((13 : Fin 16)) : ℕ), (l : ℕ)) ∈ inc →
    ev (List.ofFn (fun u : Fin 16 => decide (u = (13 : Fin 16))) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  decide +kernel

theorem neg2_13 : ∀ b : Fin 16,
    ev (List.ofFn (fun u : Fin 16 => decide (u = (13 : Fin 16) ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((((13 : Fin 16)) : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  decide +kernel

theorem pos_14 : ∀ l : Fin 16, ((((14 : Fin 16)) : ℕ), (l : ℕ)) ∈ inc →
    ev (List.ofFn (fun u : Fin 16 => decide (u = (14 : Fin 16))) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  decide +kernel

theorem neg2_14 : ∀ b : Fin 16,
    ev (List.ofFn (fun u : Fin 16 => decide (u = (14 : Fin 16) ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((((14 : Fin 16)) : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  decide +kernel

theorem pos_15 : ∀ l : Fin 16, ((((15 : Fin 16)) : ℕ), (l : ℕ)) ∈ inc →
    ev (List.ofFn (fun u : Fin 16 => decide (u = (15 : Fin 16))) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  decide +kernel

theorem neg2_15 : ∀ b : Fin 16,
    ev (List.ofFn (fun u : Fin 16 => decide (u = (15 : Fin 16) ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((((15 : Fin 16)) : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  decide +kernel

theorem pos_ok' : ∀ p l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ inc →
    ev (List.ofFn (fun u : Fin 16 => decide (u = p)) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  intro p
  fin_cases p
  · exact pos_0
  · exact pos_1
  · exact pos_2
  · exact pos_3
  · exact pos_4
  · exact pos_5
  · exact pos_6
  · exact pos_7
  · exact pos_8
  · exact pos_9
  · exact pos_10
  · exact pos_11
  · exact pos_12
  · exact pos_13
  · exact pos_14
  · exact pos_15

theorem pos_ok (p l : Fin 16) (h : ((p : ℕ), (l : ℕ)) ∈ inc) :
    C0.eval (List.ofFn (fun u : Fin 16 => decide (u = p)) ++
      List.ofFn (fun v : Fin 16 => decide (v = l))) = true := by
  rw [← ev_eq]; exact pos_ok' p l h

theorem neg2' : ∀ a b : Fin 16,
    ev (List.ofFn (fun u : Fin 16 => decide (u = a ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((a : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  intro a
  fin_cases a
  · exact neg2_0
  · exact neg2_1
  · exact neg2_2
  · exact neg2_3
  · exact neg2_4
  · exact neg2_5
  · exact neg2_6
  · exact neg2_7
  · exact neg2_8
  · exact neg2_9
  · exact neg2_10
  · exact neg2_11
  · exact neg2_12
  · exact neg2_13
  · exact neg2_14
  · exact neg2_15

theorem neg2 (a b : Fin 16) :
    C0.eval (List.ofFn (fun u : Fin 16 => decide (u = a ∨ u = b)) ++
      List.ofFn (fun v : Fin 16 => decide (((a : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc)))
      = false := by
  rw [← ev_eq]; exact neg2' a b

theorem supp (x : Fin 16 → Bool)
    (hx : (Finset.univ.filter (fun p : Fin 16 => x p = true)).card ≤ 2) :
    (∀ p, x p = false) ∨ ∃ a b : Fin 16, ∀ p, x p = true ↔ (p = a ∨ p = b) := by
  have h3 : (Finset.univ.filter (fun p : Fin 16 => x p = true)).card = 0 ∨
      (Finset.univ.filter (fun p : Fin 16 => x p = true)).card = 1 ∨
      (Finset.univ.filter (fun p : Fin 16 => x p = true)).card = 2 := by omega
  rcases h3 with h0 | h1 | h2
  · left
    intro p
    have hs := Finset.card_eq_zero.mp h0
    have hp : p ∉ Finset.univ.filter (fun p : Fin 16 => x p = true) := by rw [hs]; simp
    simpa using hp
  · right
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    refine ⟨a, a, fun p => ?_⟩
    have hp : p ∈ Finset.univ.filter (fun p : Fin 16 => x p = true) ↔ p ∈ ({a} : Finset (Fin 16)) := by
      rw [ha]
    simpa using hp
  · right
    obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp h2
    refine ⟨a, b, fun p => ?_⟩
    have hp : p ∈ Finset.univ.filter (fun p : Fin 16 => x p = true) ↔ p ∈ ({a, b} : Finset (Fin 16)) := by
      rw [hs]
    simpa using hp

theorem main (x y : Fin 16 → Bool)
    (hx : (Finset.univ.filter (fun p : Fin 16 => x p = true)).card ≤ 2) :
    C0.eval (List.ofFn x ++ List.ofFn y) =
      decide (∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ inc ∧ x p = true ∧ y l = true) := by
  by_cases h : ∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ inc ∧ x p = true ∧ y l = true
  · rw [decide_eq_true h]
    obtain ⟨p, l, hpl, hp, hl⟩ := h
    refine eval_mono _ _ (le_ofFn _ _ _ _ ?_ ?_) (pos_ok p l hpl)
    · intro i hi
      have : i = p := by simpa using hi
      rw [this]; exact hp
    · intro i hi
      have : i = l := by simpa using hi
      rw [this]; exact hl
  · rw [decide_eq_false h]
    by_contra hne
    have ht : C0.eval (List.ofFn x ++ List.ofFn y) = true := by simpa using hne
    rcases supp x hx with h0 | ⟨a, b, hab⟩
    · have h2 := eval_mono _ _ (le_ofFn x (fun _ : Fin 16 => false) y (fun _ : Fin 16 => true)
        (fun i hi => by rw [h0 i] at hi; exact hi) (fun i _ => rfl)) ht
      rw [neg0] at h2
      exact Bool.false_ne_true h2
    · have h2 := eval_mono _ _ (le_ofFn x (fun u : Fin 16 => decide (u = a ∨ u = b)) y
        (fun v : Fin 16 => decide (((a : ℕ), (v : ℕ)) ∉ inc ∧ ((b : ℕ), (v : ℕ)) ∉ inc))
        (fun i hi => by simpa using (hab i).mp hi)
        (fun i hi => by
          have ha : x a = true := (hab a).mpr (Or.inl rfl)
          have hb : x b = true := (hab b).mpr (Or.inr rfl)
          have h1 : ((a : ℕ), (i : ℕ)) ∉ inc := fun hc => h ⟨a, i, hc, ha, hi⟩
          have h2 : ((b : ℕ), (i : ℕ)) ∉ inc := fun hc => h ⟨b, i, hc, hb, hi⟩
          exact decide_eq_true ⟨h1, h2⟩)) ht
      rw [neg2 a b] at h2
      exact Bool.false_ne_true h2

theorem rb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 + 16) C0 := by
  decide +kernel

end PEqualNP.Outside.L_meta_1701

theorem PEqualNP.Outside.L_meta_1701 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 48] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 54] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 57] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 63] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [65, 66] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 69] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 72] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 75] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 78] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [80, 81] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 84] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 87] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 90] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 93] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [101, 102] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [104, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [105, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [106, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [107, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [109, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [111, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [112, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [114, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [115, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [116, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [117, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [119, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [120, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [121, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [122, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [124, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [125, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [126, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [127, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [129, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [130, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [131, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [132, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [134, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [135, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [136, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [137, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [139, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [140, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [141, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [142, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [144, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [146, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [147, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [149, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [150, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [151, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [152, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [154, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [156, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [157, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [159, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [160, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [161, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [162, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [164, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [166, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [167, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [169, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [170, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [171, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [172, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [174, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [176, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [177, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [179, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [180, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [181, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [182, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [184, 185] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 186] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [188, 189] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 190] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [192, 193] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [196, 197] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 198] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [200, 201] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 202] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [204, 205] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 206] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [208, 209] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 210] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [212, 213] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [216, 217] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [220, 221] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 222] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [224, 225] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 226] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [228, 229] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 230] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [232, 233] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 234] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [236, 237] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 238] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [240, 241] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 242] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [244, 245] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 246] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [187, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [195, 199] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [203, 207] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [211, 215] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [219, 223] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [227, 231] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [235, 239] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [243, 247] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [248, 249] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [250, 251] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [252, 253] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [254, 255] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [256, 257] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [258, 259] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [260, 261] }], output := 262 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 231 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 + 16) C ∧ ∀ (x y : Fin 16 → Bool), (Finset.univ.filter (fun p : Fin 16 => x p = true)).card ≤ 2 →
    C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (4, 0), (8, 0), (12, 0), (1, 1), (5, 1), (9, 1), (13, 1), (2, 2), (6, 2), (10, 2), (14, 2), (3, 3), (7, 3), (11, 3), (15, 3), (0, 4), (5, 4), (10, 4), (15, 4), (1, 5), (4, 5), (11, 5), (14, 5), (2, 6), (7, 6), (8, 6), (13, 6), (3, 7), (6, 7), (9, 7), (12, 7), (0, 8), (6, 8), (11, 8), (13, 8), (1, 9), (7, 9), (10, 9), (12, 9), (2, 10), (4, 10), (9, 10), (15, 10), (3, 11), (5, 11), (8, 11), (14, 11), (0, 12), (7, 12), (9, 12), (14, 12), (1, 13), (6, 13), (8, 13), (15, 13), (2, 14), (5, 14), (11, 14), (12, 14), (3, 15), (4, 15), (10, 15), (13, 15)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) := by
  intro C hC
  have hC' : C = PEqualNP.Outside.L_meta_1701.C0 := hC
  rw [hC']
  exact ⟨rfl, PEqualNP.Outside.L_meta_1701.rb, PEqualNP.Outside.L_meta_1701.main⟩
