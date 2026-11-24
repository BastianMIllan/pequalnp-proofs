import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3753

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

def G : List (Bool × ℕ × ℕ) := [(false, 0, 3), (true, 14, 7), (false, 7, 10), (true, 0, 16), (true, 15, 17), (false, 7, 8), (true, 14, 19), (true, 18, 20), (true, 15, 17), (false, 3, 5), (true, 23, 8), (true, 22, 24), (false, 21, 25), (true, 15, 17), (false, 3, 6), (true, 28, 8), (true, 27, 29), (false, 26, 30), (true, 15, 20), (true, 32, 24), (false, 31, 33), (true, 15, 20), (true, 35, 29), (false, 34, 36), (true, 15, 24), (true, 38, 29), (false, 37, 39), (true, 17, 20), (true, 41, 24), (false, 40, 42), (true, 17, 20), (true, 44, 29), (false, 43, 45), (true, 17, 24), (true, 47, 29), (false, 46, 48), (true, 20, 24), (true, 50, 29), (false, 49, 51), (false, 1, 2), (true, 53, 7), (false, 52, 54), (false, 0, 4), (true, 56, 8), (false, 55, 57), (false, 0, 5), (false, 59, 6), (true, 60, 9), (false, 58, 61), (false, 1, 3), (false, 63, 5), (true, 64, 10), (false, 62, 65), (false, 1, 4), (false, 67, 6), (true, 68, 11), (false, 66, 69), (false, 2, 3), (false, 71, 6), (true, 72, 12), (false, 70, 73), (false, 2, 4), (false, 75, 5), (true, 76, 13), (false, 74, 77)]

def L : List (Fin 14 × Fin 14) := [(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)]

def toGate (g : Bool × ℕ × ℕ) : Gate := ⟨cond g.1 GateOp.and GateOp.or, [g.2.1, g.2.2]⟩

def C0 : Circuit := ⟨G.map toGate, 78⟩
def stpG (fa fo : ℕ → ℕ → ℕ) (w : List ℕ) (g : Bool × ℕ × ℕ) : List ℕ :=
  w ++ [cond g.1 (fa (w.getD g.2.1 0) (w.getD g.2.2 0)) (fo (w.getD g.2.1 0) (w.getD g.2.2 0))]

def rd (n : ℕ) (r : List ℕ) (a : ℕ) : ℕ := if a < n then r.getD (n - 1 - a) 0 else 0

def evR (fa fo : ℕ → ℕ → ℕ) : List (Bool × ℕ × ℕ) → ℕ → List ℕ → List ℕ
  | [], _, r => r
  | g :: gs, n, r =>
    evR fa fo gs (n + 1)
      (cond g.1 (fa (rd n r g.2.1) (rd n r g.2.2)) (fo (rd n r g.2.1) (rd n r g.2.2)) :: r)

theorem rd_eq (w : List ℕ) (a : ℕ) : rd w.length w.reverse a = w.getD a 0 := by
  unfold rd
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_reverse (by omega)]
    congr 2
    omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem evR_eq (fa fo : ℕ → ℕ → ℕ) : ∀ (gs : List (Bool × ℕ × ℕ)) (w : List ℕ),
    evR fa fo gs w.length w.reverse = (gs.foldl (stpG fa fo) w).reverse := by
  intro gs
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ← ih, evR, rd_eq, rd_eq]
    simp [stpG]

theorem length_fold (fa fo : ℕ → ℕ → ℕ) : ∀ (gs : List (Bool × ℕ × ℕ)) (w : List ℕ),
    (gs.foldl (stpG fa fo) w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stpG]
    omega

theorem fold_getD (fa fo : ℕ → ℕ → ℕ) (gs : List (Bool × ℕ × ℕ)) (w : List ℕ) (a : ℕ) :
    (gs.foldl (stpG fa fo) w).getD a 0
      = rd (w.length + gs.length) (evR fa fo gs w.length w.reverse) a := by
  rw [evR_eq, ← length_fold fa fo, rd_eq]

def stpN (w : List ℕ) (g : Bool × ℕ × ℕ) : List ℕ := stpG (fun a b => a &&& b) (fun a b => a ||| b) w g

theorem getD_tb (k : ℕ) (W : List ℕ) (i : ℕ) :
    (W.map fun v => v.testBit k).getD i false = (W.getD i 0).testBit k := by
  have h := List.getD_map (f := fun v : ℕ => v.testBit k) (l := W) (d := 0) (n := i)
  simpa using h

theorem bridge (k : ℕ) : ∀ (gs : List (Bool × ℕ × ℕ)) (W : List ℕ),
    (gs.map toGate).foldl stp (W.map fun v => v.testBit k)
      = (gs.foldl stpN W).map fun v => v.testBit k := by
  intro gs
  induction gs with
  | nil => intro W; rfl
  | cons g gs ih =>
    intro W
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← ih]
    congr 1
    obtain ⟨b, i, j⟩ := g
    have hi := getD_tb k W i
    have hj := getD_tb k W j
    cases b
    · simp only [stp, stpN, stpG, toGate, GateOp.eval, cond, List.map_cons, List.map_nil, List.map_append, hi, hj]
      simp [Nat.testBit_lor]
    · simp only [stp, stpN, stpG, toGate, GateOp.eval, cond, List.map_cons, List.map_nil, List.map_append, hi, hj]
      simp [Nat.testBit_land]

def tab : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, p => if p = n then (2 ^ 2 ^ n - 1) <<< 2 ^ n else tab n p ||| (tab n p <<< 2 ^ n)

theorem tab_bit : ∀ n p k, p < n →
    (tab n p).testBit k = (decide (k < 2 ^ n) && k.testBit p) := by
  intro n
  induction n with
  | zero => intro p k h; omega
  | succ n ih =>
    intro p k hp
    have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    rw [tab]
    split_ifs with hpn
    · subst hpn
      rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      by_cases hk : k < 2 ^ p
      · rw [Nat.testBit_lt_two_pow hk]
        simp
        omega
      · have hb : k.testBit p = !((k - 2 ^ p).testBit p) := by
          rw [← Nat.testBit_two_pow_add_eq]
          congr 1
          omega
        by_cases hk2 : k - 2 ^ p < 2 ^ p
        · have e0 : decide (k ≥ 2 ^ p) = true := by
            simp only [decide_eq_true_eq]
            omega
          have e1 : decide (k - 2 ^ p < 2 ^ p) = true := by simpa using hk2
          have e2 : decide (k < 2 ^ (p + 1)) = true := by
            simp only [decide_eq_true_eq]
            omega
          rw [hb, Nat.testBit_lt_two_pow hk2, e0, e1, e2]
          rfl
        · have e1 : decide (k - 2 ^ p < 2 ^ p) = false := by simpa using hk2
          have e2 : decide (k < 2 ^ (p + 1)) = false := by
            simp only [decide_eq_false_iff_not]
            omega
          rw [e1, e2]
          simp
    · have hp' : p < n := by omega
      rw [Nat.testBit_lor, Nat.testBit_shiftLeft, ih p k hp', ih p (k - 2 ^ n) hp']
      by_cases hk : k < 2 ^ n
      · have e1 : decide (k < 2 ^ n) = true := by simpa using hk
        have e2 : decide (k < 2 ^ (n + 1)) = true := by
          simp only [decide_eq_true_eq]
          omega
        have e3 : decide (k ≥ 2 ^ n) = false := by
          simp only [decide_eq_false_iff_not]
          omega
        rw [e1, e2, e3]
        simp
      · have hb : (k - 2 ^ n).testBit p = k.testBit p := by
          rw [← Nat.testBit_two_pow_add_gt hp' (k - 2 ^ n)]
          congr 1
          omega
        have e1 : decide (k < 2 ^ n) = false := by simpa using hk
        have e3 : decide (k ≥ 2 ^ n) = true := by
          simp only [decide_eq_true_eq]
          omega
        have e4 : decide (k - 2 ^ n < 2 ^ n) = decide (k < 2 ^ (n + 1)) := by
          apply decide_eq_decide.mpr
          omega
        rw [e1, e3, e4, hb]
        simp

def W : List ℕ := (List.range 14).map (tab 14)

theorem W_getD (i : ℕ) : W.getD i 0 = if i < 14 then tab 14 i else 0 := by
  unfold W
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [List.getElem?_range h]
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem W_len : W.length = 14 := by simp [W]

theorem G_len : G.length = 65 := by decide +kernel

def E : ℕ := L.foldr (fun q acc => (tab 14 q.1 &&& tab 14 q.2) ||| acc) 0

set_option maxRecDepth 100000 in
theorem out0 :
    rd 79 (evR (fun a b => a &&& b) (fun a b => a ||| b) G 14 W.reverse) 78 = E := by
  decide +kernel

theorem out_eq : (G.foldl stpN W).getD 78 0 = E := by
  have h := fold_getD (fun a b => a &&& b) (fun a b => a ||| b) G W 78
  rw [W_len, G_len] at h
  exact h.trans out0

theorem any_bit (k : ℕ) (hk : k < 2 ^ 14) : ∀ M : List (Fin 14 × Fin 14),
    (M.foldr (fun q acc => (tab 14 q.1 &&& tab 14 q.2) ||| acc) 0).testBit k
      = M.any (fun q => k.testBit q.1 && k.testBit q.2) := by
  intro M
  induction M with
  | nil => simp
  | cons q M ih =>
    rw [List.foldr_cons, List.any_cons, Nat.testBit_lor, Nat.testBit_land,
      tab_bit 14 q.1 k q.1.2, tab_bit 14 q.2 k q.2.2, ih, decide_eq_true hk]
    simp

theorem main (x : Fin 14 → Bool) :
    PEqualNP.MetaComplexity.circuitFun 14 C0 x = decide (∃ e ∈ L, x e.1 = true ∧ x e.2 = true) := by
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, k < 2 ^ 14 ∧ ∀ (i : ℕ) (h : i < 14), k.testBit i = x ⟨i, h⟩ :=
    ⟨Nat.ofBits x, Nat.ofBits_lt_two_pow x, fun i hi => Nat.testBit_ofBits_lt x i hi⟩
  have hin : List.ofFn x = W.map (fun v => v.testBit k) := by
    refine List.ext_getElem (by simp [W]) (fun i h1 h2 => ?_)
    have h14 : i < 14 := by simpa using h1
    rw [← List.getD_eq_getElem _ false h1, ← List.getD_eq_getElem _ false h2, ofFn_getD, getD_tb,
      W_getD, if_pos h14, tab_bit 14 i k h14, decide_eq_true hk1, Bool.true_and, hk2 i h14,
      dif_pos h14]
  show C0.eval (List.ofFn x) = _
  rw [eval_eq, hin]
  show ((G.map toGate).foldl stp (W.map fun v => v.testBit k)).getD 78 false = _
  rw [bridge, getD_tb, out_eq]
  show (L.foldr (fun q acc => (tab 14 q.1 &&& tab 14 q.2) ||| acc) 0).testBit k = _
  rw [any_bit k hk1 L]
  have hx : ∀ i : Fin 14, k.testBit i = x i := fun i => hk2 i.1 i.2
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, decide_eq_true_eq]
  simp only [hx, Bool.and_eq_true]


end PEqualNP.Outside.L_meta_3753

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_3753 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [32, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [35, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [38, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [37, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [41, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [44, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [47, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [46, 48] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [53, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [52, 54] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [56, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [55, 57] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [60, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [58, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [63, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [64, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 65] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [68, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [66, 69] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [72, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [70, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [75, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [76, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 77] }], output := 78 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 14 C ∧ C.size = 65 ∧
  (∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = decide (∃ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), PEqualNP.Core.ReadTwiceAt 14 C (C.output - 14) e.1 e.2 ↔ e ∈ ([(0, 7), (3, 8)] : List (Fin 14 × Fin 14))) := by
  intro C hC
  have hC' : C = PEqualNP.Outside.L_meta_3753.C0 := hC
  clear hC
  subst hC'
  refine ⟨by decide +kernel, rfl, PEqualNP.Outside.L_meta_3753.main, ?_⟩
  decide +kernel
