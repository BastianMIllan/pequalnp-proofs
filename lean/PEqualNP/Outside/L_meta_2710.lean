import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2710

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- one evaluation step of a circuit
def F : List Bool → Gate → List Bool :=
  fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl F x := rfl

theorem cf_eq (n : ℕ) (C : Circuit) (x : Fin n → Bool) : circuitFun n C x = (C.gates.foldl F (List.ofFn x)).getD C.output false := rfl

theorem fold_pre : ∀ (gs : List Gate) (w : List Bool), ∃ R, gs.foldl F w = w ++ R ∧ R.length = gs.length := by
  intro gs
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨R, h1, h2⟩ := ih (F w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ R, ?_, ?_⟩
    · rw [List.foldl_cons, h1]; simp [F]
    · simp [h2]

theorem gA (l l' : List Bool) (n : ℕ) (h : n < l.length) : (l ++ l').getD n false = l.getD n false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gB (l l' : List Bool) (n : ℕ) (h : l.length ≤ n) : (l ++ l').getD n false = l'.getD (n - l.length) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem fold_len (gs : List Gate) (w : List Bool) : (gs.foldl F w).length = w.length + gs.length := by
  obtain ⟨R, h1, h2⟩ := fold_pre gs w
  rw [h1, List.length_append, h2]

theorem getD_fold (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) : (gs.foldl F w).getD k false = w.getD k false := by
  obtain ⟨R, h1, _⟩ := fold_pre gs w
  rw [h1, gA _ _ _ hk]

-- the index map of the twenty inputs of the inner circuit into the new circuit
def f (i : ℕ) : ℕ := if i < 17 then (if i < 5 then i else if i < 14 then i + 8 else i + 9) else if i < 20 then i + 9 else i + 45

def rg (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem key (w y : List Bool) (hw : w.length = 65) (hy : y.length = 20)
    (hwy : ∀ i < 20, w.getD (f i) false = y.getD i false) (i : ℕ) (vs : List Bool) :
    (w ++ vs).getD (f i) false = (y ++ vs).getD i false := by
  by_cases hi : i < 20
  · have hfi : f i < 29 := by unfold f; split_ifs <;> omega
    rw [gA _ _ _ (by omega), gA _ _ _ (by omega)]
    exact hwy i hi
  · have hfi : f i = i + 45 := by unfold f; split_ifs <;> omega
    rw [hfi, gB _ _ _ (by omega), gB _ _ _ (by omega), hw, hy]
    congr 1

theorem remap (w y : List Bool) (hw : w.length = 65) (hy : y.length = 20)
    (hwy : ∀ i < 20, w.getD (f i) false = y.getD i false) :
    ∀ (gs : List Gate) (vs : List Bool), ∃ R, (gs.map rg).foldl F (w ++ vs) = w ++ R ∧
      gs.foldl F (y ++ vs) = y ++ R ∧ R.length = vs.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro vs; exact ⟨vs, by simp, by simp, by simp⟩
  | cons g gs ih =>
    intro vs
    have hv : g.op.eval ((g.inputs.map f).map fun i => (w ++ vs).getD i false)
        = g.op.eval (g.inputs.map fun i => (y ++ vs).getD i false) := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact key w y hw hy hwy i vs
    obtain ⟨R, h1, h2, h3⟩ := ih (vs ++ [g.op.eval (g.inputs.map fun i => (y ++ vs).getD i false)])
    refine ⟨R, ?_, ?_, ?_⟩
    · rw [List.map_cons, List.foldl_cons]
      have : F (w ++ vs) (rg g) = w ++ (vs ++ [g.op.eval (g.inputs.map fun i => (y ++ vs).getD i false)]) := by
        simp only [F, rg]
        rw [hv, List.append_assoc]
      rw [this, h1]
    · rw [List.foldl_cons]
      have : F (y ++ vs) g = y ++ (vs ++ [g.op.eval (g.inputs.map fun i => (y ++ vs).getD i false)]) := by
        simp only [F]
        rw [List.append_assoc]
      rw [this, h2]
    · rw [h3]; simp; omega

def sub3 : List Gate := [⟨GateOp.or, [16, 18]⟩, ⟨GateOp.or, [19, 23]⟩, ⟨GateOp.or, [26, 27]⟩]

def inc36 : List Gate := [⟨GateOp.or, [15, 22]⟩, ⟨GateOp.or, [17, 29]⟩, ⟨GateOp.or, [18, 30]⟩, ⟨GateOp.and, [5, 31]⟩,
  ⟨GateOp.or, [17, 24]⟩, ⟨GateOp.or, [19, 33]⟩, ⟨GateOp.or, [20, 34]⟩, ⟨GateOp.and, [7, 35]⟩,
  ⟨GateOp.or, [18, 25]⟩, ⟨GateOp.or, [20, 37]⟩, ⟨GateOp.or, [21, 38]⟩, ⟨GateOp.and, [8, 39]⟩,
  ⟨GateOp.or, [19, 13]⟩, ⟨GateOp.or, [21, 41]⟩, ⟨GateOp.or, [22, 42]⟩, ⟨GateOp.and, [9, 43]⟩,
  ⟨GateOp.or, [20, 14]⟩, ⟨GateOp.or, [22, 45]⟩, ⟨GateOp.or, [23, 46]⟩, ⟨GateOp.and, [10, 47]⟩,
  ⟨GateOp.or, [21, 15]⟩, ⟨GateOp.or, [23, 49]⟩, ⟨GateOp.or, [24, 50]⟩, ⟨GateOp.and, [11, 51]⟩,
  ⟨GateOp.or, [22, 16]⟩, ⟨GateOp.or, [24, 53]⟩, ⟨GateOp.or, [25, 54]⟩, ⟨GateOp.and, [12, 55]⟩,
  ⟨GateOp.and, [6, 28]⟩,
  ⟨GateOp.or, [56, 57]⟩, ⟨GateOp.or, [52, 58]⟩, ⟨GateOp.or, [48, 59]⟩, ⟨GateOp.or, [44, 60]⟩,
  ⟨GateOp.or, [40, 61]⟩, ⟨GateOp.or, [36, 62]⟩, ⟨GateOp.or, [32, 63]⟩]

def pc : Circuit := ⟨sub3 ++ inc36, 64⟩

def lp : List (Fin 26 × List (Fin 26)) := [(5, [18, 17, 15, 22]), (7, [20, 19, 17, 24]), (8, [21, 20, 18, 25]), (9, [22, 21, 19, 13]), (10, [23, 22, 20, 14]), (11, [24, 23, 21, 15]), (12, [25, 24, 22, 16]), (6, [16, 18, 19, 23])]

def ff (x : Fin 26 → Bool) : Bool := lp.any (fun q => x q.1 && q.2.any x)

theorem ofn (x : Fin 26 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25] := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ev (x : Fin 26 → Bool) : circuitFun 26 pc x = ff x := by
  show (pc.wires (List.ofFn x)).getD 64 false = ff x
  rw [ofn]
  simp [Circuit.wires, pc, sub3, inc36, GateOp.eval, ff, lp, Bool.or_assoc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem key1 : ∀ p l : Fin 13, 5 ≤ (p : ℕ) → (∃ d ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], p = l + d) → ∃ q ∈ lp, q.1 = Fin.castAdd 13 p ∧ Fin.natAdd 13 l ∈ q.2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem key2 : ∀ q ∈ lp, ∀ m ∈ q.2, ∃ p l : Fin 13, q.1 = Fin.castAdd 13 p ∧ m = Fin.natAdd 13 l ∧ 5 ≤ (p : ℕ) ∧ ∃ d ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))), p = l + d := by
  decide +kernel

theorem conv (p l : Fin 13) (h : ∃ d ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))), p = l + d) : ∃ d ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], p = l + d := by
  simpa using h

theorem spec (x : Fin 26 → Bool) : ff x = Decidable.decide (∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (5 : ℕ) ≤ ↑x7 ∧ (∃ x4 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x7 = x8 + x4) ∧ x (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) x8) = Bool.true) := by
  rw [Bool.eq_iff_iff]
  simp only [ff, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨q, hq, h1, m, hm, h2⟩
    obtain ⟨p, l, e1, e2, h5, hI⟩ := key2 q hq m hm
    exact ⟨p, l, h5, conv p l hI, e1 ▸ h1, e2 ▸ h2⟩
  · rintro ⟨p, l, h5, hI, hp, hl⟩
    obtain ⟨q, hq, e1, e2⟩ := key1 p l h5 hI
    exact ⟨q, hq, e1 ▸ hp, _, e2, hl⟩

def sub (x1 : Fin (26 : ℕ) → Bool) (x2 : Fin (20 : ℕ)) : Bool := if ↑x2 < (17 : ℕ) then x1 (Fin.ofNat (26 : ℕ) (if ↑x2 < (5 : ℕ) then ↑x2 else if ↑x2 < (14 : ℕ) then ↑x2 + (8 : ℕ) else ↑x2 + (9 : ℕ))) else Decidable.decide (↑x2 ≠ (18 : ℕ)) && (x1 (16 : Fin (26 : ℕ)) || x1 (18 : Fin (26 : ℕ))) || Decidable.decide (↑x2 ≠ (17 : ℕ)) && (x1 (19 : Fin (26 : ℕ)) || x1 (23 : Fin (26 : ℕ)))

theorem s3 (x : Fin 26 → Bool) : sub3.foldl F (List.ofFn x) = List.ofFn x ++ [x 16 || (x 18 || false), x 19 || (x 23 || false), (x 16 || (x 18 || false)) || ((x 19 || (x 23 || false)) || false)] := by
  rw [ofn]; rfl

theorem hwy (x : Fin 26 → Bool) : ∀ i < 20, ((sub3 ++ inc36).foldl F (List.ofFn x)).getD (f i) false = (List.ofFn (sub x)).getD i false := by
  intro i hi
  have hl : (sub3.foldl F (List.ofFn x)).length = 29 := by
    rw [fold_len]; simp [sub3]
  have hfi : f i < 29 := by unfold f; split_ifs <;> omega
  rw [List.foldl_append, getD_fold _ _ _ (by omega), s3]
  interval_cases i
  all_goals try rfl
  · show (x 16 || (x 18 || false)) = ((decide ((17 : ℕ) ≠ 18) && (x 16 || x 18)) || (decide ((17 : ℕ) ≠ 17) && (x 19 || x 23)))
    simp
  · show (x 19 || (x 23 || false)) = ((decide ((18 : ℕ) ≠ 18) && (x 16 || x 18)) || (decide ((18 : ℕ) ≠ 17) && (x 19 || x 23)))
    simp
  · show ((x 16 || (x 18 || false)) || ((x 19 || (x 23 || false)) || false)) = ((decide ((19 : ℕ) ≠ 18) && (x 16 || x 18)) || (decide ((19 : ℕ) ≠ 17) && (x 19 || x 23)))
    simp

theorem core : ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ x3.size + (40 : ℕ) ∧ ∀ (x6 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x5 x6 = (Decidable.decide (∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (5 : ℕ) ≤ ↑x7 ∧ (∃ x4 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x7 = x8 + x4) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) || PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x3 (sub x6)) := by
  intro x3 hx3
  refine ⟨⟨sub3 ++ inc36 ++ x3.gates.map rg ++ [⟨GateOp.or, [64, f x3.output]⟩], 65 + x3.gates.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with ((hg | hg) | ⟨g0, hg0, rfl⟩) | rfl
    · simp only [sub3, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp
    · simp only [inc36, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · obtain ⟨h1, h2⟩ := hx3 g0 hg0
      exact ⟨h1, by simp [rg, h2]⟩
    · simp
  · simp [Circuit.size, sub3, inc36]
  · intro x6
    have hw : ((sub3 ++ inc36).foldl F (List.ofFn x6)).length = 65 := by
      rw [fold_len]; simp [sub3, inc36]
    have hy : (List.ofFn (sub x6)).length = 20 := by simp
    obtain ⟨R, h1, h2, h3⟩ := remap _ _ hw hy (hwy x6) x3.gates []
    simp only [List.append_nil, List.length_nil, Nat.zero_add] at h1 h2 h3
    have e1 : circuitFun 20 x3 (sub x6) = (List.ofFn (sub x6) ++ R).getD x3.output false := by
      rw [cf_eq, h2]
    have e0 : ((sub3 ++ inc36).foldl F (List.ofFn x6)).getD 64 false = ff x6 := (ev x6)
    rw [e1, ← spec, ← e0, cf_eq]
    dsimp only
    rw [List.foldl_append, List.foldl_append, h1]
    simp only [List.foldl_cons, List.foldl_nil, F]
    rw [gB _ _ _ (by rw [List.length_append, hw, h3])]
    simp only [List.length_append, hw, h3, Nat.sub_self, List.getD_cons_zero, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false]
    rw [gA _ _ _ (by omega), key _ _ hw hy (hwy x6)]

end PEqualNP.Outside.L_meta_2710

theorem PEqualNP.Outside.L_meta_2710 : have x1 : (Fin (26 : ℕ) → Bool) → Fin (20 : ℕ) → Bool := fun (x1 : Fin (26 : ℕ) → Bool) (x2 : Fin (20 : ℕ)) => if ↑x2 < (17 : ℕ) then x1 (Fin.ofNat (26 : ℕ) (if ↑x2 < (5 : ℕ) then ↑x2 else if ↑x2 < (14 : ℕ) then ↑x2 + (8 : ℕ) else ↑x2 + (9 : ℕ))) else Decidable.decide (↑x2 ≠ (18 : ℕ)) && (x1 (16 : Fin (26 : ℕ)) || x1 (18 : Fin (26 : ℕ))) || Decidable.decide (↑x2 ≠ (17 : ℕ)) && (x1 (19 : Fin (26 : ℕ)) || x1 (23 : Fin (26 : ℕ))); let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x2 = x3 + x4; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ x3.size + (40 : ℕ) ∧ ∀ (x6 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x5 x6 = (Decidable.decide (∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (5 : ℕ) ≤ ↑x7 ∧ x2 x7 x8 ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) || PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x3 (x1 x6)) := by
  exact PEqualNP.Outside.L_meta_2710.core
