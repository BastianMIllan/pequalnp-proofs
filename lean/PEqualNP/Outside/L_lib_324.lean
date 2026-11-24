import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_324

open PEqualNP.CircuitLowerBounds

def enc : List Bool → ℕ
  | [] => 0
  | b :: t => Nat.bit b (enc t)

theorem enc_testBit (w : List Bool) (i : ℕ) : (enc w).testBit i = w.getD i false := by
  induction w generalizing i with
  | nil => simp [enc]
  | cons b t ih =>
    cases i with
    | zero => simp [enc]
    | succ i => simp [enc, Nat.testBit_bit_succ, ih]

def run : List Gate → ℕ → ℕ → ℕ
  | [], _, W => W
  | g :: gs, k, W =>
    run gs (k + 1) (W ||| (bif g.op.eval (g.inputs.map fun i => W.testBit i) then 2 ^ k else 0))

theorem getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = (w.getD i false || (b && decide (w.length = i))) := by
  rcases lt_trichotomy i w.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, h.ne']
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · obtain ⟨d, rfl⟩ : ∃ d, i = w.length + (d + 1) := ⟨i - w.length - 1, by omega⟩
    simp [List.getD_eq_getElem?_getD]

theorem run_rep (gs : List Gate) (w : List Bool) (W : ℕ)
    (h : ∀ i, W.testBit i = w.getD i false) (i : ℕ) :
    (run gs w.length W).testBit i =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false := by
  induction gs generalizing w W i with
  | nil => simpa [run] using h i
  | cons g gs ih =>
    have hv : (g.inputs.map fun i => W.testBit i) = (g.inputs.map fun i => w.getD i false) := by
      congr 1
      funext j
      exact h j
    have hrep : ∀ j, (W ||| (bif g.op.eval (g.inputs.map fun i => w.getD i false) then 2 ^ w.length
        else 0)).testBit j
        = (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD j false := by
      intro j
      rw [getD_snoc, Nat.testBit_lor, h j]
      cases g.op.eval (g.inputs.map fun i => w.getD i false) <;> simp [Nat.testBit_two_pow]
    have key := ih _ _ hrep i
    simp only [List.length_append, List.length_singleton] at key
    simp only [run, List.foldl_cons, hv]
    exact key

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (run C.gates x.length (enc x)).testBit C.output := by
  unfold Circuit.eval Circuit.wires
  exact (run_rep C.gates x (enc x) (enc_testBit x) C.output).symm


def F (x : Fin 14 → Bool) : Bool :=
  (x 0 && x 7) || ((x 1 && x 7) || ((x 2 && x 7) || ((x 0 && x 8) || ((x 3 && x 8) || ((x 4 && x 8) || ((x 0 && x 9) || ((x 5 && x 9) || ((x 6 && x 9) || ((x 1 && x 10) || ((x 3 && x 10) || ((x 5 && x 10) || ((x 1 && x 11) || ((x 4 && x 11) || ((x 6 && x 11) || ((x 2 && x 12) || ((x 3 && x 12) || ((x 6 && x 12) || ((x 2 && x 13) || ((x 4 && x 13) || ((x 5 && x 13)))))))))))))))))))))

def C : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.CircuitLowerBounds.Circuit.mk [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 15]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 23]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 6]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 35]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 27]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [42, 36]⟩] 43

theorem enc_lt (w : List Bool) : enc w < 2 ^ w.length := by
  induction w with
  | nil => simp [enc]
  | cons b t ih =>
    simp only [enc, Nat.bit_val, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

def chk (m : ℕ) : Bool :=
  decide ((run C.gates 14 m).testBit 43 = F (fun i : Fin 14 => m.testBit i))

theorem k0 : (List.range' 0 1024).all chk = true := by
  decide +kernel

theorem k1 : (List.range' 1024 1024).all chk = true := by
  decide +kernel

theorem k2 : (List.range' 2048 1024).all chk = true := by
  decide +kernel

theorem k3 : (List.range' 3072 1024).all chk = true := by
  decide +kernel

theorem k4 : (List.range' 4096 1024).all chk = true := by
  decide +kernel

theorem k5 : (List.range' 5120 1024).all chk = true := by
  decide +kernel

theorem k6 : (List.range' 6144 1024).all chk = true := by
  decide +kernel

theorem k7 : (List.range' 7168 1024).all chk = true := by
  decide +kernel

theorem k8 : (List.range' 8192 1024).all chk = true := by
  decide +kernel

theorem k9 : (List.range' 9216 1024).all chk = true := by
  decide +kernel

theorem k10 : (List.range' 10240 1024).all chk = true := by
  decide +kernel

theorem k11 : (List.range' 11264 1024).all chk = true := by
  decide +kernel

theorem k12 : (List.range' 12288 1024).all chk = true := by
  decide +kernel

theorem k13 : (List.range' 13312 1024).all chk = true := by
  decide +kernel

theorem k14 : (List.range' 14336 1024).all chk = true := by
  decide +kernel

theorem k15 : (List.range' 15360 1024).all chk = true := by
  decide +kernel

theorem kern (m : ℕ) (h : m < 16384) :
    (run C.gates 14 m).testBit 43 = F (fun i : Fin 14 => m.testBit i) := by
  have hj : m / 1024 < 16 := by omega
  have hc : chk m = true := by
    interval_cases hq : m / 1024
    · exact List.all_eq_true.mp k0 m (List.mem_range'_1.mpr (by omega))
    · exact List.all_eq_true.mp k1 m (List.mem_range'_1.mpr (by omega))
    · exact List.all_eq_true.mp k2 m (List.mem_range'_1.mpr (by omega))
    · exact List.all_eq_true.mp k3 m (List.mem_range'_1.mpr (by omega))
    · exact List.all_eq_true.mp k4 m (List.mem_range'_1.mpr (by omega))
    · exact List.all_eq_true.mp k5 m (List.mem_range'_1.mpr (by omega))
    · exact List.all_eq_true.mp k6 m (List.mem_range'_1.mpr (by omega))
    · exact List.all_eq_true.mp k7 m (List.mem_range'_1.mpr (by omega))
    · exact List.all_eq_true.mp k8 m (List.mem_range'_1.mpr (by omega))
    · exact List.all_eq_true.mp k9 m (List.mem_range'_1.mpr (by omega))
    · exact List.all_eq_true.mp k10 m (List.mem_range'_1.mpr (by omega))
    · exact List.all_eq_true.mp k11 m (List.mem_range'_1.mpr (by omega))
    · exact List.all_eq_true.mp k12 m (List.mem_range'_1.mpr (by omega))
    · exact List.all_eq_true.mp k13 m (List.mem_range'_1.mpr (by omega))
    · exact List.all_eq_true.mp k14 m (List.mem_range'_1.mpr (by omega))
    · exact List.all_eq_true.mp k15 m (List.mem_range'_1.mpr (by omega))
  exact of_decide_eq_true hc

theorem circ_eq (x : Fin 14 → Bool) : PEqualNP.MetaComplexity.circuitFun 14 C x = F x := by
  unfold PEqualNP.MetaComplexity.circuitFun
  rw [eval_eq, List.length_ofFn]
  show (run C.gates 14 (enc (List.ofFn x))).testBit 43 = F x
  have hlt : enc (List.ofFn x) < 2 ^ 14 := by
    have := enc_lt (List.ofFn x)
    simpa using this
  have hbits : ∀ i : Fin 14, (enc (List.ofFn x)).testBit i = x i := by
    intro i
    rw [enc_testBit]
    fin_cases i <;> rfl
  have hx : x = fun i : Fin 14 => (enc (List.ofFn x)).testBit i := by
    funext i
    exact (hbits i).symm
  generalize enc (List.ofFn x) = m at hlt hx ⊢
  have key := kern m hlt
  rw [key, ← hx]

theorem graph_eq (x : Fin 14 → Bool) :
    PEqualNP.MetaComplexity.NestedCover.graphFun (PEqualNP.EdgeOwnership.edgeGraph 14 [(0, 7), (1, 7), (2, 7), (0, 8), (3, 8), (4, 8), (0, 9), (5, 9), (6, 9), (1, 10), (3, 10), (5, 10), (1, 11), (4, 11), (6, 11), (2, 12), (3, 12), (6, 12), (2, 13), (4, 13), (5, 13)]) ∅ x = F x := by
  unfold PEqualNP.MetaComplexity.NestedCover.graphFun
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨u, v, hadj, hu, hv⟩
    fin_cases u <;> fin_cases v
    all_goals first
      | exact absurd hadj (by decide)
      | skip
    all_goals simp only [F, Bool.or_eq_true, Bool.and_eq_true]
    all_goals first
      | exact Or.inl ⟨hu, hv⟩
      | exact Or.inr (Or.inl ⟨hu, hv⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨hu, hv⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩)))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩)))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩)))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩))))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩)))))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩))))))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩)))))))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩))))))))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩)))))))))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩))))))))))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩)))))))))))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hu, hv⟩))))))))))))))))))))
      | exact Or.inl ⟨hv, hu⟩
      | exact Or.inr (Or.inl ⟨hv, hu⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨hv, hu⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu⟩)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu⟩))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu⟩)))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu⟩))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu⟩)))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu⟩))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu⟩)))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu⟩))))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu⟩)))))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu⟩))))))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu⟩)))))))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu⟩))))))))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu⟩)))))))))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu⟩))))))))))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu⟩)))))))))))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hv, hu⟩))))))))))))))))))))
  · intro h
    simp only [F, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      exact ⟨_, _, by decide, h.1, h.2⟩

end PEqualNP.Outside.L_lib_324

theorem PEqualNP.Outside.L_lib_324 : PEqualNP.MetaComplexity.circuitFun 14 (PEqualNP.CircuitLowerBounds.Circuit.mk [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 15]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 23]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 6]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 35]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 27]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [42, 36]⟩] 43) = PEqualNP.MetaComplexity.NestedCover.graphFun (PEqualNP.EdgeOwnership.edgeGraph 14 [(0, 7), (1, 7), (2, 7), (0, 8), (3, 8), (4, 8),
  (0, 9), (5, 9), (6, 9), (1, 10), (3, 10), (5, 10), (1, 11), (4, 11), (6, 11), (2, 12), (3, 12),
  (6, 12), (2, 13), (4, 13), (5, 13)]) ∅ := by
  funext x
  rw [PEqualNP.Outside.L_lib_324.graph_eq]
  exact PEqualNP.Outside.L_lib_324.circ_eq x
