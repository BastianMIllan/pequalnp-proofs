import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5507

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- the four test inputs: two edges (0,0), (0,1) and two non-edges (1,0), (0,2)
def good (C : Circuit) : Bool :=
  C.eval (oneEach (0 : Fin 4) (0 : Fin 4)) && C.eval (oneEach (0 : Fin 4) (1 : Fin 4)) &&
    !C.eval (oneEach (1 : Fin 4) (0 : Fin 4)) && !C.eval (oneEach (0 : Fin 4) (2 : Fin 4))

theorem getD_clip (x : List Bool) (k : ℕ) (hx : x.length = k) (a : ℕ) :
    x.getD a false = x.getD (min a k) false := by
  by_cases h : a < k
  · rw [min_eq_left h.le]
  · rw [min_eq_right (by omega), List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega)]

theorem eval_zero (o : ℕ) (x : List Bool) (hx : x.length = 8) :
    Circuit.eval ⟨[], o⟩ x = Circuit.eval ⟨[], min o 8⟩ x := by
  show x.getD o false = x.getD (min o 8) false
  exact getD_clip x 8 hx o

theorem eval_nil (op : GateOp) (o : ℕ) (x : List Bool) (hx : x.length = 8) :
    Circuit.eval ⟨[⟨op, []⟩], o⟩ x = Circuit.eval ⟨[⟨op, []⟩], min o 9⟩ x := by
  show (x ++ [op.eval []]).getD o false = (x ++ [op.eval []]).getD (min o 9) false
  exact getD_clip _ 9 (by simp [hx]) o

theorem eval_one (op : GateOp) (a o : ℕ) (x : List Bool) (hx : x.length = 8) :
    Circuit.eval ⟨[⟨op, [a]⟩], o⟩ x = Circuit.eval ⟨[⟨op, [min a 8]⟩], min o 9⟩ x := by
  show (x ++ [op.eval [x.getD a false]]).getD o false =
    (x ++ [op.eval [x.getD (min a 8) false]]).getD (min o 9) false
  rw [← getD_clip x 8 hx a]
  exact getD_clip _ 9 (by simp [hx]) o

theorem eval_two (op : GateOp) (a b o : ℕ) (x : List Bool) (hx : x.length = 8) :
    Circuit.eval ⟨[⟨op, [a, b]⟩], o⟩ x =
      Circuit.eval ⟨[⟨op, [min a 8, min b 8]⟩], min o 9⟩ x := by
  show (x ++ [op.eval [x.getD a false, x.getD b false]]).getD o false =
    (x ++ [op.eval [x.getD (min a 8) false, x.getD (min b 8) false]]).getD (min o 9) false
  rw [← getD_clip x 8 hx a, ← getD_clip x 8 hx b]
  exact getD_clip _ 9 (by simp [hx]) o

theorem good_zero (o : ℕ) : good ⟨[], o⟩ = good ⟨[], min o 8⟩ := by
  unfold good
  rw [eval_zero o _ (by decide), eval_zero o _ (by decide), eval_zero o _ (by decide),
    eval_zero o _ (by decide)]

theorem good_nil (op : GateOp) (o : ℕ) : good ⟨[⟨op, []⟩], o⟩ = good ⟨[⟨op, []⟩], min o 9⟩ := by
  unfold good
  rw [eval_nil op o _ (by decide), eval_nil op o _ (by decide), eval_nil op o _ (by decide),
    eval_nil op o _ (by decide)]

theorem good_one (op : GateOp) (a o : ℕ) :
    good ⟨[⟨op, [a]⟩], o⟩ = good ⟨[⟨op, [min a 8]⟩], min o 9⟩ := by
  unfold good
  rw [eval_one op a o _ (by decide), eval_one op a o _ (by decide),
    eval_one op a o _ (by decide), eval_one op a o _ (by decide)]

theorem good_two (op : GateOp) (a b o : ℕ) :
    good ⟨[⟨op, [a, b]⟩], o⟩ = good ⟨[⟨op, [min a 8, min b 8]⟩], min o 9⟩ := by
  unfold good
  rw [eval_two op a b o _ (by decide), eval_two op a b o _ (by decide),
    eval_two op a b o _ (by decide), eval_two op a b o _ (by decide)]

theorem chk_zero : ∀ o : Fin 9, good ⟨[], o.val⟩ = false := by decide

theorem chk_nil : ∀ c : Bool, ∀ o : Fin 10,
    good ⟨[⟨cond c GateOp.and GateOp.or, []⟩], o.val⟩ = false := by decide

theorem chk_one : ∀ c : Bool, ∀ a : Fin 9, ∀ o : Fin 10,
    good ⟨[⟨cond c GateOp.and GateOp.or, [a.val]⟩], o.val⟩ = false := by decide

set_option maxRecDepth 8192 in
theorem chk_two_and : ∀ a b : Fin 9, ∀ o : Fin 10,
    good ⟨[⟨GateOp.and, [a.val, b.val]⟩], o.val⟩ = false := by decide +kernel

set_option maxRecDepth 8192 in
theorem chk_two_or : ∀ a b : Fin 9, ∀ o : Fin 10,
    good ⟨[⟨GateOp.or, [a.val, b.val]⟩], o.val⟩ = false := by decide +kernel

theorem op_cases (op : GateOp) (h : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∃ c : Bool, op = cond c GateOp.and GateOp.or := by
  rcases h with rfl | rfl
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩

theorem good_of_rep (C : Circuit)
    (hr : Represents (fun u v : Fin 4 => (3 : ℕ).testBit (4 * u.val + v.val)) C) :
    good C = true := by
  have h1 := hr 0 0
  have h2 := hr 0 1
  have h3 := hr 1 0
  have h4 := hr 0 2
  unfold good
  rw [h1, h2, h3, h4]
  decide

theorem lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (3 : ℕ).testBit (4 * u.val + v.val)) 1 := by
  rintro ⟨⟨gates, o⟩, hm, hs, hr⟩
  have hg := good_of_rep _ hr
  rcases gates with _ | ⟨⟨op, ins⟩, _ | ⟨g2, rest⟩⟩
  · rw [good_zero] at hg
    have := chk_zero ⟨min o 8, by omega⟩
    simp only at this
    rw [this] at hg
    exact absurd hg (by decide)
  · obtain ⟨hop, hlen⟩ := hm ⟨op, ins⟩ (by simp)
    obtain ⟨c, rfl⟩ := op_cases op hop
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, t⟩⟩⟩
    · rw [good_nil] at hg
      have := chk_nil c ⟨min o 9, by omega⟩
      simp only at this
      rw [this] at hg
      exact absurd hg (by decide)
    · rw [good_one] at hg
      have := chk_one c ⟨min a 8, by omega⟩ ⟨min o 9, by omega⟩
      simp only at this
      rw [this] at hg
      exact absurd hg (by decide)
    · rw [good_two] at hg
      cases c
      · have := chk_two_or ⟨min a 8, by omega⟩ ⟨min b 8, by omega⟩ ⟨min o 9, by omega⟩
        simp only at this
        simp only [cond] at hg
        rw [this] at hg
        exact absurd hg (by decide)
      · have := chk_two_and ⟨min a 8, by omega⟩ ⟨min b 8, by omega⟩ ⟨min o 9, by omega⟩
        simp only at this
        simp only [cond] at hg
        rw [this] at hg
        exact absurd hg (by decide)
    · simp at hlen
  · simp [Circuit.size] at hs

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (3 : ℕ).testBit (4 * u.val + v.val)) 2 := by
  refine ⟨⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [0, 8]⟩], 9⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_5507

theorem PEqualNP.Outside.L_meta_5507 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (3 : ℕ).testBit (4 * u.val + v.val)) 2 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (3 : ℕ).testBit (4 * u.val + v.val)) 1 :=
  ⟨PEqualNP.Outside.L_meta_5507.upper, PEqualNP.Outside.L_meta_5507.lower⟩
