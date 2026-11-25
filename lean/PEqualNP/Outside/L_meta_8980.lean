import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8980

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem snoc_val (hs : List Gate) (g : Gate) (x : List Bool) :
    (run (hs ++ [g]) x).getD (x.length + hs.length) false =
      g.op.eval (g.inputs.map fun i => (run hs x).getD i false) := by
  rw [run_snoc, ← run_length]
  exact getD_at' false _ _

def mono (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem any_congr' {l : List ℕ} {f g : ℕ → Bool} (h : ∀ w ∈ l, f w = g w) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun w hw => h w (by simp [hw]))]

theorem orChain (N : ℕ) : ∀ (ws : List ℕ) (hs : List Gate) (a : ℕ), a < N + hs.length →
    (∀ w ∈ ws, w < N + hs.length) →
    ∃ e : List Gate, e.length = ws.length ∧ (∀ g ∈ e, mono g) ∧ ∃ r, r < N + hs.length + e.length ∧
      ∀ x : List Bool, x.length = N → (run (hs ++ e) x).getD r false =
        ((a :: ws).any fun w => (run hs x).getD w false)
  | [], hs, a, ha, _ => ⟨[], rfl, by simp, a, by simpa using ha, fun x _ => by simp⟩
  | b :: ws, hs, a, ha, hw => by
    have hb : b < N + hs.length := hw b (by simp)
    obtain ⟨e, he1, he2, r, hr, hv⟩ := orChain N ws (hs ++ [⟨GateOp.or, [a, b]⟩]) (N + hs.length)
      (by simp) (fun w hw' => by have := hw w (by simp [hw']); simp; omega)
    refine ⟨⟨GateOp.or, [a, b]⟩ :: e, by simp [he1], ?_, r, by simp at hr ⊢; omega, fun x hx => ?_⟩
    · intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact ⟨Or.inr rfl, by simp⟩
      · exact he2 g hg
    · have e1 : hs ++ ⟨GateOp.or, [a, b]⟩ :: e = (hs ++ [⟨GateOp.or, [a, b]⟩]) ++ e := by simp
      rw [e1, hv x hx]
      have v1 : (run (hs ++ [⟨GateOp.or, [a, b]⟩]) x).getD (N + hs.length) false =
          ((run hs x).getD a false || (run hs x).getD b false) := by
        rw [← hx, snoc_val]
        simp [GateOp.eval]
      have pre : ∀ w, w < N + hs.length →
          (run (hs ++ [⟨GateOp.or, [a, b]⟩]) x).getD w false = (run hs x).getD w false :=
        fun w hw' => run_prefix hs _ x w (by rw [hx]; exact hw')
      rw [List.any_cons, v1, any_congr' (fun w hw' => pre w (hw w (by simp [hw'])))]
      simp only [List.any_cons, Bool.or_assoc]

theorem layer (N : ℕ) (f : ℕ → Gate) (hs : List Gate) (n : ℕ)
    (hf : ∀ j < n, ∀ i ∈ (f j).inputs, i < N + hs.length) :
    ∀ x : List Bool, x.length = N → ∀ j < n,
      (run (hs ++ (List.range n).map f) x).getD (N + hs.length + j) false =
        (f j).op.eval ((f j).inputs.map fun i => (run hs x).getD i false) := by
  induction n with
  | zero => intro x _ j hj; omega
  | succ n ih =>
    intro x hx j hj
    have ih' := ih (fun j hj' => hf j (by omega)) x hx
    rw [List.range_succ, List.map_append, List.map_singleton, ← List.append_assoc]
    have hlen : (hs ++ (List.range n).map f).length = hs.length + n := by simp
    rcases Nat.lt_or_ge j n with h | h
    · rw [run_prefix _ _ _ _ (by rw [hlen, hx]; omega)]
      exact ih' j h
    · rw [show j = n by omega]
      have e1 : N + hs.length + n = x.length + (hs ++ (List.range n).map f).length := by
        rw [hlen, hx]; omega
      rw [e1, snoc_val]
      congr 1
      refine List.map_congr_left fun i hi => ?_
      exact run_prefix _ _ _ _ (by rw [hx]; exact hf n (by omega) i hi)

def pairGate (pos : ℕ → ℕ) (j : ℕ) : Gate := ⟨GateOp.or, [pos (2 * j), pos (2 * j + 1)]⟩

theorem anyEven (P U c : ℕ) (hP : 1 ≤ P) (hU : U < 2 * P) (hc : c < 2) :
    (decide (c = U) || (List.range (P - 1)).any (fun j => decide (2 * (j + 1) + c = U))) =
      decide (U % 2 = c) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]
  constructor
  · rintro (h | ⟨j, _, h⟩) <;> omega
  · intro h
    by_cases h0 : U = c
    · exact Or.inl h0.symm
    · exact Or.inr ⟨(U - c) / 2 - 1, by omega, by omega⟩

theorem bitf (U : ℕ) : decide (U % 2 = 0) = decide (U.testBit 0 = false) := by
  rcases Nat.mod_two_eq_zero_or_one U with h | h <;> simp [Nat.testBit_zero, h]

theorem bitt (U : ℕ) : decide (U % 2 = 1) = decide (U.testBit 0 = true) := by
  rcases Nat.mod_two_eq_zero_or_one U with h | h <;> simp [Nat.testBit_zero, h]

theorem dec (N : ℕ) (X : Type) (src : X → List Bool) (hsrc : ∀ x, (src x).length = N) :
    ∀ (k : ℕ) (hs : List Gate) (pos : ℕ → ℕ), (∀ j < 2 ^ k, pos j < N + hs.length) →
    ∀ (U : X → ℕ), (∀ x, U x < 2 ^ k) →
    (∀ x, ∀ j < 2 ^ k, (run hs (src x)).getD (pos j) false = decide (j = U x)) →
    ∃ e : List Gate, (∀ g ∈ e, mono g) ∧ e.length + 3 ≤ 3 * 2 ^ k ∧ ∃ w : ℕ → Bool → ℕ,
      ∀ x, ∀ i < k, ∀ b : Bool,
        (run (hs ++ e) (src x)).getD (w i b) false = decide ((U x).testBit i = b) := by
  intro k
  induction k with
  | zero =>
    intro hs pos _ U _ _
    exact ⟨[], by simp, by simp, fun _ _ => 0, fun x i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hs pos hpos U hU hval
    have hP : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have hP1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hl := layer N (pairGate pos) hs (2 ^ k) (fun j hj i hi => by
      simp only [pairGate, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hpos _ (by omega)
      · exact hpos _ (by omega))
    have he1 : ((List.range (2 ^ k)).map (pairGate pos)).length = 2 ^ k := by simp
    obtain ⟨e2, he2l, he2m, r0, hr0, hv0⟩ := orChain N
      ((List.range (2 ^ k - 1)).map fun j => pos (2 * (j + 1) + 0))
      (hs ++ (List.range (2 ^ k)).map (pairGate pos)) (pos 0)
      (by have := hpos 0 (by omega); rw [List.length_append, he1]; omega)
      (by
        intro w hw
        simp only [List.mem_map, List.mem_range] at hw
        obtain ⟨j, hj, rfl⟩ := hw
        have := hpos (2 * (j + 1) + 0) (by omega)
        rw [List.length_append, he1]; omega)
    obtain ⟨e3, he3l, he3m, r1, hr1, hv1⟩ := orChain N
      ((List.range (2 ^ k - 1)).map fun j => pos (2 * (j + 1) + 1))
      (hs ++ (List.range (2 ^ k)).map (pairGate pos) ++ e2) (pos 1)
      (by have := hpos 1 (by omega); rw [List.length_append, List.length_append, he1]; omega)
      (by
        intro w hw
        simp only [List.mem_map, List.mem_range] at hw
        obtain ⟨j, hj, rfl⟩ := hw
        have := hpos (2 * (j + 1) + 1) (by omega)
        rw [List.length_append, List.length_append, he1]; omega)
    have hq : ∀ (t : List Gate) x, ∀ j < 2 ^ (k + 1),
        (run (hs ++ t) (src x)).getD (pos j) false = decide (j = U x) := by
      intro t x j hj
      rw [run_prefix _ _ _ _ (by rw [hsrc]; exact hpos j hj)]
      exact hval x j hj
    have hany : ∀ (t : List Gate) x, ∀ c < 2,
        ((List.range (2 ^ k - 1)).map (fun j => pos (2 * (j + 1) + c))).any
          (fun w => (run (hs ++ t) (src x)).getD w false) =
        (List.range (2 ^ k - 1)).any (fun j => decide (2 * (j + 1) + c = U x)) := by
      intro t x c hc
      rw [List.any_map]
      exact any_congr' (fun j hj => by
        simp only [Function.comp]
        simp only [List.mem_range] at hj
        exact hq t x _ (by omega))
    obtain ⟨e4, he4m, he4l, w, hw⟩ := ih
      (hs ++ (List.range (2 ^ k)).map (pairGate pos) ++ e2 ++ e3)
      (fun j => N + hs.length + j)
      (fun j hj => by simp only [List.length_append, he1]; omega)
      (fun x => U x / 2) (fun x => by have := hU x; omega)
      (fun x j hj => by
        rw [run_prefix _ e3 _ _ (by rw [hsrc, List.length_append, List.length_append, he1]; omega),
          run_prefix _ e2 _ _ (by rw [hsrc, List.length_append, he1]; omega),
          hl (src x) (hsrc x) j hj]
        simp only [pairGate, List.map_cons, List.map_nil]
        rw [hval x _ (by omega), hval x _ (by omega)]
        rw [Bool.eq_iff_iff]
        simp [GateOp.eval]
        omega)
    refine ⟨(List.range (2 ^ k)).map (pairGate pos) ++ e2 ++ e3 ++ e4, ?_, ?_,
      fun i b => if i = 0 then (if b then r1 else r0) else w (i - 1) b, ?_⟩
    · intro g hg
      simp only [List.mem_append] at hg
      rcases hg with ((hg | hg) | hg) | hg
      · simp only [List.mem_map] at hg
        obtain ⟨j, _, rfl⟩ := hg
        exact ⟨Or.inr rfl, by simp [pairGate]⟩
      · exact he2m g hg
      · exact he3m g hg
      · exact he4m g hg
    · simp only [List.length_append, he1, he2l, he3l, List.length_map, List.length_range]
      omega
    · intro x i hi b
      have ea : hs ++ ((List.range (2 ^ k)).map (pairGate pos) ++ e2 ++ e3 ++ e4) =
          hs ++ (List.range (2 ^ k)).map (pairGate pos) ++ e2 ++ e3 ++ e4 := by simp
      rw [ea]
      rcases i with _ | i
      · simp only [if_true]
        cases b
        · simp only [Bool.false_eq_true, if_false]
          rw [run_prefix _ e4 _ _ (by
                rw [hsrc, List.length_append, List.length_append, List.length_append, he1]
                rw [List.length_append, he1] at hr0; omega),
            run_prefix _ e3 _ _ (by
                rw [hsrc, List.length_append, List.length_append, he1]
                rw [List.length_append, he1] at hr0; omega),
            hv0 (src x) (hsrc x), List.any_cons, hany _ x 0 (by omega), hq _ x 0 (by omega),
            anyEven (2 ^ k) (U x) 0 hP1 (by have := hU x; omega) (by omega)]
          exact bitf (U x)
        · simp only [if_true]
          rw [run_prefix _ e4 _ _ (by
                rw [hsrc, List.length_append, List.length_append, List.length_append, he1]
                rw [List.length_append, List.length_append, he1] at hr1; omega),
            hv1 (src x) (hsrc x), List.any_cons, List.append_assoc hs, hany _ x 1 (by omega),
            hq _ x 1 (by omega),
            anyEven (2 ^ k) (U x) 1 hP1 (by have := hU x; omega) (by omega)]
          exact bitt (U x)
      · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        rw [hw x i (by omega) b, Nat.testBit_div_two]

end PEqualNP.Outside.L_meta_8980

theorem PEqualNP.Outside.L_meta_8980 : ∀ (k m : ℕ), ∃ gs : List PEqualNP.CircuitLowerBounds.Gate, PEqualNP.MetaComplexity.Monotone2 (⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ gs.length ≤ 3 * 2 ^ k ∧ ∃ w : Fin k → Bool → ℕ, ∀ (u : Fin (2 ^ k)) (v : Fin m) (i : Fin k) (b : Bool), ((⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (PEqualNP.Represents.oneEach u v)).getD (w i b) false = decide ((u : ℕ).testBit i = b) := by
  intro k m
  obtain ⟨e, hm, hl, w, hw⟩ := PEqualNP.Outside.L_meta_8980.dec (2 ^ k + m) (Fin (2 ^ k) × Fin m)
    (fun p => PEqualNP.Represents.oneEach p.1 p.2)
    (fun p => by simp [PEqualNP.Represents.oneEach]) k [] (fun j => j)
    (fun j hj => by simp; omega) (fun p => (p.1 : ℕ)) (fun p => p.1.isLt)
    (fun p j hj => by
      show (PEqualNP.Represents.oneEach p.1 p.2).getD j false = decide (j = (p.1 : ℕ))
      unfold PEqualNP.Represents.oneEach
      rw [List.getD_append _ _ _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj),
        List.getElem_ofFn]
      simp [Fin.ext_iff])
  refine ⟨e, fun g hg => ?_, by omega, fun i b => w i b, fun u v i b => ?_⟩
  · have := hm g hg
    refine ⟨?_, this.2⟩
    rcases this.1 with h | h <;> simp [h]
  · have h := hw (u, v) i i.isLt b
    rw [List.nil_append] at h
    exact h
