import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9019

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


def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len_foldl (G : List Gate) (s : List Bool) :
    (G.foldl step s).length = s.length + G.length := by
  induction G generalizing s with
  | nil => simp
  | cons g G ih => simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons,
      List.length_nil]; omega

def remap (L M K : ℕ) (w : Fin L → ℕ) (i : ℕ) : ℕ :=
  if h : i < L then (if w ⟨i, h⟩ < M then w ⟨i, h⟩ else M + K) else M + (i - L)

def mapGate (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

theorem main (W y : List Bool) (r : ℕ → ℕ) (K : ℕ)
    (hr : ∀ E : List Bool, E.length ≤ K → ∀ i, (W ++ E).getD (r i) false = (y ++ E).getD i false) :
    ∀ (G : List Gate) (E : List Bool), E.length + G.length ≤ K →
      ∃ E' : List Bool, E'.length = E.length + G.length ∧
        (G.map (mapGate r)).foldl step (W ++ E) = W ++ E' ∧ G.foldl step (y ++ E) = y ++ E' := by
  intro G
  induction G with
  | nil => intro E _; exact ⟨E, by simp, by simp, by simp⟩
  | cons g G ih =>
    intro E hE
    simp only [List.length_cons] at hE
    have hv : (g.inputs.map r).map (fun i => (W ++ E).getD i false)
        = g.inputs.map (fun i => (y ++ E).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact hr E (by omega) i
    obtain ⟨E', h1, h2, h3⟩ :=
      ih (E ++ [g.op.eval (g.inputs.map fun i => (y ++ E).getD i false)])
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    refine ⟨E', ?_, ?_, ?_⟩
    · rw [h1]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · simp only [List.map_cons, List.foldl_cons]
      have : step (W ++ E) (mapGate r g)
          = W ++ (E ++ [g.op.eval (g.inputs.map fun i => (y ++ E).getD i false)]) := by
        simp only [step, mapGate]
        rw [hv, List.append_assoc]
      rw [this, h2]
    · simp only [List.foldl_cons]
      have : step (y ++ E) g
          = y ++ (E ++ [g.op.eval (g.inputs.map fun i => (y ++ E).getD i false)]) := by
        simp only [step, List.append_assoc]
      rw [this, h3]

theorem getD_left (l l' : List Bool) (n : ℕ) (h : n < l.length) :
    (l ++ l').getD n false = l.getD n false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_right (l l' : List Bool) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getD n false = l'.getD (n - l.length) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_big (l : List Bool) (n : ℕ) (h : l.length ≤ n) : l.getD n false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

theorem hr_of (L M K : ℕ) (w : Fin L → ℕ) (W : List Bool) (v : Fin L → Bool)
    (hW : W.length = M) (hw : ∀ j, W.getD (w j) false = v j) :
    ∀ E : List Bool, E.length ≤ K → ∀ i,
      (W ++ E).getD (remap L M K w i) false = (List.ofFn v ++ E).getD i false := by
  intro E hE i
  unfold remap
  by_cases h : i < L
  · rw [dif_pos h, getD_left (List.ofFn v) E i (by simp [h])]
    have hy : (List.ofFn v).getD i false = v ⟨i, h⟩ := by
      simp [List.getD_eq_getElem?_getD, h]
    rw [hy]
    by_cases h2 : w ⟨i, h⟩ < M
    · rw [if_pos h2, getD_left _ _ _ (by omega), hw]
    · rw [if_neg h2, ← hw, getD_big _ _ (by simp; omega), getD_big W _ (by omega)]
  · rw [dif_neg h, getD_right _ _ _ (by omega), getD_right _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    congr 1
    omega


theorem compose : ∀ (N L : ℕ) (D : Set (List Bool)) (P : List PEqualNP.CircuitLowerBounds.Gate) (w : Fin L → ℕ) (g : Fin L → List Bool → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ x ∈ D, x.length = N) → PEqualNP.MetaComplexity.Monotone2 (⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x ∈ D, ∀ j, ((⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).getD (w j) false = g j x) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size ≤ P.length + C.size ∧ ∀ x ∈ D, C'.eval x = C.eval (List.ofFn fun j => g j x) := by
  intro N L D P w g C hD hP hC hw
  let M := N + P.length
  let K := C.gates.length
  let r := remap L M K w
  refine ⟨⟨P ++ C.gates.map (mapGate r), r C.output⟩, ?_, ?_, ?_⟩
  · intro gt hgt
    rw [List.mem_append] at hgt
    rcases hgt with hgt | hgt
    · exact hP gt hgt
    · rw [List.mem_map] at hgt
      obtain ⟨g0, hg0, rfl⟩ := hgt
      obtain ⟨h1, h2⟩ := hC g0 hg0
      exact ⟨h1, by simp only [mapGate, List.length_map]; exact h2⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x hx
    have hWlen : ((⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).length = M := by
      show (P.foldl step x).length = M
      rw [len_foldl, hD x hx]
    have hr := hr_of L M K w ((⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x)
      (fun j => g j x) hWlen (hw x hx)
    obtain ⟨E', h1, h2, h3⟩ := main _ _ r K hr C.gates [] (by simp [K])
    simp only [List.append_nil] at h2 h3
    show ((P ++ C.gates.map (mapGate r)).foldl step x).getD (r C.output) false
      = (C.gates.foldl step (List.ofFn fun j => g j x)).getD C.output false
    rw [List.foldl_append]
    have hPw : P.foldl step x = (⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x := rfl
    rw [hPw, h2, h3]
    exact hr E' (by simp at h1; omega) C.output

theorem ti_aux : ∀ (k u : ℕ), (Finset.univ.sum fun i : Fin k =>
    if u.testBit (i : ℕ) = true then 2 ^ (i : ℕ) else 0) = u % 2 ^ k
  | 0, u => by simp [Nat.mod_one]
  | k + 1, u => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    have h1 : (u / 2 ^ k).testBit 0 = u.testBit (0 + k) := Nat.testBit_div_two_pow ..
    rw [Nat.zero_add] at h1
    rw [ti_aux k u, pow_succ, Nat.mod_mul, ← h1]
    rcases Nat.mod_two_eq_zero_or_one (u / 2 ^ k) with h | h <;> simp [h, Nat.testBit_zero]

theorem tidx (k u : ℕ) (h : u < 2 ^ k) :
    PEqualNP.MetaComplexity.tableIndex (fun i : Fin k => u.testBit (i : ℕ)) = u := by
  unfold PEqualNP.MetaComplexity.tableIndex
  rw [ti_aux]
  exact Nat.mod_eq_of_lt h

theorem getD_true_lt (l : List Bool) (i : ℕ) (h : l.getD i false = true) : i < l.length := by
  by_contra hc
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hc)] at h
  simp at h

theorem dt (c : Bool) : decide (c = true) = c := by cases c <;> rfl

theorem df (c : Bool) : decide (c = false) = !c := by cases c <;> rfl

def posW (k : ℕ) (wL wR : ℕ → Bool → ℕ) (t : ℕ) (b : Bool) : ℕ :=
  if t < k then wL t b else wR (t - k) b

def wW (k l : ℕ) (wL wR : ℕ → Bool → ℕ) (j : Fin ((k + l) + (k + l))) : ℕ :=
  if (j : ℕ) < k + l then posW k wL wR j true else posW k wL wR ((j : ℕ) - (k + l)) false

theorem wW_lo (k l : ℕ) (wL wR : ℕ → Bool → ℕ) (t : ℕ) (h : t < k + l)
    {h2 : t < (k + l) + (k + l)} : wW k l wL wR ⟨t, h2⟩ = posW k wL wR t true := by
  show (if t < k + l then posW k wL wR t true else posW k wL wR (t - (k + l)) false) = _
  rw [if_pos h]

theorem wW_hi (k l : ℕ) (wL wR : ℕ → Bool → ℕ) (t : ℕ)
    {h2 : k + l + t < (k + l) + (k + l)} : wW k l wL wR ⟨k + l + t, h2⟩ = posW k wL wR t false := by
  show (if k + l + t < k + l then posW k wL wR (k + l + t) true
    else posW k wL wR (k + l + t - (k + l)) false) = _
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem oneL {n m : ℕ} (u : Fin n) (v : Fin m) (j : ℕ) (hj : j < n) :
    (PEqualNP.Represents.oneEach u v).getD j false = decide (j = (u : ℕ)) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hj)]
  simp [List.getElem?_ofFn, hj, Fin.ext_iff]

theorem oneR {n m : ℕ} (u : Fin n) (v : Fin m) (j : ℕ) (hj : j < m) :
    (PEqualNP.Represents.oneEach u v).getD (n + j) false = decide (j = (v : ℕ)) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp [List.getElem?_ofFn, hj, Fin.ext_iff]

theorem oneLen {n m : ℕ} (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]

end PEqualNP.Outside.L_meta_9019

open PEqualNP.Outside.L_meta_9019 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9019 : ∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), PEqualNP.Represents.HasLitSize (k + l) (PEqualNP.Represents.adjFun A) s → PEqualNP.Represents.RepSizeAtMost A (s + 3 * 2 ^ k + 3 * 2 ^ l) := by
  intro k l s A hlit
  obtain ⟨C, hCm, hCs, hCf⟩ := hlit
  have hsrc : ∀ p : Fin (2 ^ k) × Fin (2 ^ l),
      (PEqualNP.Represents.oneEach p.1 p.2).length = 2 ^ k + 2 ^ l := fun p => oneLen p.1 p.2
  obtain ⟨eL, hmL, hlL, wL, hwL⟩ := dec (2 ^ k + 2 ^ l) (Fin (2 ^ k) × Fin (2 ^ l))
    (fun p => PEqualNP.Represents.oneEach p.1 p.2) hsrc k [] (fun j => j)
    (fun j hj => by simp only [List.length_nil, Nat.add_zero]; exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)) (fun p => (p.1 : ℕ)) (fun p => p.1.isLt)
    (fun p j hj => by
      show (PEqualNP.Represents.oneEach p.1 p.2).getD j false = decide (j = (p.1 : ℕ))
      exact oneL p.1 p.2 j hj)
  simp only [List.nil_append] at hwL
  obtain ⟨eR, hmR, hlR, wR, hwR⟩ := dec (2 ^ k + 2 ^ l) (Fin (2 ^ k) × Fin (2 ^ l))
    (fun p => PEqualNP.Represents.oneEach p.1 p.2) hsrc l eL (fun j => 2 ^ k + j)
    (fun j hj => by
      show 2 ^ k + j < 2 ^ k + 2 ^ l + eL.length
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) (Nat.le_add_right _ _)) (fun p => (p.2 : ℕ)) (fun p => p.2.isLt)
    (fun p j hj => by
      have h := run_prefix [] eL (PEqualNP.Represents.oneEach p.1 p.2) (2 ^ k + j)
        (by rw [hsrc, List.length_nil]; omega)
      rw [List.nil_append] at h
      show (run eL (PEqualNP.Represents.oneEach p.1 p.2)).getD (2 ^ k + j) false = _
      rw [h]
      exact oneR p.1 p.2 j hj)
  have hbL : ∀ i < k, ∀ b : Bool, wL i b < (2 ^ k + 2 ^ l) + eL.length := by
    intro i hi b
    have hu : (if b then 2 ^ i else 0) < 2 ^ k := by
      cases b
      · simp only [Bool.false_eq_true, if_false]; positivity
      · simp only [if_true]; exact Nat.pow_lt_pow_right (by norm_num) hi
    have h := hwL (⟨if b then 2 ^ i else 0, hu⟩, ⟨0, by positivity⟩) i hi b
    have htrue : decide ((if b then 2 ^ i else 0 : ℕ).testBit i = b) = true := by
      cases b <;> simp [Nat.testBit_two_pow_self]
    have h2 : (run eL (PEqualNP.Represents.oneEach
        (⟨if b then 2 ^ i else 0, hu⟩ : Fin (2 ^ k)) (⟨0, by positivity⟩ : Fin (2 ^ l)))).getD
        (wL i b) false = true := by
      exact h.trans htrue
    have h3 := getD_true_lt _ _ h2
    rwa [run_length, oneLen] at h3
  have hwL' : ∀ p : Fin (2 ^ k) × Fin (2 ^ l), ∀ i < k, ∀ b : Bool,
      (run (eL ++ eR) (PEqualNP.Represents.oneEach p.1 p.2)).getD (wL i b) false =
        decide ((p.1 : ℕ).testBit i = b) := by
    intro p i hi b
    rw [run_prefix eL eR _ _ (by rw [hsrc]; exact hbL i hi b)]
    exact hwL p i hi b
  have hmono : PEqualNP.MetaComplexity.Monotone2 (⟨eL ++ eR, 0⟩ : Circuit) := by
    intro g hg
    have hg' : g ∈ eL ++ eR := hg
    have hm : mono g := by
      rcases List.mem_append.1 hg' with h | h
      · exact hmL g h
      · exact hmR g h
    refine ⟨?_, hm.2⟩
    rcases hm.1 with h | h <;> simp [h]
  obtain ⟨C', hC'm, hC's, hC'e⟩ := compose (2 ^ k + 2 ^ l) ((k + l) + (k + l))
    (Set.range fun p : Fin (2 ^ k) × Fin (2 ^ l) => PEqualNP.Represents.oneEach p.1 p.2)
    (eL ++ eR) (wW k l wL wR)
    (fun j x => ((⟨eL ++ eR, 0⟩ : Circuit).wires x).getD (wW k l wL wR j) false) C
    (by rintro x ⟨p, rfl⟩; exact hsrc p) hmono hCm (fun x _ j => rfl)
  refine ⟨C', hC'm, ?_, ?_⟩
  · have h1 := hC's
    rw [List.length_append] at h1
    omega
  · intro u v
    rw [hC'e _ ⟨(u, v), rfl⟩]
    have hval : ∀ (t : ℕ), t < k + l → ∀ b : Bool,
        (run (eL ++ eR) (PEqualNP.Represents.oneEach u v)).getD (posW k wL wR t b) false =
          decide ((if t < k then (u : ℕ).testBit t else (v : ℕ).testBit (t - k)) = b) := by
      intro t ht b
      by_cases h : t < k
      · simp only [posW, if_pos h]; exact hwL' (u, v) t h b
      · simp only [posW, if_neg h]; exact hwR (u, v) (t - k) (by omega) b
    let x' : Fin (k + l) → Bool := fun i =>
      if (i : ℕ) < k then (u : ℕ).testBit i else (v : ℕ).testBit ((i : ℕ) - k)
    have hx : (List.ofFn fun j : Fin ((k + l) + (k + l)) =>
        ((⟨eL ++ eR, 0⟩ : Circuit).wires (PEqualNP.Represents.oneEach u v)).getD
          (wW k l wL wR j) false) = List.ofFn x' ++ List.ofFn fun i => !x' i := by
      rw [List.ofFn_add]
      congr 1
      · apply congrArg List.ofFn
        funext i
        show (run (eL ++ eR) (PEqualNP.Represents.oneEach u v)).getD
          (wW k l wL wR ⟨(i : ℕ), by omega⟩) false = x' i
        rw [wW_lo k l wL wR i i.isLt, hval i i.isLt true, dt]
      · apply congrArg List.ofFn
        funext i
        show (run (eL ++ eR) (PEqualNP.Represents.oneEach u v)).getD
          (wW k l wL wR ⟨k + l + (i : ℕ), by omega⟩) false = !x' i
        rw [wW_hi k l wL wR i, hval i i.isLt false, df]
    rw [hx, hCf x']
    unfold PEqualNP.Represents.adjFun
    have hl : (fun i : Fin k => x' (Fin.castAdd l i)) = fun i : Fin k => (u : ℕ).testBit (i : ℕ) := by
      funext i
      simp only [x', Fin.coe_castAdd, if_pos i.isLt]
    have hr : (fun j : Fin l => x' (Fin.natAdd k j)) = fun j : Fin l => (v : ℕ).testBit (j : ℕ) := by
      funext j
      simp only [x', Fin.coe_natAdd]
      rw [if_neg (by omega), Nat.add_sub_cancel_left]
    rw [hl, hr, tidx k u u.isLt, tidx l v v.isLt]
    congr 1
    · apply Fin.ext; simp [Nat.mod_eq_of_lt u.isLt]
    · apply Fin.ext; simp [Nat.mod_eq_of_lt v.isLt]
