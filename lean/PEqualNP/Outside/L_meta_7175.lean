import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7175

def I (a l : Fin 13) : Prop := ((a : ℕ) + (l : ℕ)) % 13 ∈ [0, 1, 3, 9]

instance (a l : Fin 13) : Decidable (I a l) := by unfold I; infer_instance

def lm (l : Fin 13) : ℕ :=
  [523, 4357, 6274, 3137, 5664, 2832, 1416, 708, 354, 177, 4184, 2092, 1046].getD l 0

theorem lm_bit : ∀ a l : Fin 13, (lm l).testBit a = decide (I a l) := by decide

theorem lm_lt : ∀ l : Fin 13, lm l < 2 ^ 13 := by decide

def plT (a : Fin 13) : List ℕ :=
  [[523, 4357, 3137, 177], [523, 6274, 354, 1046], [4357, 708, 2092, 1046], [523, 1416, 4184, 2092],
   [2832, 177, 4184, 1046], [5664, 354, 177, 2092], [3137, 708, 354, 4184], [6274, 1416, 708, 177],
   [4357, 2832, 1416, 354], [523, 5664, 2832, 708], [3137, 5664, 1416, 1046],
   [6274, 3137, 2832, 2092], [4357, 6274, 5664, 4184]].getD a []

theorem plT_eq : ∀ a : Fin 13, plT a = ((List.finRange 13).filter fun l => decide (I a l)).map lm := by
  decide

def closedB (m : ℕ) : Bool :=
  (List.finRange 13).all fun a => m.testBit a || (plT a).any fun M => m &&& M == 0

set_option maxRecDepth 100000 in
theorem count : ((List.range 8192).filter closedB).length = 704 := by
  decide +kernel

def dec (m : ℕ) : Fin 13 → Bool := fun a => m.testBit a

def enc (X : Fin 13 → Bool) : Fin 26 → Bool := fun i =>
  if h : (i : ℕ) < 13 then X ⟨i, h⟩
  else decide (∀ a : Fin 13, X a = true → ¬ I a ⟨(i : ℕ) - 13, by omega⟩)

def pairIn (a l : Fin 13) : Fin 26 → Bool := fun i => decide ((i : ℕ) = a ∨ (i : ℕ) = 13 + l)

def T1 : List (Fin 26 → Bool) :=
  (List.finRange 13).flatMap fun a => ((List.finRange 13).filter fun l => decide (I a l)).map
    fun l => pairIn a l

theorem T1_len : T1.length = 52 := by
  decide +kernel

def T2 : List (Fin 26 → Bool) := ((List.range 8192).filter closedB).map fun m => enc (dec m)

def encode : (n : ℕ) → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n + 1, X => Nat.bit (X 0) (encode n (fun a => X a.succ))

theorem encode_bit : ∀ (n : ℕ) (X : Fin n → Bool) (a : Fin n), (encode n X).testBit a = X a
  | 0, _, a => a.elim0
  | n + 1, X, a => by
    refine Fin.cases ?_ (fun b => ?_) a
    · simp [encode, Nat.testBit_bit_zero]
    · rw [Fin.val_succ]
      simp only [encode]
      rw [Nat.testBit_bit_succ, encode_bit n]

theorem encode_lt : ∀ (n : ℕ) (X : Fin n → Bool), encode n X < 2 ^ n
  | 0, _ => by simp [encode]
  | n + 1, X => by
    have h := encode_lt n (fun a => X a.succ)
    simp only [encode]
    rw [Nat.bit_val, pow_succ]
    cases X 0 <;> simp <;> omega

end PEqualNP.Outside.L_meta_7175

theorem PEqualNP.Outside.L_meta_7175 : have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∃ (x2 : Fin (756 : ℕ) → Fin (26 : ℕ) → Bool), ∀ (x3 : Fin (26 : ℕ) → Bool), Minimal x1 x3 ∨ Maximal (fun (x4 : Fin (26 : ℕ) → Bool) => ¬x1 x4) x3 → ∃ (x5 : Fin (756 : ℕ)), x2 x5 = x3 := by
  intro x1
  open PEqualNP.Outside.L_meta_7175 in
  have hlen : (T1 ++ T2).length = 756 := by
    rw [List.length_append, T1_len, T2, List.length_map, count]
  open PEqualNP.Outside.L_meta_7175 in
  have hmem : ∀ x : Fin 26 → Bool, Minimal x1 x ∨ Maximal (fun x4 => ¬x1 x4) x → x ∈ T1 ++ T2 := by
    intro x hx
    rcases hx with hmin | hmax
    · obtain ⟨⟨a, l, hI, ha, hl⟩, hm⟩ := hmin
      have hy : x1 (pairIn a l) := ⟨a, l, hI, by simp [pairIn], by
        simp only [pairIn]; exact decide_eq_true (Or.inr (Fin.val_natAdd 13 l))⟩
      have hle : pairIn a l ≤ x := by
        rw [Pi.le_def]
        intro i
        by_cases h : (i : ℕ) = a ∨ (i : ℕ) = 13 + l
        · rcases h with h | h
          · have e : i = Fin.castAdd 13 a := Fin.ext (by simp [h])
            rw [e, ha]
            exact le_top
          · have e : i = Fin.natAdd 13 l := Fin.ext (by simp [h]; omega)
            rw [e, hl]
            exact le_top
        · have : pairIn a l i = false := by simp [pairIn, h]
          rw [this]
          exact bot_le
      have hxe : x = pairIn a l := le_antisymm (hm hy hle) hle
      apply List.mem_append_left
      rw [T1, List.mem_flatMap]
      refine ⟨a, List.mem_finRange a, ?_⟩
      rw [List.mem_map]
      refine ⟨l, ?_, hxe.symm⟩
      rw [List.mem_filter]
      exact ⟨List.mem_finRange l, decide_eq_true hI⟩
    · obtain ⟨hn, hM⟩ := hmax
      have hcn : ∀ (a l : Fin 13), Fin.castAdd 13 a ≠ Fin.natAdd 13 l := by
        intro a l e
        have := congrArg Fin.val e
        simp at this
        omega
      have hlines : ∀ l : Fin 13, x (Fin.natAdd 13 l) = true ↔
          ∀ a : Fin 13, x (Fin.castAdd 13 a) = true → ¬ I a l := by
        intro l
        constructor
        · intro hl a ha hI
          exact hn ⟨a, l, hI, ha, hl⟩
        · intro h
          by_contra hl'
          have hy : ¬ x1 (Function.update x (Fin.natAdd 13 l) true) := by
            rintro ⟨a', l', hI', ha', hl''⟩
            rw [Function.update_of_ne (hcn a' l)] at ha'
            by_cases hll : l' = l
            · subst hll
              exact h a' ha' hI'
            · have hne2 : Fin.natAdd 13 l' ≠ Fin.natAdd 13 l := by
                intro e
                apply hll
                ext
                have := congrArg Fin.val e
                simp at this
                omega
              rw [Function.update_of_ne hne2] at hl''
              exact hn ⟨a', l', hI', ha', hl''⟩
          have hle : x ≤ Function.update x (Fin.natAdd 13 l) true := by
            rw [Pi.le_def]
            intro i
            by_cases hi : i = Fin.natAdd 13 l
            · subst hi
              simp
            · rw [Function.update_of_ne hi]
          have h2 := hM hy hle (Fin.natAdd 13 l)
          simp only [Function.update_self] at h2
          exact hl' (top_le_iff.mp h2)
      have hpts : ∀ a : Fin 13, x (Fin.castAdd 13 a) = false →
          ∃ l : Fin 13, I a l ∧ ∀ a' : Fin 13, x (Fin.castAdd 13 a') = true → ¬ I a' l := by
        intro a ha
        have hle : x ≤ Function.update x (Fin.castAdd 13 a) true := by
          rw [Pi.le_def]
          intro i
          by_cases hi : i = Fin.castAdd 13 a
          · subst hi
            simp
          · rw [Function.update_of_ne hi]
        have hy : x1 (Function.update x (Fin.castAdd 13 a) true) := by
          by_contra hy
          have h2 := hM hy hle (Fin.castAdd 13 a)
          simp only [Function.update_self] at h2
          rw [top_le_iff.mp h2] at ha
          exact Bool.noConfusion ha
        obtain ⟨a', l, hI, ha', hl⟩ := hy
        have hl' : x (Fin.natAdd 13 l) = true := by
          rwa [Function.update_of_ne (fun e => hcn a l e.symm)] at hl
        by_cases haa : a' = a
        · subst haa
          exact ⟨l, hI, fun a'' h'' hI'' => hn ⟨a'', l, hI'', h'', hl'⟩⟩
        · have hne : Fin.castAdd 13 a' ≠ Fin.castAdd 13 a := by
            intro e
            apply haa
            ext
            have := congrArg Fin.val e
            simpa using this
          rw [Function.update_of_ne hne] at ha'
          exact absurd ⟨a', l, hI, ha', hl'⟩ hn
      set P : Fin 13 → Bool := fun a => x (Fin.castAdd 13 a) with hP
      have hxe : x = enc P := by
        funext i
        unfold enc
        split_ifs with h
        · rw [hP]
          congr 1
        · have hi26 := i.isLt
          have e : i = Fin.natAdd 13 (⟨(i : ℕ) - 13, by omega⟩ : Fin 13) :=
            Fin.ext (by rw [Fin.val_natAdd]; show (i : ℕ) = 13 + ((i : ℕ) - 13); omega)
          have hl := hlines (⟨(i : ℕ) - 13, by omega⟩ : Fin 13)
          rw [← e] at hl
          rw [Bool.eq_iff_iff, hl, decide_eq_true_iff]
      have hdec : dec (encode 13 P) = P := funext fun a => encode_bit 13 P a
      have hcl : closedB (encode 13 P) = true := by
        unfold closedB
        rw [List.all_eq_true]
        intro a _
        rw [Bool.or_eq_true, List.any_eq_true]
        have hb : (encode 13 P).testBit a = P a := encode_bit 13 P a
        cases hPa : P a
        · right
          obtain ⟨l, hI, hl⟩ := hpts a hPa
          refine ⟨lm l, ?_, ?_⟩
          · rw [plT_eq, List.mem_map]
            exact ⟨l, List.mem_filter.mpr ⟨List.mem_finRange l, decide_eq_true hI⟩, rfl⟩
          · rw [beq_iff_eq]
            apply Nat.eq_of_testBit_eq
            intro i
            rw [Nat.testBit_land, Nat.zero_testBit]
            by_cases hi : i < 13
            · have h1 : (encode 13 P).testBit i = P ⟨i, hi⟩ := encode_bit 13 P ⟨i, hi⟩
              have h2 : (lm l).testBit i = decide (I ⟨i, hi⟩ l) := lm_bit ⟨i, hi⟩ l
              rw [h1, h2]
              cases hp : P ⟨i, hi⟩
              · simp
              · have := hl ⟨i, hi⟩ hp
                simp [this]
            · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (lm_lt l)
                (Nat.pow_le_pow_right (by norm_num) (by omega)))]
              simp
        · left
          rw [hb, hPa]
      apply List.mem_append_right
      rw [T2, List.mem_map]
      refine ⟨encode 13 P, ?_, ?_⟩
      · rw [List.mem_filter]
        exact ⟨List.mem_range.mpr (encode_lt 13 P), hcl⟩
      · rw [hdec, ← hxe]
  refine ⟨fun i => (PEqualNP.Outside.L_meta_7175.T1 ++ PEqualNP.Outside.L_meta_7175.T2).getD i
    (fun _ => false), ?_⟩
  intro x hx
  obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem (hmem x hx)
  refine ⟨⟨k, by rw [hlen] at hk; exact hk⟩, ?_⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact hkx
