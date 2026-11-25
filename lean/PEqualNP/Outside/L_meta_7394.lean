import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7394

def inc (a b : Fin 13) : Bool := [0, 1, 3, 9].contains ((a.val + 13 - b.val) % 13)

theorem inc_iff : ∀ a b : Fin 13,
    (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), a = b + d) ↔ inc a b = true := by decide

theorem inc_iff2 : ∀ a b : Fin 13,
    (((a - b : Fin 13) : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) ↔ inc a b = true := by decide

def missB (f : Fin 13 → Bool) (w : Fin 13) : Bool :=
  (List.finRange 13).all fun p => !(f p && inc p w)

def h1B (f : Fin 13 → Bool) : Bool :=
  (List.finRange 13).all fun v => f v || (List.finRange 13).any fun w => missB f w && inc v w

def h2B (f : Fin 13 → Bool) : Bool :=
  (List.finRange 13).any (fun w => (List.finRange 13).all fun p => !f p || inc p w) ||
  (List.finRange 13).any (fun v => (List.finRange 13).all fun w => !missB f w || inc v w)

def h4B (f : Fin 13 → Bool) : Bool :=
  decide (14 * (List.finRange 13).countP f + (List.finRange 13).countP (missB f) ∈
    [(13 : ℕ), (23 : ℕ), (34 : ℕ), (45 : ℕ), (86 : ℕ), (127 : ℕ), (182 : ℕ)])

def chkF (f : Fin 13 → Bool) : Bool := h4B f == (h1B f && h2B f)

def fX (X : Finset (Fin 13)) (i : Fin 13) : Bool := decide (i ∈ X)

theorem fX_eq (X : Finset (Fin 13)) (i : Fin 13) : fX X i = true ↔ i ∈ X := by simp [fX]

theorem hmiss (X : Finset (Fin 13)) (w : Fin 13) :
    missB (fX X) w = true ↔ ∀ p ∈ X, ¬ inc p w = true := by
  simp [missB, fX]
  exact forall_congr' fun p => by by_cases hp : p ∈ X <;> simp [hp]
theorem hA (X : Finset (Fin 13)) : h1B (fX X) = true ↔
    ∀ v, v ∉ X → ∃ w, (∀ p ∈ X, ¬ inc p w = true) ∧ inc v w = true := by
  simp only [h1B, List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true,
    List.any_eq_true, true_and, Bool.and_eq_true, hmiss, fX_eq]
  exact forall_congr' fun v => or_iff_not_imp_left

theorem hB (X : Finset (Fin 13)) : h2B (fX X) = true ↔
    ((∃ w, ∀ p ∈ X, inc p w = true) ∨
      ∃ v, ∀ w, (∀ p ∈ X, ¬ inc p w = true) → inc v w = true) := by
  have e1 : ∀ w, ((List.finRange 13).all fun p => !fX X p || inc p w) = true ↔
      ∀ p ∈ X, inc p w = true := by
    intro w
    simp only [List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true,
      Bool.not_eq_true']
    refine forall_congr' fun p => ?_
    rw [← Bool.not_eq_true, fX_eq, or_iff_not_imp_left, not_not]
  have e2 : ∀ v, ((List.finRange 13).all fun w => !missB (fX X) w || inc v w) = true ↔
      ∀ w, (∀ p ∈ X, ¬ inc p w = true) → inc v w = true := by
    intro v
    simp only [List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true,
      Bool.not_eq_true']
    refine forall_congr' fun w => ?_
    rw [← Bool.not_eq_true, hmiss, or_iff_not_imp_left, not_not]
  simp only [h2B, Bool.or_eq_true, List.any_eq_true, List.mem_finRange, true_and, e1, e2]

theorem hcard (X : Finset (Fin 13)) : X.card = (List.finRange 13).countP (fX X) := by
  rw [List.countP_eq_length_filter]
  have e : X = ((List.finRange 13).filter (fX X)).toFinset := by
    ext i
    simp [fX]
  conv_lhs => rw [e]
  exact List.toFinset_card_of_nodup ((List.nodup_finRange 13).filter _)

theorem hcnt (X : Finset (Fin 13)) :
    List.countP (fun (x5 : Fin 13) => decide (∀ x6 ∈ X, ↑(x6 - x5) ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]))
      (List.finRange 13) = (List.finRange 13).countP (missB (fX X)) := by
  apply List.countP_congr
  intro w _
  rw [decide_eq_true_iff, hmiss]
  simp only [inc_iff2]

theorem key0 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, false, false, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key1 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, false, false, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key2 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, false, true, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key3 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, false, true, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key4 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, true, false, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key5 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, true, false, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key6 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, true, true, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key7 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, true, true, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key8 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, false, false, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key9 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, false, false, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key10 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, false, true, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key11 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, false, true, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key12 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, true, false, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key13 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, true, false, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key14 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, true, true, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key15 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, true, true, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  intro b0 b1 b2 b3
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3
  exacts [key0, key1, key2, key3, key4, key5, key6, key7, key8, key9, key10, key11, key12, key13,
    key14, key15]

theorem keyX (X : Finset (Fin 13)) : chkF (fX X) = true := by
  have h := key (fX X 0) (fX X 1) (fX X 2) (fX X 3) (fX X 4) (fX X 5) (fX X 6) (fX X 7) (fX X 8)
    (fX X 9) (fX X 10) (fX X 11) (fX X 12)
  have e : (fun i : Fin 13 => [fX X 0, fX X 1, fX X 2, fX X 3, fX X 4, fX X 5, fX X 6, fX X 7,
      fX X 8, fX X 9, fX X 10, fX X 11, fX X 12].getD i.val false) = fX X := by
    funext i
    fin_cases i <;> rfl
  rwa [e] at h

end PEqualNP.Outside.L_meta_7394

open PEqualNP.Outside.L_meta_7394 in
theorem PEqualNP.Outside.L_meta_7394 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => (14 : ℕ) * x4.card + List.countP (fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, ↑(x6 - x5) ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])) (List.finRange (13 : ℕ)) ∈ [(13 : ℕ), (23 : ℕ), (34 : ℕ), (45 : ℕ), (86 : ℕ), (127 : ℕ), (182 : ℕ)]; ∀ (x5 : Finset (Fin (13 : ℕ))), x4 x5 ↔ (∀ x6 ∉ x5, ∃ (x8 : Fin (13 : ℕ)), x3 x5 x8 ∧ x2 x6 x8) ∧ ((∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x5, x2 x7 x6) ∨ ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x3 x5 x7 → x2 x6 x7) := by
  intro x1 x2 x3 x4 X
  have hx2 : ∀ p l, x2 p l ↔ inc p l = true := fun p l => inc_iff p l
  have hf : h4B (fX X) = (h1B (fX X) && h2B (fX X)) := by
    have := keyX X
    simpa [chkF] using this
  show 14 * X.card + _ ∈ _ ↔ _
  rw [hcard, hcnt]
  have e4 : (14 * (List.finRange 13).countP (fX X) + (List.finRange 13).countP (missB (fX X)) ∈
      [(13 : ℕ), (23 : ℕ), (34 : ℕ), (45 : ℕ), (86 : ℕ), (127 : ℕ), (182 : ℕ)]) ↔ h4B (fX X) = true :=
    (decide_eq_true_iff).symm
  rw [e4, hf, Bool.and_eq_true, hA, hB]
  simp only [x3, hx2]
