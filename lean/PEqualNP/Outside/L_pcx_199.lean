import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_199

open PEqualNP.ProofComplexity

abbrev VV : Type := Fin 5 × Fin 4

theorem memD {α : Type} (l : List α) (d : α) (i : ℕ) (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

-- a step of a Res(2) certificate, newest first; premises are indices into the tail
inductive St (V : Type) where
  | ax : Clause V → St V
  | cut : KLine V → ℕ → ℕ → KTerm V → St V
  | andI : KLine V → ℕ → ℕ → KTerm V → KTerm V → St V

def St.line {V : Type} [DecidableEq V] : St V → KLine V
  | .ax C => kLineOfClause C
  | .cut R _ _ _ => R
  | .andI R _ _ _ _ => R

def chk {V : Type} [DecidableEq V] (ax : Clause V → Bool) : List (St V) → Bool
  | [] => true
  | .ax C :: t => ax C && decide (∀ T ∈ kLineOfClause C, T.card ≤ 2) && chk ax t
  | .cut R i j T :: t =>
      decide (i < t.length) && decide (j < t.length) &&
      decide (T ∈ (t.map St.line).getD i ∅ ∧ T.Nonempty ∧
        (∀ l ∈ T, ({(l.1, !l.2)} : KTerm V) ∈ (t.map St.line).getD j ∅) ∧
        R = ((t.map St.line).getD i ∅).erase T ∪
          ((t.map St.line).getD j ∅ \ T.image (fun l => ({(l.1, !l.2)} : KTerm V)))) &&
      chk ax t
  | .andI R i j T1 T2 :: t =>
      decide (i < t.length) && decide (j < t.length) &&
      decide (T1 ∈ (t.map St.line).getD i ∅ ∧ T2 ∈ (t.map St.line).getD j ∅ ∧
        R = (((t.map St.line).getD i ∅).erase T1 ∪ ((t.map St.line).getD j ∅).erase T2) ∪ {T1 ∪ T2}) &&
      decide (∀ T ∈ R, T.card ≤ 2) && chk ax t

theorem chk_sound {V : Type} [DecidableEq V] (F : Set (Clause V)) (ax : Clause V → Bool)
    (hax : ∀ C, ax C = true → C ∈ F) :
    ∀ l, chk ax l = true → IsResKDerivation 2 ((fun C => kLineOfClause C) '' F) (l.map St.line)
  | [], _ => IsResKDerivation.nil
  | .ax C :: t, h => by
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact IsResKDerivation.ax (chk_sound F ax hax t h.2) ⟨C, hax C h.1.1, rfl⟩ h.1.2
  | .cut R i j T :: t, h => by
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, h1, h2, h3, h4⟩, ht⟩ := h
    exact IsResKDerivation.cut (chk_sound F ax hax t ht) (memD _ _ _ (by simpa using hi))
      (memD _ _ _ (by simpa using hj)) ⟨T, h1, h2, h3, h4⟩
  | .andI R i j T1 T2 :: t, h => by
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hi, hj⟩, h1, h2, h3⟩, hc⟩, ht⟩ := h
    exact IsResKDerivation.andIntro (chk_sound F ax hax t ht) (memD _ _ _ (by simpa using hi))
      (memD _ _ _ (by simpa using hj)) ⟨T1, T2, h1, h2, h3⟩ hc

def axPHP (m n : ℕ) (C : Clause (Fin m × Fin n)) : Bool :=
  decide (∃ i : Fin m, C = Finset.univ.image (fun j : Fin n => ((i, j), true))) ||
  decide (∃ i : Fin m, ∃ i' : Fin m, ∃ j : Fin n, i ≠ i' ∧ C = {((i, j), false), ((i', j), false)})

theorem axPHP_sound (m n : ℕ) : ∀ C, axPHP m n C = true → C ∈ PHP m n := by
  intro C h
  simp only [axPHP, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨i, hi⟩ | ⟨i, i', j, hne, hC⟩
  · exact Or.inl ⟨i, hi⟩
  · exact Or.inr ⟨i, i', j, hne, hC⟩

def cert : List (St VV) := [
  St.cut ∅ 8 0 {((4, 3), true)},
  St.cut {{((4, 3), false)}} 1 0 {((3, 3), true)},
  St.ax {((3, 3), false), ((4, 3), false)},
  St.cut {{((3, 3), true)}, {((4, 3), false)}} 1 0 {((2, 3), true)},
  St.ax {((2, 3), false), ((4, 3), false)},
  St.cut {{((2, 3), true)}, {((3, 3), true)}, {((4, 3), false)}} 1 0 {((1, 3), true)},
  St.ax {((1, 3), false), ((4, 3), false)},
  St.cut {{((1, 3), true)}, {((2, 3), true)}, {((3, 3), true)}, {((4, 3), false)}} 29 0 {((0, 3), true)},
  St.ax {((0, 3), false), ((4, 3), false)},
  St.cut {{((4, 3), true)}} 8 0 {((4, 2), true)},
  St.cut {{((4, 2), false)}} 1 0 {((3, 2), true)},
  St.ax {((3, 2), false), ((4, 2), false)},
  St.cut {{((3, 2), true)}, {((4, 2), false)}} 1 0 {((2, 2), true)},
  St.ax {((2, 2), false), ((4, 2), false)},
  St.cut {{((2, 2), true)}, {((3, 2), true)}, {((4, 2), false)}} 1 0 {((1, 2), true)},
  St.ax {((1, 2), false), ((4, 2), false)},
  St.cut {{((1, 2), true)}, {((2, 2), true)}, {((3, 2), true)}, {((4, 2), false)}} 29 0 {((0, 2), true)},
  St.ax {((0, 2), false), ((4, 2), false)},
  St.cut {{((4, 2), true)}, {((4, 3), true)}} 8 0 {((4, 1), true)},
  St.cut {{((4, 1), false)}} 1 0 {((3, 1), true)},
  St.ax {((3, 1), false), ((4, 1), false)},
  St.cut {{((3, 1), true)}, {((4, 1), false)}} 1 0 {((2, 1), true)},
  St.ax {((2, 1), false), ((4, 1), false)},
  St.cut {{((2, 1), true)}, {((3, 1), true)}, {((4, 1), false)}} 1 0 {((1, 1), true)},
  St.ax {((1, 1), false), ((4, 1), false)},
  St.cut {{((1, 1), true)}, {((2, 1), true)}, {((3, 1), true)}, {((4, 1), false)}} 29 0 {((0, 1), true)},
  St.ax {((0, 1), false), ((4, 1), false)},
  St.cut {{((4, 1), true)}, {((4, 2), true)}, {((4, 3), true)}} 8 0 {((4, 0), true)},
  St.cut {{((4, 0), false)}} 1 0 {((3, 0), true)},
  St.ax {((3, 0), false), ((4, 0), false)},
  St.cut {{((3, 0), true)}, {((4, 0), false)}} 1 0 {((2, 0), true)},
  St.ax {((2, 0), false), ((4, 0), false)},
  St.cut {{((2, 0), true)}, {((3, 0), true)}, {((4, 0), false)}} 1 0 {((1, 0), true)},
  St.ax {((1, 0), false), ((4, 0), false)},
  St.cut {{((1, 0), true)}, {((2, 0), true)}, {((3, 0), true)}, {((4, 0), false)}} 33 0 {((0, 0), true)},
  St.ax {((0, 0), false), ((4, 0), false)},
  St.ax {((4, 0), true), ((4, 1), true), ((4, 2), true), ((4, 3), true)},
  St.cut {{((0, 3), true)}, {((1, 3), true)}, {((2, 3), true)}, {((3, 3), true)}} 2 0 {((3, 2), true)},
  St.cut {{((0, 3), true)}, {((1, 3), true)}, {((2, 3), true)}, {((3, 2), false)}} 38 0 {((1, 2), false), ((2, 2), false)},
  St.cut {{((0, 3), true)}, {((1, 2), true)}, {((1, 3), true)}, {((2, 2), true)}, {((2, 3), true)}, {((3, 2), false)}} 50 41 {((0, 2), true)},
  St.cut {{((0, 3), true)}, {((1, 3), true)}, {((2, 3), true)}, {((3, 2), true)}, {((3, 3), true)}} 2 0 {((3, 1), true)},
  St.cut {{((0, 3), true)}, {((1, 3), true)}, {((2, 3), true)}, {((3, 1), false)}} 0 42 {((2, 1), true)},
  St.cut {{((0, 3), true)}, {((1, 3), true)}, {((2, 1), true)}, {((2, 3), true)}, {((3, 1), false)}} 43 50 {((0, 1), false), ((1, 1), false)},
  St.cut {{((0, 3), true)}, {((1, 3), true)}, {((2, 3), true)}, {((3, 1), true)}, {((3, 2), true)}, {((3, 3), true)}} 45 0 {((3, 0), true)},
  St.cut {{((0, 3), true)}, {((1, 3), true)}, {((2, 3), true)}, {((3, 0), false)}} 18 0 {((1, 0), false), ((2, 0), false)},
  St.cut {{((0, 3), true)}, {((1, 0), true)}, {((1, 3), true)}, {((2, 0), true)}, {((2, 3), true)}, {((3, 0), false)}} 58 21 {((0, 0), true)},
  St.cut {{((0, 2), true)}, {((1, 2), true)}, {((2, 2), true)}, {((3, 2), true)}} 2 0 {((3, 3), true)},
  St.cut {{((0, 2), true)}, {((1, 2), true)}, {((2, 2), true)}, {((3, 3), false)}} 0 22 {((2, 3), true)},
  St.cut {{((0, 2), true)}, {((1, 2), true)}, {((2, 2), true)}, {((2, 3), true)}, {((3, 3), false)}} 23 41 {((0, 3), false), ((1, 3), false)},
  St.cut {{((0, 2), true)}, {((1, 2), true)}, {((2, 2), true)}, {((3, 2), true)}, {((3, 3), true)}} 2 0 {((3, 1), true)},
  St.cut {{((0, 2), true)}, {((1, 2), true)}, {((2, 2), true)}, {((3, 1), false)}} 0 33 {((2, 1), true)},
  St.cut {{((0, 2), true)}, {((1, 2), true)}, {((2, 1), true)}, {((2, 2), true)}, {((3, 1), false)}} 34 44 {((0, 1), false), ((1, 1), false)},
  St.cut {{((0, 2), true)}, {((1, 2), true)}, {((2, 2), true)}, {((3, 1), true)}, {((3, 2), true)}, {((3, 3), true)}} 36 0 {((3, 0), true)},
  St.cut {{((0, 2), true)}, {((1, 2), true)}, {((2, 2), true)}, {((3, 0), false)}} 9 0 {((1, 0), false), ((2, 0), false)},
  St.cut {{((0, 2), true)}, {((1, 0), true)}, {((1, 2), true)}, {((2, 0), true)}, {((2, 2), true)}, {((3, 0), false)}} 53 12 {((0, 0), true)},
  St.cut {{((0, 1), true)}, {((1, 1), true)}, {((2, 1), true)}, {((3, 1), true)}} 2 0 {((3, 3), true)},
  St.cut {{((0, 1), true)}, {((1, 1), true)}, {((2, 1), true)}, {((3, 3), false)}} 0 13 {((2, 3), true)},
  St.cut {{((0, 1), true)}, {((1, 1), true)}, {((2, 1), true)}, {((2, 3), true)}, {((3, 3), false)}} 14 35 {((0, 3), false), ((1, 3), false)},
  St.cut {{((0, 1), true)}, {((1, 1), true)}, {((2, 1), true)}, {((3, 1), true)}, {((3, 3), true)}} 2 0 {((3, 2), true)},
  St.cut {{((0, 1), true)}, {((1, 1), true)}, {((2, 1), true)}, {((3, 2), false)}} 17 0 {((1, 2), false), ((2, 2), false)},
  St.cut {{((0, 1), true)}, {((1, 1), true)}, {((1, 2), true)}, {((2, 1), true)}, {((2, 2), true)}, {((3, 2), false)}} 35 20 {((0, 2), true)},
  St.cut {{((0, 1), true)}, {((1, 1), true)}, {((2, 1), true)}, {((3, 1), true)}, {((3, 2), true)}, {((3, 3), true)}} 27 0 {((3, 0), true)},
  St.cut {{((0, 1), true)}, {((1, 1), true)}, {((2, 1), true)}, {((3, 0), false)}} 0 3 {((1, 0), false), ((2, 0), false)},
  St.andI {{((1, 0), false), ((2, 0), false)}, {((3, 0), false)}} 1 0 {((1, 0), false)} {((2, 0), false)},
  St.ax {((2, 0), false), ((3, 0), false)},
  St.ax {((1, 0), false), ((3, 0), false)},
  St.cut {{((0, 1), true)}, {((1, 0), true)}, {((1, 1), true)}, {((2, 0), true)}, {((2, 1), true)}, {((3, 0), false)}} 48 0 {((0, 0), true)},
  St.ax {((0, 0), false), ((3, 0), false)},
  St.cut {{((0, 0), true)}, {((1, 0), true)}, {((2, 0), true)}, {((3, 0), true)}} 6 0 {((3, 3), true)},
  St.cut {{((0, 0), true)}, {((1, 0), true)}, {((2, 0), true)}, {((3, 3), false)}} 1 0 {((2, 3), true)},
  St.ax {((2, 3), false), ((3, 3), false)},
  St.cut {{((0, 0), true)}, {((1, 0), true)}, {((2, 0), true)}, {((2, 3), true)}, {((3, 3), false)}} 0 32 {((0, 3), false), ((1, 3), false)},
  St.andI {{((0, 3), false), ((1, 3), false)}, {((3, 3), false)}} 1 0 {((0, 3), false)} {((1, 3), false)},
  St.ax {((1, 3), false), ((3, 3), false)},
  St.ax {((0, 3), false), ((3, 3), false)},
  St.cut {{((0, 0), true)}, {((1, 0), true)}, {((2, 0), true)}, {((3, 0), true)}, {((3, 3), true)}} 6 0 {((3, 2), true)},
  St.cut {{((0, 0), true)}, {((1, 0), true)}, {((2, 0), true)}, {((3, 2), false)}} 0 3 {((1, 2), false), ((2, 2), false)},
  St.andI {{((1, 2), false), ((2, 2), false)}, {((3, 2), false)}} 1 0 {((1, 2), false)} {((2, 2), false)},
  St.ax {((2, 2), false), ((3, 2), false)},
  St.ax {((1, 2), false), ((3, 2), false)},
  St.cut {{((0, 0), true)}, {((1, 0), true)}, {((1, 2), true)}, {((2, 0), true)}, {((2, 2), true)}, {((3, 2), false)}} 27 0 {((0, 2), true)},
  St.ax {((0, 2), false), ((3, 2), false)},
  St.cut {{((0, 0), true)}, {((1, 0), true)}, {((2, 0), true)}, {((3, 0), true)}, {((3, 2), true)}, {((3, 3), true)}} 6 0 {((3, 1), true)},
  St.cut {{((0, 0), true)}, {((1, 0), true)}, {((2, 0), true)}, {((3, 1), false)}} 1 0 {((2, 1), true)},
  St.ax {((2, 1), false), ((3, 1), false)},
  St.cut {{((0, 0), true)}, {((1, 0), true)}, {((2, 0), true)}, {((2, 1), true)}, {((3, 1), false)}} 0 29 {((0, 1), false), ((1, 1), false)},
  St.andI {{((0, 1), false), ((1, 1), false)}, {((3, 1), false)}} 1 0 {((0, 1), false)} {((1, 1), false)},
  St.ax {((1, 1), false), ((3, 1), false)},
  St.ax {((0, 1), false), ((3, 1), false)},
  St.ax {((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)},
  St.cut {{((0, 2), true)}, {((0, 3), true)}, {((1, 2), true)}, {((1, 3), true)}, {((2, 2), true)}, {((2, 3), true)}} 1 0 {((2, 1), true)},
  St.cut {{((0, 2), true)}, {((0, 3), true)}, {((1, 2), true)}, {((1, 3), true)}, {((2, 1), false)}} 20 34 {((0, 1), false), ((1, 1), false)},
  St.cut {{((0, 2), true)}, {((0, 3), true)}, {((1, 2), true)}, {((1, 3), true)}, {((2, 1), true)}, {((2, 2), true)}, {((2, 3), true)}} 6 36 {((0, 0), false), ((1, 0), false)},
  St.cut {{((0, 1), true)}, {((0, 3), true)}, {((1, 1), true)}, {((1, 3), true)}, {((2, 1), true)}, {((2, 3), true)}} 1 0 {((2, 2), true)},
  St.cut {{((0, 1), true)}, {((0, 3), true)}, {((1, 1), true)}, {((1, 3), true)}, {((2, 2), false)}} 27 31 {((0, 2), false), ((1, 2), false)},
  St.cut {{((0, 1), true)}, {((0, 3), true)}, {((1, 1), true)}, {((1, 3), true)}, {((2, 1), true)}, {((2, 2), true)}, {((2, 3), true)}} 3 36 {((0, 0), false), ((1, 0), false)},
  St.cut {{((0, 1), true)}, {((0, 2), true)}, {((1, 1), true)}, {((1, 2), true)}, {((2, 1), true)}, {((2, 2), true)}} 1 0 {((2, 3), true)},
  St.cut {{((0, 1), true)}, {((0, 2), true)}, {((1, 1), true)}, {((1, 2), true)}, {((2, 3), false)}} 19 28 {((0, 3), false), ((1, 3), false)},
  St.cut {{((0, 1), true)}, {((0, 2), true)}, {((1, 1), true)}, {((1, 2), true)}, {((2, 1), true)}, {((2, 2), true)}, {((2, 3), true)}} 0 36 {((0, 0), false), ((1, 0), false)},
  St.andI {{((0, 0), false), ((1, 0), false)}, {((2, 1), true)}, {((2, 2), true)}, {((2, 3), true)}} 1 0 {((0, 0), false)} {((1, 0), false)},
  St.cut {{((1, 0), false)}, {((2, 1), true)}, {((2, 2), true)}, {((2, 3), true)}} 24 1 {((2, 0), true)},
  St.cut {{((0, 0), false)}, {((2, 1), true)}, {((2, 2), true)}, {((2, 3), true)}} 23 1 {((2, 0), true)},
  St.ax {((1, 0), false), ((2, 0), false)},
  St.ax {((0, 0), false), ((2, 0), false)},
  St.cut {{((0, 0), true)}, {((0, 3), true)}, {((1, 0), true)}, {((1, 3), true)}, {((2, 0), true)}, {((2, 3), true)}} 1 0 {((2, 2), true)},
  St.cut {{((0, 0), true)}, {((0, 3), true)}, {((1, 0), true)}, {((1, 3), true)}, {((2, 2), false)}} 16 23 {((0, 2), false), ((1, 2), false)},
  St.cut {{((0, 0), true)}, {((0, 3), true)}, {((1, 0), true)}, {((1, 3), true)}, {((2, 0), true)}, {((2, 2), true)}, {((2, 3), true)}} 18 0 {((2, 1), true)},
  St.cut {{((0, 0), true)}, {((0, 3), true)}, {((1, 0), true)}, {((1, 3), true)}, {((2, 1), false)}} 4 24 {((0, 1), false), ((1, 1), false)},
  St.cut {{((0, 0), true)}, {((0, 2), true)}, {((1, 0), true)}, {((1, 2), true)}, {((2, 0), true)}, {((2, 2), true)}} 1 0 {((2, 3), true)},
  St.cut {{((0, 0), true)}, {((0, 2), true)}, {((1, 0), true)}, {((1, 2), true)}, {((2, 3), false)}} 7 19 {((0, 3), false), ((1, 3), false)},
  St.cut {{((0, 0), true)}, {((0, 2), true)}, {((1, 0), true)}, {((1, 2), true)}, {((2, 0), true)}, {((2, 2), true)}, {((2, 3), true)}} 14 0 {((2, 1), true)},
  St.cut {{((0, 0), true)}, {((0, 2), true)}, {((1, 0), true)}, {((1, 2), true)}, {((2, 1), false)}} 0 23 {((0, 1), false), ((1, 1), false)},
  St.andI {{((0, 1), false), ((1, 1), false)}, {((2, 1), false)}} 1 0 {((0, 1), false)} {((1, 1), false)},
  St.ax {((1, 1), false), ((2, 1), false)},
  St.ax {((0, 1), false), ((2, 1), false)},
  St.cut {{((0, 0), true)}, {((0, 1), true)}, {((1, 0), true)}, {((1, 1), true)}, {((2, 0), true)}, {((2, 1), true)}} 4 0 {((2, 3), true)},
  St.cut {{((0, 0), true)}, {((0, 1), true)}, {((1, 0), true)}, {((1, 1), true)}, {((2, 3), false)}} 0 15 {((0, 3), false), ((1, 3), false)},
  St.andI {{((0, 3), false), ((1, 3), false)}, {((2, 3), false)}} 1 0 {((0, 3), false)} {((1, 3), false)},
  St.ax {((1, 3), false), ((2, 3), false)},
  St.ax {((0, 3), false), ((2, 3), false)},
  St.cut {{((0, 0), true)}, {((0, 1), true)}, {((1, 0), true)}, {((1, 1), true)}, {((2, 0), true)}, {((2, 1), true)}, {((2, 3), true)}} 4 0 {((2, 2), true)},
  St.cut {{((0, 0), true)}, {((0, 1), true)}, {((1, 0), true)}, {((1, 1), true)}, {((2, 2), false)}} 0 13 {((0, 2), false), ((1, 2), false)},
  St.andI {{((0, 2), false), ((1, 2), false)}, {((2, 2), false)}} 1 0 {((0, 2), false)} {((1, 2), false)},
  St.ax {((1, 2), false), ((2, 2), false)},
  St.ax {((0, 2), false), ((2, 2), false)},
  St.ax {((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)},
  St.cut {{((0, 1), true)}, {((0, 2), true)}, {((0, 3), true)}, {((1, 1), true)}, {((1, 2), true)}, {((1, 3), true)}} 11 0 {((1, 0), true)},
  St.cut {{((0, 1), true)}, {((0, 2), true)}, {((0, 3), true)}, {((1, 0), false)}} 11 0 {((0, 0), true)},
  St.ax {((0, 0), false), ((1, 0), false)},
  St.cut {{((0, 0), true)}, {((0, 2), true)}, {((0, 3), true)}, {((1, 0), true)}, {((1, 2), true)}, {((1, 3), true)}} 8 0 {((1, 1), true)},
  St.cut {{((0, 0), true)}, {((0, 2), true)}, {((0, 3), true)}, {((1, 1), false)}} 8 0 {((0, 1), true)},
  St.ax {((0, 1), false), ((1, 1), false)},
  St.cut {{((0, 0), true)}, {((0, 1), true)}, {((0, 3), true)}, {((1, 0), true)}, {((1, 1), true)}, {((1, 3), true)}} 5 0 {((1, 2), true)},
  St.cut {{((0, 0), true)}, {((0, 1), true)}, {((0, 3), true)}, {((1, 2), false)}} 5 0 {((0, 2), true)},
  St.ax {((0, 2), false), ((1, 2), false)},
  St.cut {{((0, 0), true)}, {((0, 1), true)}, {((0, 2), true)}, {((1, 0), true)}, {((1, 1), true)}, {((1, 2), true)}} 2 0 {((1, 3), true)},
  St.cut {{((0, 0), true)}, {((0, 1), true)}, {((0, 2), true)}, {((1, 3), false)}} 2 0 {((0, 3), true)},
  St.ax {((0, 3), false), ((1, 3), false)},
  St.ax {((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)},
  St.ax {((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)}]

theorem hc : chk (axPHP 5 4) cert = true := by decide +kernel

theorem hm : (∅ : KLine VV) ∈ cert.map St.line := by decide +kernel

theorem hl : (cert.map St.line).length ≤ 140 := by decide +kernel

theorem main_aux : ∃ π : List (PEqualNP.ProofComplexity.KLine (Fin 5 × Fin 4)), PEqualNP.ProofComplexity.IsResKRefutation 2 (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 140 :=
  ⟨cert.map St.line, ⟨chk_sound _ _ (axPHP_sound 5 4) cert hc, hm⟩, hl⟩

end PEqualNP.Outside.L_pcx_199

theorem PEqualNP.Outside.L_pcx_199 : ∃ π : List (PEqualNP.ProofComplexity.KLine (Fin 5 × Fin 4)), PEqualNP.ProofComplexity.IsResKRefutation 2 (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 140 := by
  exact PEqualNP.Outside.L_pcx_199.main_aux
