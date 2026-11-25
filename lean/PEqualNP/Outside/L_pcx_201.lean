import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_201

open PEqualNP.ProofComplexity

theorem memD {α : Type} (l : List α) (d : α) (i : ℕ) (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

-- resolution lines, newest first; a hint (i, j, v): the premises are entries i and j of the tail, pivot v
def chkR {V : Type} [DecidableEq V] (ax : Clause V → Bool) :
    List (Clause V × Option (ℕ × ℕ × V)) → Bool
  | [] => true
  | (R, none) :: t => ax R && chkR ax t
  | (R, some (i, j, v)) :: t =>
      decide (i < t.length) && decide (j < t.length) &&
      decide ((v, true) ∈ (t.map Prod.fst).getD i ∅ ∧ (v, false) ∈ (t.map Prod.fst).getD j ∅ ∧
        R = ((t.map Prod.fst).getD i ∅).erase (v, true) ∪ ((t.map Prod.fst).getD j ∅).erase (v, false)) &&
      chkR ax t

theorem chkR_sound {V : Type} [DecidableEq V] (F : Set (Clause V)) (ax : Clause V → Bool)
    (hax : ∀ C, ax C = true → C ∈ F) :
    ∀ l, chkR ax l = true → IsDerivation F (l.map Prod.fst)
  | [], _ => IsDerivation.nil
  | (R, none) :: t, h => by
    simp only [chkR, Bool.and_eq_true] at h
    exact IsDerivation.ax (chkR_sound F ax hax t h.2) (hax R h.1)
  | (R, some (i, j, v)) :: t, h => by
    simp only [chkR, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, h1, h2, h3⟩, ht⟩ := h
    exact IsDerivation.res (chkR_sound F ax hax t ht) (memD _ _ _ (by simpa using hi))
      (memD _ _ _ (by simpa using hj)) ⟨v, h1, h2, h3⟩

-- Res(lin): the assignment check of a weakening runs over the variables vs only
def axPHP (m n : ℕ) (C : Clause (Fin m × Fin n)) : Bool :=
  decide (∃ i : Fin m, C = Finset.univ.image (fun j : Fin n => ((i, j), true))) ||
  decide (∃ i : Fin m, ∃ i' : Fin m, ∃ j : Fin n, i ≠ i' ∧ C = {((i, j), false), ((i', j), false)})

theorem axPHP_sound (m n : ℕ) : ∀ C, axPHP m n C = true → C ∈ PHP m n := by
  intro C h
  simp only [axPHP, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨i, hi⟩ | ⟨i, i', j, hne, hC⟩
  · exact Or.inl ⟨i, hi⟩
  · exact Or.inr ⟨i, i', j, hne, hC⟩

def cert : List (Clause (Fin 5 × Fin 4) × Option (ℕ × ℕ × (Fin 5 × Fin 4))) := [
  (∅, some (8, 0, (4, 3))),
  ({((4, 3), false)}, some (1, 0, (3, 3))),
  ({((3, 3), false), ((4, 3), false)}, none),
  ({((3, 3), true), ((4, 3), false)}, some (1, 0, (2, 3))),
  ({((2, 3), false), ((4, 3), false)}, none),
  ({((2, 3), true), ((3, 3), true), ((4, 3), false)}, some (1, 0, (1, 3))),
  ({((1, 3), false), ((4, 3), false)}, none),
  ({((1, 3), true), ((2, 3), true), ((3, 3), true), ((4, 3), false)}, some (29, 0, (0, 3))),
  ({((0, 3), false), ((4, 3), false)}, none),
  ({((4, 3), true)}, some (8, 0, (4, 2))),
  ({((4, 2), false)}, some (1, 0, (3, 2))),
  ({((3, 2), false), ((4, 2), false)}, none),
  ({((3, 2), true), ((4, 2), false)}, some (1, 0, (2, 2))),
  ({((2, 2), false), ((4, 2), false)}, none),
  ({((2, 2), true), ((3, 2), true), ((4, 2), false)}, some (1, 0, (1, 2))),
  ({((1, 2), false), ((4, 2), false)}, none),
  ({((1, 2), true), ((2, 2), true), ((3, 2), true), ((4, 2), false)}, some (32, 0, (0, 2))),
  ({((0, 2), false), ((4, 2), false)}, none),
  ({((4, 2), true), ((4, 3), true)}, some (8, 0, (4, 1))),
  ({((4, 1), false)}, some (1, 0, (3, 1))),
  ({((3, 1), false), ((4, 1), false)}, none),
  ({((3, 1), true), ((4, 1), false)}, some (1, 0, (2, 1))),
  ({((2, 1), false), ((4, 1), false)}, none),
  ({((2, 1), true), ((3, 1), true), ((4, 1), false)}, some (1, 0, (1, 1))),
  ({((1, 1), false), ((4, 1), false)}, none),
  ({((1, 1), true), ((2, 1), true), ((3, 1), true), ((4, 1), false)}, some (35, 0, (0, 1))),
  ({((0, 1), false), ((4, 1), false)}, none),
  ({((4, 1), true), ((4, 2), true), ((4, 3), true)}, some (8, 0, (4, 0))),
  ({((4, 0), false)}, some (1, 0, (3, 0))),
  ({((3, 0), false), ((4, 0), false)}, none),
  ({((3, 0), true), ((4, 0), false)}, some (1, 0, (2, 0))),
  ({((2, 0), false), ((4, 0), false)}, none),
  ({((2, 0), true), ((3, 0), true), ((4, 0), false)}, some (1, 0, (1, 0))),
  ({((1, 0), false), ((4, 0), false)}, none),
  ({((1, 0), true), ((2, 0), true), ((3, 0), true), ((4, 0), false)}, some (41, 0, (0, 0))),
  ({((0, 0), false), ((4, 0), false)}, none),
  ({((4, 0), true), ((4, 1), true), ((4, 2), true), ((4, 3), true)}, none),
  ({((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 3), true)}, some (3, 0, (3, 2))),
  ({((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 2), false)}, some (0, 46, (2, 2))),
  ({((0, 3), true), ((1, 3), true), ((2, 2), true), ((2, 3), true), ((3, 2), false)}, some (0, 47, (1, 2))),
  ({((0, 3), true), ((1, 2), true), ((1, 3), true), ((2, 2), true), ((2, 3), true), ((3, 2), false)}, some (57, 48, (0, 2))),
  ({((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 2), true), ((3, 3), true)}, some (3, 0, (3, 1))),
  ({((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 1), false)}, some (0, 49, (2, 1))),
  ({((0, 3), true), ((1, 3), true), ((2, 1), true), ((2, 3), true), ((3, 1), false)}, some (0, 50, (1, 1))),
  ({((0, 3), true), ((1, 1), true), ((1, 3), true), ((2, 1), true), ((2, 3), true), ((3, 1), false)}, some (59, 51, (0, 1))),
  ({((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)}, some (51, 0, (3, 0))),
  ({((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 0), false)}, some (0, 24, (2, 0))),
  ({((0, 3), true), ((1, 3), true), ((2, 0), true), ((2, 3), true), ((3, 0), false)}, some (0, 25, (1, 0))),
  ({((0, 3), true), ((1, 0), true), ((1, 3), true), ((2, 0), true), ((2, 3), true), ((3, 0), false)}, some (69, 26, (0, 0))),
  ({((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 2), true)}, some (3, 0, (3, 3))),
  ({((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 3), false)}, some (0, 27, (2, 3))),
  ({((0, 2), true), ((1, 2), true), ((2, 2), true), ((2, 3), true), ((3, 3), false)}, some (0, 28, (1, 3))),
  ({((0, 2), true), ((1, 2), true), ((1, 3), true), ((2, 2), true), ((2, 3), true), ((3, 3), false)}, some (45, 29, (0, 3))),
  ({((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 2), true), ((3, 3), true)}, some (3, 0, (3, 1))),
  ({((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 1), false)}, some (0, 37, (2, 1))),
  ({((0, 2), true), ((1, 2), true), ((2, 1), true), ((2, 2), true), ((3, 1), false)}, some (0, 38, (1, 1))),
  ({((0, 2), true), ((1, 1), true), ((1, 2), true), ((2, 1), true), ((2, 2), true), ((3, 1), false)}, some (53, 39, (0, 1))),
  ({((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)}, some (39, 0, (3, 0))),
  ({((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 0), false)}, some (0, 12, (2, 0))),
  ({((0, 2), true), ((1, 2), true), ((2, 0), true), ((2, 2), true), ((3, 0), false)}, some (0, 13, (1, 0))),
  ({((0, 2), true), ((1, 0), true), ((1, 2), true), ((2, 0), true), ((2, 2), true), ((3, 0), false)}, some (63, 14, (0, 0))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 1), true)}, some (3, 0, (3, 3))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 3), false)}, some (0, 15, (2, 3))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true), ((2, 3), true), ((3, 3), false)}, some (0, 16, (1, 3))),
  ({((0, 1), true), ((1, 1), true), ((1, 3), true), ((2, 1), true), ((2, 3), true), ((3, 3), false)}, some (39, 17, (0, 3))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 1), true), ((3, 3), true)}, some (3, 0, (3, 2))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 2), false)}, some (0, 18, (2, 2))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true), ((2, 2), true), ((3, 2), false)}, some (0, 19, (1, 2))),
  ({((0, 1), true), ((1, 1), true), ((1, 2), true), ((2, 1), true), ((2, 2), true), ((3, 2), false)}, some (41, 20, (0, 2))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)}, some (27, 0, (3, 0))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 0), false)}, some (1, 0, (2, 0))),
  ({((2, 0), false), ((3, 0), false)}, none),
  ({((0, 1), true), ((1, 1), true), ((2, 0), true), ((2, 1), true), ((3, 0), false)}, some (1, 0, (1, 0))),
  ({((1, 0), false), ((3, 0), false)}, none),
  ({((0, 1), true), ((1, 0), true), ((1, 1), true), ((2, 0), true), ((2, 1), true), ((3, 0), false)}, some (57, 0, (0, 0))),
  ({((0, 0), false), ((3, 0), false)}, none),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 0), true)}, some (6, 0, (3, 3))),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 3), false)}, some (1, 0, (2, 3))),
  ({((2, 3), false), ((3, 3), false)}, none),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((2, 3), true), ((3, 3), false)}, some (1, 0, (1, 3))),
  ({((1, 3), false), ((3, 3), false)}, none),
  ({((0, 0), true), ((1, 0), true), ((1, 3), true), ((2, 0), true), ((2, 3), true), ((3, 3), false)}, some (36, 0, (0, 3))),
  ({((0, 3), false), ((3, 3), false)}, none),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 0), true), ((3, 3), true)}, some (6, 0, (3, 2))),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 2), false)}, some (1, 0, (2, 2))),
  ({((2, 2), false), ((3, 2), false)}, none),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((2, 2), true), ((3, 2), false)}, some (1, 0, (1, 2))),
  ({((1, 2), false), ((3, 2), false)}, none),
  ({((0, 0), true), ((1, 0), true), ((1, 2), true), ((2, 0), true), ((2, 2), true), ((3, 2), false)}, some (35, 0, (0, 2))),
  ({((0, 2), false), ((3, 2), false)}, none),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 0), true), ((3, 2), true), ((3, 3), true)}, some (6, 0, (3, 1))),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 1), false)}, some (1, 0, (2, 1))),
  ({((2, 1), false), ((3, 1), false)}, none),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((2, 1), true), ((3, 1), false)}, some (1, 0, (1, 1))),
  ({((1, 1), false), ((3, 1), false)}, none),
  ({((0, 0), true), ((1, 0), true), ((1, 1), true), ((2, 0), true), ((2, 1), true), ((3, 1), false)}, some (36, 0, (0, 1))),
  ({((0, 1), false), ((3, 1), false)}, none),
  ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)}, none),
  ({((0, 2), true), ((0, 3), true), ((1, 2), true), ((1, 3), true), ((2, 2), true), ((2, 3), true)}, some (2, 0, (2, 1))),
  ({((0, 2), true), ((0, 3), true), ((1, 2), true), ((1, 3), true), ((2, 1), false)}, some (0, 29, (1, 1))),
  ({((0, 2), true), ((0, 3), true), ((1, 1), true), ((1, 2), true), ((1, 3), true), ((2, 1), false)}, some (42, 30, (0, 1))),
  ({((0, 2), true), ((0, 3), true), ((1, 2), true), ((1, 3), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)}, some (40, 0, (2, 0))),
  ({((0, 2), true), ((0, 3), true), ((1, 2), true), ((1, 3), true), ((2, 0), false)}, some (0, 12, (1, 0))),
  ({((0, 2), true), ((0, 3), true), ((1, 0), true), ((1, 2), true), ((1, 3), true), ((2, 0), false)}, some (42, 13, (0, 0))),
  ({((0, 1), true), ((0, 3), true), ((1, 1), true), ((1, 3), true), ((2, 1), true), ((2, 3), true)}, some (2, 0, (2, 2))),
  ({((0, 1), true), ((0, 3), true), ((1, 1), true), ((1, 3), true), ((2, 2), false)}, some (0, 33, (1, 2))),
  ({((0, 1), true), ((0, 3), true), ((1, 1), true), ((1, 2), true), ((1, 3), true), ((2, 2), false)}, some (36, 34, (0, 2))),
  ({((0, 1), true), ((0, 3), true), ((1, 1), true), ((1, 3), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)}, some (34, 0, (2, 0))),
  ({((0, 1), true), ((0, 3), true), ((1, 1), true), ((1, 3), true), ((2, 0), false)}, some (0, 6, (1, 0))),
  ({((0, 1), true), ((0, 3), true), ((1, 0), true), ((1, 1), true), ((1, 3), true), ((2, 0), false)}, some (39, 7, (0, 0))),
  ({((0, 1), true), ((0, 2), true), ((1, 1), true), ((1, 2), true), ((2, 1), true), ((2, 2), true)}, some (2, 0, (2, 3))),
  ({((0, 1), true), ((0, 2), true), ((1, 1), true), ((1, 2), true), ((2, 3), false)}, some (0, 22, (1, 3))),
  ({((0, 1), true), ((0, 2), true), ((1, 1), true), ((1, 2), true), ((1, 3), true), ((2, 3), false)}, some (30, 23, (0, 3))),
  ({((0, 1), true), ((0, 2), true), ((1, 1), true), ((1, 2), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)}, some (28, 0, (2, 0))),
  ({((0, 1), true), ((0, 2), true), ((1, 1), true), ((1, 2), true), ((2, 0), false)}, some (1, 0, (1, 0))),
  ({((1, 0), false), ((2, 0), false)}, none),
  ({((0, 1), true), ((0, 2), true), ((1, 0), true), ((1, 1), true), ((1, 2), true), ((2, 0), false)}, some (35, 0, (0, 0))),
  ({((0, 0), false), ((2, 0), false)}, none),
  ({((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 3), true), ((2, 0), true), ((2, 3), true)}, some (2, 0, (2, 2))),
  ({((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 3), true), ((2, 2), false)}, some (0, 19, (1, 2))),
  ({((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 2), true), ((1, 3), true), ((2, 2), false)}, some (25, 20, (0, 2))),
  ({((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 3), true), ((2, 0), true), ((2, 2), true), ((2, 3), true)}, some (20, 0, (2, 1))),
  ({((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 3), true), ((2, 1), false)}, some (0, 6, (1, 1))),
  ({((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 1), true), ((1, 3), true), ((2, 1), false)}, some (25, 7, (0, 1))),
  ({((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 2), true), ((2, 0), true), ((2, 2), true)}, some (2, 0, (2, 3))),
  ({((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 2), true), ((2, 3), false)}, some (0, 8, (1, 3))),
  ({((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 2), true), ((1, 3), true), ((2, 3), false)}, some (19, 9, (0, 3))),
  ({((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 2), true), ((2, 0), true), ((2, 2), true), ((2, 3), true)}, some (14, 0, (2, 1))),
  ({((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 2), true), ((2, 1), false)}, some (1, 0, (1, 1))),
  ({((1, 1), false), ((2, 1), false)}, none),
  ({((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 1), true), ((1, 2), true), ((2, 1), false)}, some (21, 0, (0, 1))),
  ({((0, 1), false), ((2, 1), false)}, none),
  ({((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((2, 0), true), ((2, 1), true)}, some (4, 0, (2, 3))),
  ({((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((2, 3), false)}, some (1, 0, (1, 3))),
  ({((1, 3), false), ((2, 3), false)}, none),
  ({((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((1, 3), true), ((2, 3), false)}, some (13, 0, (0, 3))),
  ({((0, 3), false), ((2, 3), false)}, none),
  ({((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((2, 0), true), ((2, 1), true), ((2, 3), true)}, some (4, 0, (2, 2))),
  ({((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((2, 2), false)}, some (1, 0, (1, 2))),
  ({((1, 2), false), ((2, 2), false)}, none),
  ({((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((1, 2), true), ((2, 2), false)}, some (11, 0, (0, 2))),
  ({((0, 2), false), ((2, 2), false)}, none),
  ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)}, none),
  ({((0, 1), true), ((0, 2), true), ((0, 3), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)}, some (11, 0, (1, 0))),
  ({((0, 1), true), ((0, 2), true), ((0, 3), true), ((1, 0), false)}, some (11, 0, (0, 0))),
  ({((0, 0), false), ((1, 0), false)}, none),
  ({((0, 0), true), ((0, 2), true), ((0, 3), true), ((1, 0), true), ((1, 2), true), ((1, 3), true)}, some (8, 0, (1, 1))),
  ({((0, 0), true), ((0, 2), true), ((0, 3), true), ((1, 1), false)}, some (8, 0, (0, 1))),
  ({((0, 1), false), ((1, 1), false)}, none),
  ({((0, 0), true), ((0, 1), true), ((0, 3), true), ((1, 0), true), ((1, 1), true), ((1, 3), true)}, some (5, 0, (1, 2))),
  ({((0, 0), true), ((0, 1), true), ((0, 3), true), ((1, 2), false)}, some (5, 0, (0, 2))),
  ({((0, 2), false), ((1, 2), false)}, none),
  ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((1, 0), true), ((1, 1), true), ((1, 2), true)}, some (2, 0, (1, 3))),
  ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((1, 3), false)}, some (2, 0, (0, 3))),
  ({((0, 3), false), ((1, 3), false)}, none),
  ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)}, none),
  ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)}, none)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hc : chkR (axPHP 5 4) cert = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem hm : (∅ : Clause (Fin 5 × Fin 4)) ∈ cert.map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
theorem hl : (cert.map Prod.fst).length ≤ 173 := by decide +kernel

theorem kl_inj {V : Type} [DecidableEq V] : Function.Injective (fun l : Literal V => ({l} : KTerm V)) :=
  fun _ _ h => Finset.singleton_injective h

theorem kl_card {V : Type} [DecidableEq V] (C : Clause V) : ∀ T ∈ kLineOfClause C, T.card ≤ 2 := by
  intro T hT
  simp only [kLineOfClause, Finset.mem_image] at hT
  obtain ⟨l, _, rfl⟩ := hT
  simp

theorem kl_cut {V : Type} [DecidableEq V] (C D R : Clause V) (h : IsResolvent C D R) :
    IsResKCut (kLineOfClause C) (kLineOfClause D) (kLineOfClause R) := by
  obtain ⟨v, h1, h2, h3⟩ := h
  refine ⟨{(v, true)}, ?_, Finset.singleton_nonempty _, ?_, ?_⟩
  · exact Finset.mem_image_of_mem (fun l : Literal V => ({l} : KTerm V)) h1
  · intro l hl
    rw [Finset.mem_singleton] at hl
    subst hl
    exact Finset.mem_image_of_mem (fun l : Literal V => ({l} : KTerm V)) h2
  · subst h3
    have e1 := Finset.image_erase (kl_inj (V := V)) C (v, true)
    have e2 := Finset.image_erase (kl_inj (V := V)) D (v, false)
    simp only [kLineOfClause, Finset.image_union, Finset.image_singleton, Bool.not_true,
      Finset.sdiff_singleton_eq_erase]
    rw [e1, e2]

theorem toResK {V : Type} [DecidableEq V] (F : Set (Clause V)) (π : List (Clause V))
    (h : IsDerivation F π) :
    IsResKDerivation 2 ((fun C => kLineOfClause C) '' F) (π.map kLineOfClause) := by
  induction h with
  | nil => exact IsResKDerivation.nil
  | ax _ hC ih => exact IsResKDerivation.ax ih ⟨_, hC, rfl⟩ (kl_card _)
  | res _ hC hD hR ih =>
    exact IsResKDerivation.cut ih (List.mem_map_of_mem hC) (List.mem_map_of_mem hD) (kl_cut _ _ _ hR)

end PEqualNP.Outside.L_pcx_201

theorem PEqualNP.Outside.L_pcx_201 : ∃ π : List (PEqualNP.ProofComplexity.KLine (Fin 5 × Fin 4)), PEqualNP.ProofComplexity.IsResKRefutation 2 (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 173 := by
  refine ⟨(PEqualNP.Outside.L_pcx_201.cert.map Prod.fst).map PEqualNP.ProofComplexity.kLineOfClause, ⟨PEqualNP.Outside.L_pcx_201.toResK _ _ (PEqualNP.Outside.L_pcx_201.chkR_sound _ (PEqualNP.Outside.L_pcx_201.axPHP 5 4) (PEqualNP.Outside.L_pcx_201.axPHP_sound 5 4) _ PEqualNP.Outside.L_pcx_201.hc), ?_⟩, ?_⟩
  · have e : (∅ : PEqualNP.ProofComplexity.KLine (Fin 5 × Fin 4)) = PEqualNP.ProofComplexity.kLineOfClause (∅ : PEqualNP.ProofComplexity.Clause (Fin 5 × Fin 4)) := by
      simp [PEqualNP.ProofComplexity.kLineOfClause]
    rw [e]
    exact List.mem_map_of_mem PEqualNP.Outside.L_pcx_201.hm
  · rw [List.length_map]
    exact PEqualNP.Outside.L_pcx_201.hl
