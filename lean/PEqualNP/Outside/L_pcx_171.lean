import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_171

open PEqualNP.ProofComplexity

abbrev V : Type := Fin 5 × Fin 4

-- A Boolean checker for derivations: each line is in the list A, or the resolvent of
-- two later lines (indices into the tail) on a single variable.
def chk {W : Type} [DecidableEq W] (A : List (Clause W)) :
    List (Clause W) → List (Option (ℕ × ℕ × W)) → Bool
  | [], _ => true
  | C :: π, none :: hs => decide (C ∈ A) && chk A π hs
  | R :: π, some (i, j, v) :: hs =>
      (match π[i]?, π[j]? with
        | some C, some D => decide ((v, false) ∈ C) && decide ((v, true) ∈ D) &&
            decide (R = D.erase (v, true) ∪ C.erase (v, false))
        | _, _ => false) && chk A π hs
  | _ :: _, [] => false

theorem chk_sound {W : Type} [DecidableEq W] (F : Set (Clause W)) (A : List (Clause W))
    (hA : ∀ C ∈ A, C ∈ F) :
    ∀ (π : List (Clause W)) (hs : List (Option (ℕ × ℕ × W))), chk A π hs = true →
      IsDerivation F π
  | [], _, _ => IsDerivation.nil
  | C :: π, none :: hs, h => by
      simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
      exact IsDerivation.ax (chk_sound F A hA π hs h.2) (hA _ h.1)
  | R :: π, some (i, j, v) :: hs, h => by
      simp only [chk, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      cases hC : π[i]? with
      | none => simp [hC] at h1
      | some C =>
        cases hD : π[j]? with
        | none => simp [hC, hD] at h1
        | some D =>
          simp only [hC, hD, Bool.and_eq_true, decide_eq_true_eq] at h1
          obtain ⟨⟨m1, m2⟩, m3⟩ := h1
          exact IsDerivation.res (chk_sound F A hA π hs h2)
            (List.mem_iff_getElem?.mpr ⟨j, hD⟩) (List.mem_iff_getElem?.mpr ⟨i, hC⟩)
            ⟨v, m2, m1, m3⟩
  | _ :: _, [], h => by simp [chk] at h

def pig (i : Fin 5) : Clause V := Finset.univ.image (fun j : Fin 4 => ((i, j), true))

def hole (i i' : Fin 5) (j : Fin 4) : Clause V := {((i, j), false), ((i', j), false)}

def triples : List (Fin 5 × Fin 5 × Fin 4) :=
  [(0, 1, 0), (0, 2, 0), (0, 3, 0), (0, 4, 0), (1, 2, 0), (1, 3, 0), (1, 4, 0), (2, 3, 0), (2, 4, 0), (3, 4, 0), (0, 1, 1), (0, 2, 1), (0, 3, 1), (0, 4, 1), (1, 2, 1), (1, 3, 1), (1, 4, 1), (2, 3, 1), (2, 4, 1), (3, 4, 1), (0, 1, 2), (0, 2, 2), (0, 3, 2), (0, 4, 2), (1, 2, 2), (1, 3, 2), (1, 4, 2), (2, 3, 2), (2, 4, 2), (3, 4, 2), (0, 1, 3), (0, 2, 3), (0, 3, 3), (0, 4, 3), (1, 2, 3), (1, 3, 3), (1, 4, 3), (2, 3, 3), (2, 4, 3), (3, 4, 3)]

theorem triples_ne : ∀ t ∈ triples, t.1 ≠ t.2.1 := by decide

def axList : List (Clause V) :=
  ((List.finRange 5).map fun i => pig i) ++
    (triples.map fun t => hole t.1 t.2.1 t.2.2)

theorem axList_sub : ∀ C ∈ axList, C ∈ PHP 5 4 := by
  intro C hC
  simp only [axList, List.mem_append, List.mem_map] at hC
  rcases hC with ⟨i, -, rfl⟩ | ⟨t, ht, rfl⟩
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨t.1, t.2.1, t.2.2, triples_ne t ht, rfl⟩

def pf : List (Clause V) :=
  [∅,
   {((4, 3), true)},
   {((4, 2), true), ((4, 3), true)},
   {((4, 1), true), ((4, 2), true), ((4, 3), true)},
   {((4, 3), false)},
   {((3, 3), true), ((4, 3), false)},
   {((2, 3), true), ((3, 3), true), ((4, 3), false)},
   {((1, 3), true), ((2, 3), true), ((3, 3), true), ((4, 3), false)},
   {((4, 2), false)},
   {((3, 2), true), ((4, 2), false)},
   {((2, 2), true), ((3, 2), true), ((4, 2), false)},
   {((1, 2), true), ((2, 2), true), ((3, 2), true), ((4, 2), false)},
   {((4, 1), false)},
   {((3, 1), true), ((4, 1), false)},
   {((2, 1), true), ((3, 1), true), ((4, 1), false)},
   {((1, 1), true), ((2, 1), true), ((3, 1), true), ((4, 1), false)},
   {((4, 0), false)},
   {((3, 0), true), ((4, 0), false)},
   {((2, 0), true), ((3, 0), true), ((4, 0), false)},
   {((1, 0), true), ((2, 0), true), ((3, 0), true), ((4, 0), false)},
   {((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 3), true)},
   {((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 2), true), ((3, 3), true)},
   {((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)},
   {((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 2), false)},
   {((0, 3), true), ((1, 3), true), ((2, 2), true), ((2, 3), true), ((3, 2), false)},
   {((0, 3), true), ((1, 2), true), ((1, 3), true), ((2, 2), true), ((2, 3), true), ((3, 2), false)},
   {((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 1), false)},
   {((0, 3), true), ((1, 3), true), ((2, 1), true), ((2, 3), true), ((3, 1), false)},
   {((0, 3), true), ((1, 1), true), ((1, 3), true), ((2, 1), true), ((2, 3), true), ((3, 1), false)},
   {((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 0), false)},
   {((0, 3), true), ((1, 3), true), ((2, 0), true), ((2, 3), true), ((3, 0), false)},
   {((0, 3), true), ((1, 0), true), ((1, 3), true), ((2, 0), true), ((2, 3), true), ((3, 0), false)},
   {((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 2), true)},
   {((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 2), true), ((3, 3), true)},
   {((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)},
   {((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 3), false)},
   {((0, 2), true), ((1, 2), true), ((2, 2), true), ((2, 3), true), ((3, 3), false)},
   {((0, 2), true), ((1, 2), true), ((1, 3), true), ((2, 2), true), ((2, 3), true), ((3, 3), false)},
   {((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 1), false)},
   {((0, 2), true), ((1, 2), true), ((2, 1), true), ((2, 2), true), ((3, 1), false)},
   {((0, 2), true), ((1, 1), true), ((1, 2), true), ((2, 1), true), ((2, 2), true), ((3, 1), false)},
   {((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 0), false)},
   {((0, 2), true), ((1, 2), true), ((2, 0), true), ((2, 2), true), ((3, 0), false)},
   {((0, 2), true), ((1, 0), true), ((1, 2), true), ((2, 0), true), ((2, 2), true), ((3, 0), false)},
   {((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 1), true)},
   {((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 1), true), ((3, 3), true)},
   {((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)},
   {((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 3), false)},
   {((0, 1), true), ((1, 1), true), ((2, 1), true), ((2, 3), true), ((3, 3), false)},
   {((0, 1), true), ((1, 1), true), ((1, 3), true), ((2, 1), true), ((2, 3), true), ((3, 3), false)},
   {((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 2), false)},
   {((0, 1), true), ((1, 1), true), ((2, 1), true), ((2, 2), true), ((3, 2), false)},
   {((0, 1), true), ((1, 1), true), ((1, 2), true), ((2, 1), true), ((2, 2), true), ((3, 2), false)},
   {((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 0), false)},
   {((0, 1), true), ((1, 1), true), ((2, 0), true), ((2, 1), true), ((3, 0), false)},
   {((0, 1), true), ((1, 0), true), ((1, 1), true), ((2, 0), true), ((2, 1), true), ((3, 0), false)},
   {((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 0), true)},
   {((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 0), true), ((3, 3), true)},
   {((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 0), true), ((3, 2), true), ((3, 3), true)},
   {((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 3), false)},
   {((0, 0), true), ((1, 0), true), ((2, 0), true), ((2, 3), true), ((3, 3), false)},
   {((0, 0), true), ((1, 0), true), ((1, 3), true), ((2, 0), true), ((2, 3), true), ((3, 3), false)},
   {((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 2), false)},
   {((0, 0), true), ((1, 0), true), ((2, 0), true), ((2, 2), true), ((3, 2), false)},
   {((0, 0), true), ((1, 0), true), ((1, 2), true), ((2, 0), true), ((2, 2), true), ((3, 2), false)},
   {((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 1), false)},
   {((0, 0), true), ((1, 0), true), ((2, 0), true), ((2, 1), true), ((3, 1), false)},
   {((0, 0), true), ((1, 0), true), ((1, 1), true), ((2, 0), true), ((2, 1), true), ((3, 1), false)},
   {((0, 2), true), ((0, 3), true), ((1, 2), true), ((1, 3), true), ((2, 2), true), ((2, 3), true)},
   {((0, 2), true), ((0, 3), true), ((1, 2), true), ((1, 3), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)},
   {((0, 2), true), ((0, 3), true), ((1, 2), true), ((1, 3), true), ((2, 1), false)},
   {((0, 2), true), ((0, 3), true), ((1, 1), true), ((1, 2), true), ((1, 3), true), ((2, 1), false)},
   {((0, 2), true), ((0, 3), true), ((1, 2), true), ((1, 3), true), ((2, 0), false)},
   {((0, 2), true), ((0, 3), true), ((1, 0), true), ((1, 2), true), ((1, 3), true), ((2, 0), false)},
   {((0, 1), true), ((0, 3), true), ((1, 1), true), ((1, 3), true), ((2, 1), true), ((2, 3), true)},
   {((0, 1), true), ((0, 3), true), ((1, 1), true), ((1, 3), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)},
   {((0, 1), true), ((0, 3), true), ((1, 1), true), ((1, 3), true), ((2, 2), false)},
   {((0, 1), true), ((0, 3), true), ((1, 1), true), ((1, 2), true), ((1, 3), true), ((2, 2), false)},
   {((0, 1), true), ((0, 3), true), ((1, 1), true), ((1, 3), true), ((2, 0), false)},
   {((0, 1), true), ((0, 3), true), ((1, 0), true), ((1, 1), true), ((1, 3), true), ((2, 0), false)},
   {((0, 1), true), ((0, 2), true), ((1, 1), true), ((1, 2), true), ((2, 1), true), ((2, 2), true)},
   {((0, 1), true), ((0, 2), true), ((1, 1), true), ((1, 2), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)},
   {((0, 1), true), ((0, 2), true), ((1, 1), true), ((1, 2), true), ((2, 3), false)},
   {((0, 1), true), ((0, 2), true), ((1, 1), true), ((1, 2), true), ((1, 3), true), ((2, 3), false)},
   {((0, 1), true), ((0, 2), true), ((1, 1), true), ((1, 2), true), ((2, 0), false)},
   {((0, 1), true), ((0, 2), true), ((1, 0), true), ((1, 1), true), ((1, 2), true), ((2, 0), false)},
   {((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 3), true), ((2, 0), true), ((2, 3), true)},
   {((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 3), true), ((2, 0), true), ((2, 2), true), ((2, 3), true)},
   {((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 3), true), ((2, 2), false)},
   {((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 2), true), ((1, 3), true), ((2, 2), false)},
   {((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 3), true), ((2, 1), false)},
   {((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 1), true), ((1, 3), true), ((2, 1), false)},
   {((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 2), true), ((2, 0), true), ((2, 2), true)},
   {((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 2), true), ((2, 0), true), ((2, 2), true), ((2, 3), true)},
   {((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 2), true), ((2, 3), false)},
   {((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 2), true), ((1, 3), true), ((2, 3), false)},
   {((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 2), true), ((2, 1), false)},
   {((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 1), true), ((1, 2), true), ((2, 1), false)},
   {((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((2, 0), true), ((2, 1), true)},
   {((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((2, 0), true), ((2, 1), true), ((2, 3), true)},
   {((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((2, 3), false)},
   {((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((1, 3), true), ((2, 3), false)},
   {((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((2, 2), false)},
   {((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((1, 2), true), ((2, 2), false)},
   {((0, 1), true), ((0, 2), true), ((0, 3), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)},
   {((0, 1), true), ((0, 2), true), ((0, 3), true), ((1, 0), false)},
   {((0, 0), true), ((0, 2), true), ((0, 3), true), ((1, 0), true), ((1, 2), true), ((1, 3), true)},
   {((0, 0), true), ((0, 2), true), ((0, 3), true), ((1, 1), false)},
   {((0, 0), true), ((0, 1), true), ((0, 3), true), ((1, 0), true), ((1, 1), true), ((1, 3), true)},
   {((0, 0), true), ((0, 1), true), ((0, 3), true), ((1, 2), false)},
   {((0, 0), true), ((0, 1), true), ((0, 2), true), ((1, 0), true), ((1, 1), true), ((1, 2), true)},
   {((0, 0), true), ((0, 1), true), ((0, 2), true), ((1, 3), false)},
   {((3, 3), false), ((4, 3), false)},
   {((2, 3), false), ((4, 3), false)},
   {((2, 3), false), ((3, 3), false)},
   {((1, 3), false), ((4, 3), false)},
   {((1, 3), false), ((3, 3), false)},
   {((1, 3), false), ((2, 3), false)},
   {((0, 3), false), ((4, 3), false)},
   {((0, 3), false), ((3, 3), false)},
   {((0, 3), false), ((2, 3), false)},
   {((0, 3), false), ((1, 3), false)},
   {((3, 2), false), ((4, 2), false)},
   {((2, 2), false), ((4, 2), false)},
   {((2, 2), false), ((3, 2), false)},
   {((1, 2), false), ((4, 2), false)},
   {((1, 2), false), ((3, 2), false)},
   {((1, 2), false), ((2, 2), false)},
   {((0, 2), false), ((4, 2), false)},
   {((0, 2), false), ((3, 2), false)},
   {((0, 2), false), ((2, 2), false)},
   {((0, 2), false), ((1, 2), false)},
   {((3, 1), false), ((4, 1), false)},
   {((2, 1), false), ((4, 1), false)},
   {((2, 1), false), ((3, 1), false)},
   {((1, 1), false), ((4, 1), false)},
   {((1, 1), false), ((3, 1), false)},
   {((1, 1), false), ((2, 1), false)},
   {((0, 1), false), ((4, 1), false)},
   {((0, 1), false), ((3, 1), false)},
   {((0, 1), false), ((2, 1), false)},
   {((0, 1), false), ((1, 1), false)},
   {((3, 0), false), ((4, 0), false)},
   {((2, 0), false), ((4, 0), false)},
   {((2, 0), false), ((3, 0), false)},
   {((1, 0), false), ((4, 0), false)},
   {((1, 0), false), ((3, 0), false)},
   {((1, 0), false), ((2, 0), false)},
   {((0, 0), false), ((4, 0), false)},
   {((0, 0), false), ((3, 0), false)},
   {((0, 0), false), ((2, 0), false)},
   {((0, 0), false), ((1, 0), false)},
   {((4, 0), true), ((4, 1), true), ((4, 2), true), ((4, 3), true)},
   {((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)},
   {((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)},
   {((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)},
   {((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)}]

def hints : List (Option (ℕ × ℕ × V)) :=
  [some (3, 0, (4, 3)),
   some (6, 0, (4, 2)),
   some (9, 0, (4, 1)),
   some (12, 148, (4, 0)),
   some (107, 0, (3, 3)),
   some (107, 0, (2, 3)),
   some (108, 0, (1, 3)),
   some (110, 12, (0, 3)),
   some (113, 0, (3, 2)),
   some (113, 0, (2, 2)),
   some (114, 0, (1, 2)),
   some (116, 20, (0, 2)),
   some (119, 0, (3, 1)),
   some (119, 0, (2, 1)),
   some (120, 0, (1, 1)),
   some (122, 28, (0, 1)),
   some (125, 0, (3, 0)),
   some (125, 0, (2, 0)),
   some (126, 0, (1, 0)),
   some (128, 36, (0, 0)),
   some (2, 0, (3, 2)),
   some (4, 0, (3, 1)),
   some (6, 130, (3, 0)),
   some (100, 0, (2, 2)),
   some (101, 0, (1, 2)),
   some (103, 42, (0, 2)),
   some (107, 0, (2, 1)),
   some (108, 0, (1, 1)),
   some (110, 45, (0, 1)),
   some (114, 0, (2, 0)),
   some (115, 0, (1, 0)),
   some (117, 54, (0, 0)),
   some (2, 0, (3, 3)),
   some (4, 0, (3, 1)),
   some (6, 118, (3, 0)),
   some (78, 0, (2, 3)),
   some (79, 0, (1, 3)),
   some (81, 30, (0, 3)),
   some (95, 0, (2, 1)),
   some (96, 0, (1, 1)),
   some (98, 39, (0, 1)),
   some (102, 0, (2, 0)),
   some (103, 0, (1, 0)),
   some (105, 48, (0, 0)),
   some (2, 0, (3, 3)),
   some (4, 0, (3, 2)),
   some (6, 106, (3, 0)),
   some (66, 0, (2, 3)),
   some (67, 0, (1, 3)),
   some (69, 24, (0, 3)),
   some (73, 0, (2, 2)),
   some (74, 0, (1, 2)),
   some (76, 27, (0, 2)),
   some (90, 0, (2, 0)),
   some (91, 0, (1, 0)),
   some (93, 42, (0, 0)),
   some (2, 0, (3, 3)),
   some (4, 0, (3, 2)),
   some (6, 94, (3, 1)),
   some (54, 0, (2, 3)),
   some (55, 0, (1, 3)),
   some (57, 24, (0, 3)),
   some (61, 0, (2, 2)),
   some (62, 0, (1, 2)),
   some (64, 27, (0, 2)),
   some (68, 0, (2, 1)),
   some (69, 0, (1, 1)),
   some (71, 30, (0, 1)),
   some (1, 0, (2, 1)),
   some (2, 84, (2, 0)),
   some (66, 0, (1, 1)),
   some (68, 32, (0, 1)),
   some (74, 0, (1, 0)),
   some (76, 32, (0, 0)),
   some (1, 0, (2, 2)),
   some (2, 78, (2, 0)),
   some (50, 0, (1, 2)),
   some (52, 26, (0, 2)),
   some (68, 0, (1, 0)),
   some (70, 28, (0, 0)),
   some (1, 0, (2, 3)),
   some (2, 72, (2, 0)),
   some (34, 0, (1, 3)),
   some (36, 20, (0, 3)),
   some (62, 0, (1, 0)),
   some (64, 24, (0, 0)),
   some (1, 0, (2, 2)),
   some (2, 66, (2, 1)),
   some (38, 0, (1, 2)),
   some (40, 16, (0, 2)),
   some (46, 0, (1, 1)),
   some (48, 16, (0, 1)),
   some (1, 0, (2, 3)),
   some (2, 60, (2, 1)),
   some (22, 0, (1, 3)),
   some (24, 10, (0, 3)),
   some (40, 0, (1, 1)),
   some (42, 12, (0, 1)),
   some (1, 0, (2, 3)),
   some (2, 54, (2, 2)),
   some (16, 0, (1, 3)),
   some (18, 6, (0, 3)),
   some (24, 0, (1, 2)),
   some (26, 6, (0, 2)),
   some (0, 50, (1, 0)),
   some (45, 50, (0, 0)),
   some (0, 48, (1, 1)),
   some (33, 48, (0, 1)),
   some (0, 46, (1, 2)),
   some (21, 46, (0, 2)),
   some (0, 44, (1, 3)),
   some (9, 44, (0, 3)),
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none,
   none]

set_option maxRecDepth 10000 in
theorem pf_ok : chk axList pf hints = true := by decide +kernel

set_option maxRecDepth 10000 in
theorem pf_empty : (∅ : Clause V) ∈ pf := by decide +kernel

set_option maxRecDepth 10000 in
theorem pf_len : pf.length ≤ 159 := by decide

end PEqualNP.Outside.L_pcx_171

theorem PEqualNP.Outside.L_pcx_171 : ∃ π : List (PEqualNP.ProofComplexity.Clause (Fin 5 × Fin 4)), PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 159 := by
  exact ⟨PEqualNP.Outside.L_pcx_171.pf,
    ⟨PEqualNP.Outside.L_pcx_171.chk_sound _ _ PEqualNP.Outside.L_pcx_171.axList_sub _ _
      PEqualNP.Outside.L_pcx_171.pf_ok, PEqualNP.Outside.L_pcx_171.pf_empty⟩,
    PEqualNP.Outside.L_pcx_171.pf_len⟩
