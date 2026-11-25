import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_139

open PEqualNP.ProofComplexity

abbrev V : Type := Fin 4 × Fin 3

-- A Boolean checker for derivations: each line is in the list A, or the resolvent of
-- two later lines (indices into the tail) on a single variable.
def chk {W : Type} [DecidableEq W] (A : List (LinClause W)) :
    List (LinClause W) → List (Option (ℕ × ℕ × W)) → Bool
  | [], _ => true
  | C :: π, none :: hs => decide (C ∈ A) && chk A π hs
  | R :: π, some (i, j, v) :: hs =>
      (match π[i]?, π[j]? with
        | some C, some D => decide (({v}, false) ∈ C) && decide (({v}, true) ∈ D) &&
            decide (R = C.erase ({v}, false) ∪ D.erase ({v}, true))
        | _, _ => false) && chk A π hs
  | _ :: _, [] => false

theorem chk_sound {W : Type} [DecidableEq W] (F : Set (LinClause W)) (A : List (LinClause W))
    (hA : ∀ C ∈ A, C ∈ F) :
    ∀ (π : List (LinClause W)) (hs : List (Option (ℕ × ℕ × W))), chk A π hs = true →
      IsLinDerivation F π
  | [], _, _ => IsLinDerivation.nil
  | C :: π, none :: hs, h => by
      simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
      exact IsLinDerivation.ax (chk_sound F A hA π hs h.2) (hA _ h.1)
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
          exact IsLinDerivation.res (chk_sound F A hA π hs h2)
            (List.mem_iff_getElem?.mpr ⟨i, hC⟩) (List.mem_iff_getElem?.mpr ⟨j, hD⟩)
            ⟨{v}, m1, m2, m3⟩
  | _ :: _, [], h => by simp [chk] at h

def pig (i : Fin 4) : Clause V := Finset.univ.image (fun j : Fin 3 => ((i, j), true))

def hole (i i' : Fin 4) (j : Fin 3) : Clause V := {((i, j), false), ((i', j), false)}

def triples : List (Fin 4 × Fin 4 × Fin 3) :=
  [(0, 1, 0), (0, 2, 0), (0, 3, 0), (1, 2, 0), (1, 3, 0), (2, 3, 0),
   (0, 1, 1), (0, 2, 1), (0, 3, 1), (1, 2, 1), (1, 3, 1), (2, 3, 1),
   (0, 1, 2), (0, 2, 2), (0, 3, 2), (1, 2, 2), (1, 3, 2), (2, 3, 2)]

theorem triples_ne : ∀ t ∈ triples, t.1 ≠ t.2.1 := by decide

def axList : List (LinClause V) :=
  ((List.finRange 4).map fun i => linOfClause (pig i)) ++
    (triples.map fun t => linOfClause (hole t.1 t.2.1 t.2.2))

theorem axList_sub : ∀ C ∈ axList, C ∈ (fun C => linOfClause C) '' PHP 4 3 := by
  intro C hC
  simp only [axList, List.mem_append, List.mem_map] at hC
  rcases hC with ⟨i, -, rfl⟩ | ⟨t, ht, rfl⟩
  · exact ⟨pig i, Or.inl ⟨i, rfl⟩, rfl⟩
  · exact ⟨hole t.1 t.2.1 t.2.2, Or.inr ⟨t.1, t.2.1, t.2.2, triples_ne t ht, rfl⟩, rfl⟩

def pf : List (LinClause V) :=
  [∅,
   {({(3, 2)}, true)},
   {({(3, 1)}, true), ({(3, 2)}, true)},
   {({(3, 2)}, false)},
   {({(2, 2)}, true), ({(3, 2)}, false)},
   {({(1, 2)}, true), ({(2, 2)}, true), ({(3, 2)}, false)},
   {({(0, 2)}, true), ({(1, 2)}, true), ({(2, 2)}, true)},
   {({(0, 2)}, true), ({(1, 2)}, true), ({(2, 1)}, true), ({(2, 2)}, true)},
   {({(3, 1)}, false)},
   {({(2, 1)}, true), ({(3, 1)}, false)},
   {({(1, 1)}, true), ({(2, 1)}, true), ({(3, 1)}, false)},
   {({(0, 1)}, true), ({(1, 1)}, true), ({(2, 1)}, true)},
   {({(0, 1)}, true), ({(1, 1)}, true), ({(2, 1)}, true), ({(2, 2)}, true)},
   {({(3, 0)}, false)},
   {({(2, 0)}, true), ({(3, 0)}, false)},
   {({(1, 0)}, true), ({(2, 0)}, true), ({(3, 0)}, false)},
   {({(0, 0)}, true), ({(1, 0)}, true), ({(2, 0)}, true)},
   {({(0, 0)}, true), ({(1, 0)}, true), ({(2, 0)}, true), ({(2, 2)}, true)},
   {({(0, 2)}, true), ({(1, 2)}, true), ({(2, 1)}, false)},
   {({(0, 2)}, true), ({(1, 0)}, false), ({(2, 1)}, false)},
   {({(0, 2)}, true), ({(1, 2)}, true), ({(2, 0)}, false)},
   {({(0, 2)}, true), ({(1, 1)}, false), ({(2, 0)}, false)},
   {({(0, 1)}, true), ({(1, 1)}, true), ({(2, 2)}, false)},
   {({(0, 1)}, true), ({(1, 0)}, false), ({(2, 2)}, false)},
   {({(0, 1)}, true), ({(1, 1)}, true), ({(2, 0)}, false)},
   {({(0, 1)}, true), ({(1, 2)}, false), ({(2, 0)}, false)},
   {({(0, 0)}, true), ({(1, 0)}, true), ({(2, 2)}, false)},
   {({(0, 0)}, true), ({(1, 1)}, false), ({(2, 2)}, false)},
   {({(0, 0)}, true), ({(1, 0)}, true), ({(2, 1)}, false)},
   {({(0, 0)}, true), ({(1, 2)}, false), ({(2, 1)}, false)},
   {({(1, 0)}, true), ({(1, 1)}, true), ({(2, 2)}, false)},
   {({(0, 0)}, true), ({(0, 1)}, true), ({(2, 2)}, false)},
   {({(1, 0)}, true), ({(1, 2)}, true), ({(2, 1)}, false)},
   {({(0, 0)}, true), ({(0, 2)}, true), ({(2, 1)}, false)},
   {({(1, 1)}, true), ({(1, 2)}, true), ({(2, 0)}, false)},
   {({(0, 1)}, true), ({(0, 2)}, true), ({(2, 0)}, false)},
   {({(2, 2)}, false), ({(3, 2)}, false)},
   {({(1, 2)}, false), ({(3, 2)}, false)},
   {({(1, 2)}, false), ({(2, 2)}, false)},
   {({(0, 2)}, false), ({(3, 2)}, false)},
   {({(0, 2)}, false), ({(2, 2)}, false)},
   {({(0, 2)}, false), ({(1, 2)}, false)},
   {({(2, 1)}, false), ({(3, 1)}, false)},
   {({(1, 1)}, false), ({(3, 1)}, false)},
   {({(1, 1)}, false), ({(2, 1)}, false)},
   {({(0, 1)}, false), ({(3, 1)}, false)},
   {({(0, 1)}, false), ({(2, 1)}, false)},
   {({(0, 1)}, false), ({(1, 1)}, false)},
   {({(2, 0)}, false), ({(3, 0)}, false)},
   {({(1, 0)}, false), ({(3, 0)}, false)},
   {({(1, 0)}, false), ({(2, 0)}, false)},
   {({(0, 0)}, false), ({(3, 0)}, false)},
   {({(0, 0)}, false), ({(2, 0)}, false)},
   {({(0, 0)}, false), ({(1, 0)}, false)},
   {({(3, 0)}, true), ({(3, 1)}, true), ({(3, 2)}, true)},
   {({(2, 0)}, true), ({(2, 1)}, true), ({(2, 2)}, true)},
   {({(1, 0)}, true), ({(1, 1)}, true), ({(1, 2)}, true)},
   {({(0, 0)}, true), ({(0, 1)}, true), ({(0, 2)}, true)}]

def hints : List (Option (ℕ × ℕ × V)) :=
  [some (2, 0, (3, 2)),
   some (6, 0, (3, 1)),
   some (10, 51, (3, 0)),
   some (32, 0, (2, 2)),
   some (32, 0, (1, 2)),
   some (33, 0, (0, 2)),
   some (11, 0, (2, 1)),
   some (12, 47, (2, 0)),
   some (33, 0, (2, 1)),
   some (33, 0, (1, 1)),
   some (34, 0, (0, 1)),
   some (10, 0, (2, 2)),
   some (11, 42, (2, 0)),
   some (34, 0, (2, 0)),
   some (34, 0, (1, 0)),
   some (35, 0, (0, 0)),
   some (9, 0, (2, 2)),
   some (10, 37, (2, 1)),
   some (0, 13, (1, 0)),
   some (33, 13, (0, 0)),
   some (0, 13, (1, 1)),
   some (25, 13, (0, 1)),
   some (0, 7, (1, 0)),
   some (29, 7, (0, 0)),
   some (0, 9, (1, 2)),
   some (15, 9, (0, 2)),
   some (0, 3, (1, 1)),
   some (19, 3, (0, 1)),
   some (0, 3, (1, 2)),
   some (11, 3, (0, 2)),
   some (7, 25, (1, 2)),
   some (8, 25, (0, 2)),
   some (11, 23, (1, 1)),
   some (12, 23, (0, 1)),
   some (15, 21, (1, 0)),
   some (16, 21, (0, 0)),
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

theorem pf_ok : chk axList pf hints = true := by decide +kernel

theorem pf_empty : (∅ : LinClause V) ∈ pf := by decide +kernel

theorem pf_len : pf.length ≤ 60 := by decide

end PEqualNP.Outside.L_pcx_139

theorem PEqualNP.Outside.L_pcx_139 : ∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 60 := by
  exact ⟨PEqualNP.Outside.L_pcx_139.pf,
    ⟨PEqualNP.Outside.L_pcx_139.chk_sound _ _ PEqualNP.Outside.L_pcx_139.axList_sub _ _
      PEqualNP.Outside.L_pcx_139.pf_ok, PEqualNP.Outside.L_pcx_139.pf_empty⟩,
    PEqualNP.Outside.L_pcx_139.pf_len⟩
