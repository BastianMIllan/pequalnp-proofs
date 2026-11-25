import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9568

open PEqualNP.ProofComplexity

abbrev Cl : Type := Clause (Fin 5)

def satB (S : Finset Cl) : Prop :=
  ∃ b0 b1 b2 b3 b4 : Bool, ∀ C ∈ S, ∃ l ∈ C, (![b0, b1, b2, b3, b4] : Fin 5 → Bool) l.1 = l.2

instance : DecidablePred satB := fun S => by unfold satB; infer_instance

def MUP (S : Finset Cl) : Prop := ¬ satB S ∧ ∀ C ∈ S, satB (S.erase C)

instance : DecidablePred MUP := fun S => by unfold MUP; infer_instance

def taut (D : Cl) : Prop := ∃ v, (v, true) ∈ D ∧ (v, false) ∈ D

instance : DecidablePred taut := fun D => by unfold taut; infer_instance

theorem sat_iff (S : Finset Cl) : Satisfiable (↑S : Set Cl) ↔ satB S := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a 0, a 1, a 2, a 3, a 4, ?_⟩
    have e : (![a 0, a 1, a 2, a 3, a 4] : Fin 5 → Bool) = a := by
      funext i; fin_cases i <;> rfl
    rw [e]
    intro C hC
    exact ha C (Finset.mem_coe.2 hC)
  · rintro ⟨b0, b1, b2, b3, b4, h⟩
    exact ⟨![b0, b1, b2, b3, b4], fun C hC => h C (Finset.mem_coe.1 hC)⟩

theorem mu_iff (S : Finset Cl) :
    (¬ Satisfiable (↑S : Set Cl) ∧ ∀ C ∈ (↑S : Set Cl), Satisfiable ((↑S : Set Cl) \ {C})) ↔
      MUP S := by
  have h : ∀ C, ((↑S : Set Cl) \ {C}) = ↑(S.erase C) := by
    intro C; ext D; simp [and_comm]
  simp only [h, sat_iff, MUP, Finset.mem_coe]

def Fs : Finset Cl := {({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), false), ((3 : Fin 5), false), ((4 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), true), ((1 : Fin 5), false), ((3 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), true), ((1 : Fin 5), false), ((4 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), true), ((1 : Fin 5), true), ((2 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), true), ((1 : Fin 5), true), ((3 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), true), ((2 : Fin 5), false), ((4 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((1 : Fin 5), false), ((2 : Fin 5), false), ((3 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((1 : Fin 5), false), ((2 : Fin 5), false), ((4 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((1 : Fin 5), false), ((2 : Fin 5), true), ((3 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((1 : Fin 5), true), ((3 : Fin 5), true), ((4 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((2 : Fin 5), true), ((3 : Fin 5), true), ((4 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5))}

def Gfix (x : Fin 5) (b : Bool) : Finset Cl :=
  (Fs.filter (fun C => (x, b) ∉ C)).image (fun C => C.filter (fun l => l.1 ≠ x))

def mapL (x y : Fin 5) (p : Bool) (m : Fin 5 × Bool) : Fin 5 × Bool :=
  if m.1 = x then (y, if p then m.2 else !m.2) else m

def Gmerge (x y : Fin 5) (p : Bool) : Finset Cl :=
  (Fs.image (fun C => C.image (mapL x y p))).filter (fun D => ¬ taut D)

def Gelim (x : Fin 5) : Finset Cl :=
  ((Fs.filter (fun D => (x, true) ∉ D ∧ (x, false) ∉ D)) ∪
    ((Fs ×ˢ Fs).filter (fun q => (x, true) ∈ q.1 ∧ (x, false) ∈ q.2)).image
      (fun q => q.1.erase (x, true) ∪ q.2.erase (x, false))).filter (fun D => ¬ taut D)

theorem c1u : ¬ satB Fs := by decide +kernel

theorem w0 : satB (Fs.erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) := ⟨true, false, true, true, true, by decide +kernel⟩

theorem w1 : satB (Fs.erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), true)} : Cl)) := ⟨true, false, true, false, true, by decide +kernel⟩

theorem w2 : satB (Fs.erase ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl)) := ⟨true, true, false, false, true, by decide +kernel⟩

theorem w3 : satB (Fs.erase ({((0 : Fin 5), false), ((3 : Fin 5), false), ((4 : Fin 5), true)} : Cl)) := ⟨true, true, true, true, false, by decide +kernel⟩

theorem w4 : satB (Fs.erase ({((0 : Fin 5), true), ((1 : Fin 5), false), ((3 : Fin 5), true)} : Cl)) := ⟨false, true, false, false, true, by decide +kernel⟩

theorem w5 : satB (Fs.erase ({((0 : Fin 5), true), ((1 : Fin 5), false), ((4 : Fin 5), true)} : Cl)) := ⟨false, true, true, true, false, by decide +kernel⟩

theorem w6 : satB (Fs.erase ({((0 : Fin 5), true), ((1 : Fin 5), true), ((2 : Fin 5), true)} : Cl)) := ⟨false, false, false, false, true, by decide +kernel⟩

theorem w7 : satB (Fs.erase ({((0 : Fin 5), true), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) := ⟨false, false, true, true, false, by decide +kernel⟩

theorem w8 : satB (Fs.erase ({((0 : Fin 5), true), ((2 : Fin 5), false), ((4 : Fin 5), false)} : Cl)) := ⟨false, false, true, false, true, by decide +kernel⟩

theorem w9 : satB (Fs.erase ({((1 : Fin 5), false), ((2 : Fin 5), false), ((3 : Fin 5), true)} : Cl)) := ⟨true, true, true, false, false, by decide +kernel⟩

theorem w10 : satB (Fs.erase ({((1 : Fin 5), false), ((2 : Fin 5), false), ((4 : Fin 5), false)} : Cl)) := ⟨true, true, true, true, true, by decide +kernel⟩

theorem w11 : satB (Fs.erase ({((1 : Fin 5), false), ((2 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) := ⟨false, true, false, true, true, by decide +kernel⟩

theorem w12 : satB (Fs.erase ({((1 : Fin 5), true), ((3 : Fin 5), true), ((4 : Fin 5), true)} : Cl)) := ⟨false, false, true, false, false, by decide +kernel⟩

theorem w13 : satB (Fs.erase ({((2 : Fin 5), true), ((3 : Fin 5), true), ((4 : Fin 5), true)} : Cl)) := ⟨true, true, false, false, false, by decide +kernel⟩

set_option maxHeartbeats 4000000 in
theorem c1w : ∀ C ∈ Fs, satB (Fs.erase C) := by
  intro C hC
  simp only [Fs, Finset.mem_insert, Finset.mem_singleton] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact w0
  · exact w1
  · exact w2
  · exact w3
  · exact w4
  · exact w5
  · exact w6
  · exact w7
  · exact w8
  · exact w9
  · exact w10
  · exact w11
  · exact w12
  · exact w13

theorem c1 : MUP Fs := ⟨c1u, c1w⟩

theorem f00 : ¬ MUP (Gfix 0 false) := fun h =>
  (show ¬ satB ((Gfix 0 false).erase ({((1 : Fin 5), false), ((2 : Fin 5), false), ((3 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((1 : Fin 5), false), ((2 : Fin 5), false), ((3 : Fin 5), true)} : Cl) ∈ Gfix 0 false by decide +kernel))

theorem f01 : ¬ MUP (Gfix 0 true) := fun h =>
  (show ¬ satB ((Gfix 0 true).erase ({((1 : Fin 5), false), ((2 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((1 : Fin 5), false), ((2 : Fin 5), true), ((3 : Fin 5), false)} : Cl) ∈ Gfix 0 true by decide +kernel))

theorem f10 : ¬ MUP (Gfix 1 false) := fun h =>
  (show ¬ satB ((Gfix 1 false).erase ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl) ∈ Gfix 1 false by decide +kernel))

theorem f11 : ¬ MUP (Gfix 1 true) := fun h =>
  (show ¬ satB ((Gfix 1 true).erase ({((0 : Fin 5), true), ((2 : Fin 5), false), ((4 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), true), ((2 : Fin 5), false), ((4 : Fin 5), false)} : Cl) ∈ Gfix 1 true by decide +kernel))

theorem f20 : ¬ MUP (Gfix 2 false) := fun h =>
  (show ¬ satB ((Gfix 2 false).erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl) ∈ Gfix 2 false by decide +kernel))

theorem f21 : ¬ MUP (Gfix 2 true) := fun h =>
  (show ¬ satB ((Gfix 2 true).erase ({((0 : Fin 5), true), ((1 : Fin 5), false), ((3 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), true), ((1 : Fin 5), false), ((3 : Fin 5), true)} : Cl) ∈ Gfix 2 true by decide +kernel))

theorem f30 : ¬ MUP (Gfix 3 false) := fun h =>
  (show ¬ satB ((Gfix 3 false).erase ({((0 : Fin 5), true), ((1 : Fin 5), false), ((4 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), true), ((1 : Fin 5), false), ((4 : Fin 5), true)} : Cl) ∈ Gfix 3 false by decide +kernel))

theorem f31 : ¬ MUP (Gfix 3 true) := fun h =>
  (show ¬ satB ((Gfix 3 true).erase ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl) ∈ Gfix 3 true by decide +kernel))

theorem f40 : ¬ MUP (Gfix 4 false) := fun h =>
  (show ¬ satB ((Gfix 4 false).erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl) ∈ Gfix 4 false by decide +kernel))

theorem f41 : ¬ MUP (Gfix 4 true) := fun h =>
  (show ¬ satB ((Gfix 4 true).erase ({((0 : Fin 5), true), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), true), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl) ∈ Gfix 4 true by decide +kernel))

theorem g010 : ¬ MUP (Gmerge 0 1 false) := fun h =>
  (show ¬ satB ((Gmerge 0 1 false).erase ({((1 : Fin 5), true), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((1 : Fin 5), true), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl) ∈ Gmerge 0 1 false by decide +kernel))

theorem g011 : ¬ MUP (Gmerge 0 1 true) := fun h =>
  (show ¬ satB ((Gmerge 0 1 true).erase ({((1 : Fin 5), false), ((2 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((1 : Fin 5), false), ((2 : Fin 5), true), ((3 : Fin 5), false)} : Cl) ∈ Gmerge 0 1 true by decide +kernel))

theorem g020 : ¬ MUP (Gmerge 0 2 false) := fun h =>
  (show ¬ satB ((Gmerge 0 2 false).erase ({((2 : Fin 5), true), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((2 : Fin 5), true), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl) ∈ Gmerge 0 2 false by decide +kernel))

theorem g021 : ¬ MUP (Gmerge 0 2 true) := fun h =>
  (show ¬ satB ((Gmerge 0 2 true).erase ({((2 : Fin 5), true), ((1 : Fin 5), false), ((4 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((2 : Fin 5), true), ((1 : Fin 5), false), ((4 : Fin 5), true)} : Cl) ∈ Gmerge 0 2 true by decide +kernel))

theorem g030 : ¬ MUP (Gmerge 0 3 false) := fun h =>
  (show ¬ satB ((Gmerge 0 3 false).erase ({((3 : Fin 5), false), ((1 : Fin 5), true), ((2 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((3 : Fin 5), false), ((1 : Fin 5), true), ((2 : Fin 5), true)} : Cl) ∈ Gmerge 0 3 false by decide +kernel))

theorem g031 : ¬ MUP (Gmerge 0 3 true) := fun h =>
  (show ¬ satB ((Gmerge 0 3 true).erase ({((3 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((3 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl) ∈ Gmerge 0 3 true by decide +kernel))

theorem g040 : ¬ MUP (Gmerge 0 4 false) := fun h =>
  (show ¬ satB ((Gmerge 0 4 false).erase ({((4 : Fin 5), true), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((4 : Fin 5), true), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl) ∈ Gmerge 0 4 false by decide +kernel))

theorem g041 : ¬ MUP (Gmerge 0 4 true) := fun h =>
  (show ¬ satB ((Gmerge 0 4 true).erase ({((4 : Fin 5), true), ((1 : Fin 5), false), ((3 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((4 : Fin 5), true), ((1 : Fin 5), false), ((3 : Fin 5), true)} : Cl) ∈ Gmerge 0 4 true by decide +kernel))

theorem g100 : ¬ MUP (Gmerge 1 0 false) := fun h =>
  (show ¬ satB ((Gmerge 1 0 false).erase ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl) ∈ Gmerge 1 0 false by decide +kernel))

theorem g101 : ¬ MUP (Gmerge 1 0 true) := fun h =>
  (show ¬ satB ((Gmerge 1 0 true).erase ({((0 : Fin 5), false), ((2 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((2 : Fin 5), true), ((3 : Fin 5), false)} : Cl) ∈ Gmerge 1 0 true by decide +kernel))

theorem g120 : ¬ MUP (Gmerge 1 2 false) := fun h =>
  (show ¬ satB ((Gmerge 1 2 false).erase ({((0 : Fin 5), false), ((3 : Fin 5), false), ((4 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((3 : Fin 5), false), ((4 : Fin 5), true)} : Cl) ∈ Gmerge 1 2 false by decide +kernel))

theorem g121 : ¬ MUP (Gmerge 1 2 true) := fun h =>
  (show ¬ satB ((Gmerge 1 2 true).erase ({((0 : Fin 5), false), ((2 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((2 : Fin 5), true), ((3 : Fin 5), false)} : Cl) ∈ Gmerge 1 2 true by decide +kernel))

theorem g130 : ¬ MUP (Gmerge 1 3 false) := fun h =>
  (show ¬ satB ((Gmerge 1 3 false).erase ({((0 : Fin 5), false), ((3 : Fin 5), false), ((4 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((3 : Fin 5), false), ((4 : Fin 5), true)} : Cl) ∈ Gmerge 1 3 false by decide +kernel))

theorem g131 : ¬ MUP (Gmerge 1 3 true) := fun h =>
  (show ¬ satB ((Gmerge 1 3 true).erase ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl) ∈ Gmerge 1 3 true by decide +kernel))

theorem g140 : ¬ MUP (Gmerge 1 4 false) := fun h =>
  (show ¬ satB ((Gmerge 1 4 false).erase ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl) ∈ Gmerge 1 4 false by decide +kernel))

theorem g141 : ¬ MUP (Gmerge 1 4 true) := fun h =>
  (show ¬ satB ((Gmerge 1 4 true).erase ({((0 : Fin 5), false), ((4 : Fin 5), true), ((3 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((4 : Fin 5), true), ((3 : Fin 5), true)} : Cl) ∈ Gmerge 1 4 true by decide +kernel))

theorem g200 : ¬ MUP (Gmerge 2 0 false) := fun h =>
  (show ¬ satB ((Gmerge 2 0 false).erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl) ∈ Gmerge 2 0 false by decide +kernel))

theorem g201 : ¬ MUP (Gmerge 2 0 true) := fun h =>
  (show ¬ satB ((Gmerge 2 0 true).erase ({((0 : Fin 5), true), ((1 : Fin 5), false), ((4 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), true), ((1 : Fin 5), false), ((4 : Fin 5), true)} : Cl) ∈ Gmerge 2 0 true by decide +kernel))

theorem g210 : ¬ MUP (Gmerge 2 1 false) := fun h =>
  (show ¬ satB ((Gmerge 2 1 false).erase ({((0 : Fin 5), false), ((3 : Fin 5), false), ((4 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((3 : Fin 5), false), ((4 : Fin 5), true)} : Cl) ∈ Gmerge 2 1 false by decide +kernel))

theorem g211 : ¬ MUP (Gmerge 2 1 true) := fun h =>
  (show ¬ satB ((Gmerge 2 1 true).erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl) ∈ Gmerge 2 1 true by decide +kernel))

theorem g230 : ¬ MUP (Gmerge 2 3 false) := fun h =>
  (show ¬ satB ((Gmerge 2 3 false).erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl) ∈ Gmerge 2 3 false by decide +kernel))

theorem g231 : ¬ MUP (Gmerge 2 3 true) := fun h =>
  (show ¬ satB ((Gmerge 2 3 true).erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), true)} : Cl) ∈ Gmerge 2 3 true by decide +kernel))

theorem g240 : ¬ MUP (Gmerge 2 4 false) := fun h =>
  (show ¬ satB ((Gmerge 2 4 false).erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl) ∈ Gmerge 2 4 false by decide +kernel))

theorem g241 : ¬ MUP (Gmerge 2 4 true) := fun h =>
  (show ¬ satB ((Gmerge 2 4 true).erase ({((0 : Fin 5), false), ((3 : Fin 5), false), ((4 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((3 : Fin 5), false), ((4 : Fin 5), true)} : Cl) ∈ Gmerge 2 4 true by decide +kernel))

theorem g300 : ¬ MUP (Gmerge 3 0 false) := fun h =>
  (show ¬ satB ((Gmerge 3 0 false).erase ({((0 : Fin 5), true), ((1 : Fin 5), true), ((2 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), true), ((1 : Fin 5), true), ((2 : Fin 5), true)} : Cl) ∈ Gmerge 3 0 false by decide +kernel))

theorem g301 : ¬ MUP (Gmerge 3 0 true) := fun h =>
  (show ¬ satB ((Gmerge 3 0 true).erase ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl) ∈ Gmerge 3 0 true by decide +kernel))

theorem g310 : ¬ MUP (Gmerge 3 1 false) := fun h =>
  (show ¬ satB ((Gmerge 3 1 false).erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((4 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((1 : Fin 5), true), ((4 : Fin 5), true)} : Cl) ∈ Gmerge 3 1 false by decide +kernel))

theorem g311 : ¬ MUP (Gmerge 3 1 true) := fun h =>
  (show ¬ satB ((Gmerge 3 1 true).erase ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : Cl) ∈ Gmerge 3 1 true by decide +kernel))

theorem g320 : ¬ MUP (Gmerge 3 2 false) := fun h =>
  (show ¬ satB ((Gmerge 3 2 false).erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((2 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((1 : Fin 5), true), ((2 : Fin 5), true)} : Cl) ∈ Gmerge 3 2 false by decide +kernel))

theorem g321 : ¬ MUP (Gmerge 3 2 true) := fun h =>
  (show ¬ satB ((Gmerge 3 2 true).erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((2 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((1 : Fin 5), true), ((2 : Fin 5), true)} : Cl) ∈ Gmerge 3 2 true by decide +kernel))

theorem g340 : ¬ MUP (Gmerge 3 4 false) := fun h =>
  (show ¬ satB ((Gmerge 3 4 false).erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((4 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((1 : Fin 5), true), ((4 : Fin 5), true)} : Cl) ∈ Gmerge 3 4 false by decide +kernel))

theorem g341 : ¬ MUP (Gmerge 3 4 true) := fun h =>
  (show ¬ satB ((Gmerge 3 4 true).erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((4 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((1 : Fin 5), true), ((4 : Fin 5), true)} : Cl) ∈ Gmerge 3 4 true by decide +kernel))

theorem g400 : ¬ MUP (Gmerge 4 0 false) := fun h =>
  (show ¬ satB ((Gmerge 4 0 false).erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl) ∈ Gmerge 4 0 false by decide +kernel))

theorem g401 : ¬ MUP (Gmerge 4 0 true) := fun h =>
  (show ¬ satB ((Gmerge 4 0 true).erase ({((0 : Fin 5), true), ((1 : Fin 5), false), ((3 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), true), ((1 : Fin 5), false), ((3 : Fin 5), true)} : Cl) ∈ Gmerge 4 0 true by decide +kernel))

theorem g410 : ¬ MUP (Gmerge 4 1 false) := fun h =>
  (show ¬ satB ((Gmerge 4 1 false).erase ({((0 : Fin 5), false), ((2 : Fin 5), true), ((1 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((2 : Fin 5), true), ((1 : Fin 5), true)} : Cl) ∈ Gmerge 4 1 false by decide +kernel))

theorem g411 : ¬ MUP (Gmerge 4 1 true) := fun h =>
  (show ¬ satB ((Gmerge 4 1 true).erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), true)} : Cl) ∈ Gmerge 4 1 true by decide +kernel))

theorem g420 : ¬ MUP (Gmerge 4 2 false) := fun h =>
  (show ¬ satB ((Gmerge 4 2 false).erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl) ∈ Gmerge 4 2 false by decide +kernel))

theorem g421 : ¬ MUP (Gmerge 4 2 true) := fun h =>
  (show ¬ satB ((Gmerge 4 2 true).erase ({((0 : Fin 5), false), ((3 : Fin 5), false), ((2 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((3 : Fin 5), false), ((2 : Fin 5), true)} : Cl) ∈ Gmerge 4 2 true by decide +kernel))

theorem g430 : ¬ MUP (Gmerge 4 3 false) := fun h =>
  (show ¬ satB ((Gmerge 4 3 false).erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : Cl) ∈ Gmerge 4 3 false by decide +kernel))

theorem g431 : ¬ MUP (Gmerge 4 3 true) := fun h =>
  (show ¬ satB ((Gmerge 4 3 true).erase ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), true)} : Cl) ∈ Gmerge 4 3 true by decide +kernel))

theorem e0 : ¬ MUP (Gelim 0) := fun h =>
  (show ¬ satB ((Gelim 0).erase ({((1 : Fin 5), true), ((2 : Fin 5), true), ((3 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((1 : Fin 5), true), ((2 : Fin 5), true), ((3 : Fin 5), false)} : Cl) ∈ Gelim 0 by decide +kernel))

theorem e1 : ¬ MUP (Gelim 1) := fun h =>
  (show ¬ satB ((Gelim 1).erase ({((0 : Fin 5), false), ((3 : Fin 5), false), ((2 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((3 : Fin 5), false), ((2 : Fin 5), true)} : Cl) ∈ Gelim 1 by decide +kernel))

theorem e2 : ¬ MUP (Gelim 2) := fun h =>
  (show ¬ satB ((Gelim 2).erase ({((0 : Fin 5), false), ((4 : Fin 5), false), ((1 : Fin 5), false), ((3 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((4 : Fin 5), false), ((1 : Fin 5), false), ((3 : Fin 5), true)} : Cl) ∈ Gelim 2 by decide +kernel))

theorem e3 : ¬ MUP (Gelim 3) := fun h =>
  (show ¬ satB ((Gelim 3).erase ({((1 : Fin 5), true), ((4 : Fin 5), true), ((0 : Fin 5), false)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((1 : Fin 5), true), ((4 : Fin 5), true), ((0 : Fin 5), false)} : Cl) ∈ Gelim 3 by decide +kernel))

theorem e4 : ¬ MUP (Gelim 4) := fun h =>
  (show ¬ satB ((Gelim 4).erase ({((0 : Fin 5), false), ((3 : Fin 5), false), ((2 : Fin 5), true)} : Cl)) by decide +kernel)
    (h.2 _ (show ({((0 : Fin 5), false), ((3 : Fin 5), false), ((2 : Fin 5), true)} : Cl) ∈ Gelim 4 by decide +kernel))

theorem c2 : ∀ x b, ¬ MUP (Gfix x b) := by
  intro x b
  fin_cases x <;> cases b
  · exact f00
  · exact f01
  · exact f10
  · exact f11
  · exact f20
  · exact f21
  · exact f30
  · exact f31
  · exact f40
  · exact f41

theorem c3 : ∀ x y p, x ≠ y → ¬ MUP (Gmerge x y p) := by
  intro x y p hxy
  fin_cases x <;> fin_cases y <;> cases p
  · exact absurd rfl hxy
  · exact absurd rfl hxy
  · exact g010
  · exact g011
  · exact g020
  · exact g021
  · exact g030
  · exact g031
  · exact g040
  · exact g041
  · exact g100
  · exact g101
  · exact absurd rfl hxy
  · exact absurd rfl hxy
  · exact g120
  · exact g121
  · exact g130
  · exact g131
  · exact g140
  · exact g141
  · exact g200
  · exact g201
  · exact g210
  · exact g211
  · exact absurd rfl hxy
  · exact absurd rfl hxy
  · exact g230
  · exact g231
  · exact g240
  · exact g241
  · exact g300
  · exact g301
  · exact g310
  · exact g311
  · exact g320
  · exact g321
  · exact absurd rfl hxy
  · exact absurd rfl hxy
  · exact g340
  · exact g341
  · exact g400
  · exact g401
  · exact g410
  · exact g411
  · exact g420
  · exact g421
  · exact g430
  · exact g431
  · exact absurd rfl hxy
  · exact absurd rfl hxy

theorem c4 : ∀ x, ¬ MUP (Gelim x) := by
  intro x
  fin_cases x
  · exact e0
  · exact e1
  · exact e2
  · exact e3
  · exact e4

theorem fs_eq : ({({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), false), ((3 : Fin 5), false), ((4 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), true), ((1 : Fin 5), false), ((3 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), true), ((1 : Fin 5), false), ((4 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), true), ((1 : Fin 5), true), ((2 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), true), ((1 : Fin 5), true), ((3 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), true), ((2 : Fin 5), false), ((4 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((1 : Fin 5), false), ((2 : Fin 5), false), ((3 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((1 : Fin 5), false), ((2 : Fin 5), false), ((4 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((1 : Fin 5), false), ((2 : Fin 5), true), ((3 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((1 : Fin 5), true), ((3 : Fin 5), true), ((4 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((2 : Fin 5), true), ((3 : Fin 5), true), ((4 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5))} : Set Cl) = ↑Fs := by
  simp only [Fs, Finset.coe_insert, Finset.coe_singleton]

end PEqualNP.Outside.L_meta_9568

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_9568 : ∀ F : Set (PEqualNP.ProofComplexity.Clause (Fin 5)), F = {({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), false), ((1 : Fin 5), true), ((3 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), false), ((2 : Fin 5), true), ((4 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), false), ((3 : Fin 5), false), ((4 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), true), ((1 : Fin 5), false), ((3 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), true), ((1 : Fin 5), false), ((4 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), true), ((1 : Fin 5), true), ((2 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), true), ((1 : Fin 5), true), ((3 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((0 : Fin 5), true), ((2 : Fin 5), false), ((4 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((1 : Fin 5), false), ((2 : Fin 5), false), ((3 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((1 : Fin 5), false), ((2 : Fin 5), false), ((4 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((1 : Fin 5), false), ((2 : Fin 5), true), ((3 : Fin 5), false)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((1 : Fin 5), true), ((3 : Fin 5), true), ((4 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5)), ({((2 : Fin 5), true), ((3 : Fin 5), true), ((4 : Fin 5), true)} : PEqualNP.ProofComplexity.Clause (Fin 5))} → (¬ PEqualNP.ProofComplexity.Satisfiable F ∧ ∀ C ∈ F, PEqualNP.ProofComplexity.Satisfiable (F \ {C})) ∧ (∀ (x : Fin 5) (b : Bool) (G : Set (PEqualNP.ProofComplexity.Clause (Fin 5))), G = (fun C : PEqualNP.ProofComplexity.Clause (Fin 5) => C.filter (fun l => l.1 ≠ x)) '' {C | C ∈ F ∧ (x, b) ∉ C} → ¬ (¬ PEqualNP.ProofComplexity.Satisfiable G ∧ ∀ C ∈ G, PEqualNP.ProofComplexity.Satisfiable (G \ {C}))) ∧ (∀ (x y : Fin 5) (p : Bool) (G : Set (PEqualNP.ProofComplexity.Clause (Fin 5))), x ≠ y → G = {D | (∃ C ∈ F, D = C.image (fun m => if m.1 = x then (y, if p then m.2 else !m.2) else m)) ∧ ¬ ∃ v, (v, true) ∈ D ∧ (v, false) ∈ D} → ¬ (¬ PEqualNP.ProofComplexity.Satisfiable G ∧ ∀ C ∈ G, PEqualNP.ProofComplexity.Satisfiable (G \ {C}))) ∧ (∀ (x : Fin 5) (G : Set (PEqualNP.ProofComplexity.Clause (Fin 5))), G = {D | ((D ∈ F ∧ (x, true) ∉ D ∧ (x, false) ∉ D) ∨ ∃ C ∈ F, ∃ E ∈ F, (x, true) ∈ C ∧ (x, false) ∈ E ∧ D = C.erase (x, true) ∪ E.erase (x, false)) ∧ ¬ ∃ v, (v, true) ∈ D ∧ (v, false) ∈ D} → ¬ (¬ PEqualNP.ProofComplexity.Satisfiable G ∧ ∀ C ∈ G, PEqualNP.ProofComplexity.Satisfiable (G \ {C}))) := by
  intro F hF
  rw [PEqualNP.Outside.L_meta_9568.fs_eq] at hF
  subst hF
  refine ⟨(PEqualNP.Outside.L_meta_9568.mu_iff _).2 PEqualNP.Outside.L_meta_9568.c1, ?_, ?_, ?_⟩
  · intro x b G hG
    have h : G = ↑(PEqualNP.Outside.L_meta_9568.Gfix x b) := by
      rw [hG]; ext D
      simp [PEqualNP.Outside.L_meta_9568.Gfix]
    rw [h, PEqualNP.Outside.L_meta_9568.mu_iff]
    exact PEqualNP.Outside.L_meta_9568.c2 x b
  · intro x y p G hxy hG
    have h : G = ↑(PEqualNP.Outside.L_meta_9568.Gmerge x y p) := by
      rw [hG]; ext D
      constructor
      · rintro ⟨⟨C, hC, rfl⟩, h2⟩
        rw [Finset.mem_coe, PEqualNP.Outside.L_meta_9568.Gmerge, Finset.mem_filter,
          Finset.mem_image]
        exact ⟨⟨C, hC, rfl⟩, h2⟩
      · intro hD
        rw [Finset.mem_coe, PEqualNP.Outside.L_meta_9568.Gmerge, Finset.mem_filter,
          Finset.mem_image] at hD
        obtain ⟨⟨C, hC, rfl⟩, h2⟩ := hD
        exact ⟨⟨C, hC, rfl⟩, h2⟩
    rw [h, PEqualNP.Outside.L_meta_9568.mu_iff]
    exact PEqualNP.Outside.L_meta_9568.c3 x y p hxy
  · intro x G hG
    have h : G = ↑(PEqualNP.Outside.L_meta_9568.Gelim x) := by
      rw [hG]; ext D
      constructor
      · rintro ⟨h1 | ⟨C, hC, E, hE, h3, h4, rfl⟩, h2⟩
        · rw [Finset.mem_coe, PEqualNP.Outside.L_meta_9568.Gelim]
          exact Finset.mem_filter.2 ⟨Finset.mem_union.2
            (Or.inl (Finset.mem_filter.2 ⟨h1.1, h1.2.1, h1.2.2⟩)), h2⟩
        · rw [Finset.mem_coe, PEqualNP.Outside.L_meta_9568.Gelim]
          exact Finset.mem_filter.2 ⟨Finset.mem_union.2 (Or.inr (Finset.mem_image.2
            ⟨(C, E), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hC, hE⟩, h3, h4⟩, rfl⟩)), h2⟩
      · intro hD
        rw [Finset.mem_coe, PEqualNP.Outside.L_meta_9568.Gelim] at hD
        obtain ⟨hU, h2⟩ := Finset.mem_filter.1 hD
        rcases Finset.mem_union.1 hU with h1 | h1
        · obtain ⟨h1a, h1b⟩ := Finset.mem_filter.1 h1
          exact ⟨Or.inl ⟨h1a, h1b.1, h1b.2⟩, h2⟩
        · obtain ⟨⟨C, E⟩, hq, rfl⟩ := Finset.mem_image.1 h1
          obtain ⟨hq1, h3, h4⟩ := Finset.mem_filter.1 hq
          obtain ⟨hC, hE⟩ := Finset.mem_product.1 hq1
          exact ⟨Or.inr ⟨C, hC, E, hE, h3, h4, rfl⟩, h2⟩
    rw [h, PEqualNP.Outside.L_meta_9568.mu_iff]
    exact PEqualNP.Outside.L_meta_9568.c4 x
