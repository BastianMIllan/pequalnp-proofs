import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9549

open PEqualNP.ProofComplexity

abbrev Cl : Type := Clause (Fin 4)

def satB (S : Finset Cl) : Prop := ∃ a : Fin 4 → Bool, ∀ C ∈ S, ∃ l ∈ C, a l.1 = l.2

instance : DecidablePred satB := fun S => by unfold satB; infer_instance

def MUP (S : Finset Cl) : Prop := ¬ satB S ∧ ∀ C ∈ S, satB (S.erase C)

instance : DecidablePred MUP := fun S => by unfold MUP; infer_instance

def taut (D : Cl) : Prop := ∃ v, (v, true) ∈ D ∧ (v, false) ∈ D

instance : DecidablePred taut := fun D => by unfold taut; infer_instance

theorem sat_iff (S : Finset Cl) : Satisfiable (↑S : Set Cl) ↔ satB S := by
  simp [Satisfiable, Satisfies, ClauseSat, satB]

theorem mu_iff (S : Finset Cl) :
    (¬ Satisfiable (↑S : Set Cl) ∧ ∀ C ∈ (↑S : Set Cl), Satisfiable ((↑S : Set Cl) \ {C})) ↔
      MUP S := by
  have h : ∀ C, ((↑S : Set Cl) \ {C}) = ↑(S.erase C) := by
    intro C; ext D; simp [and_comm]
  simp only [h, sat_iff, MUP, Finset.mem_coe]

def Fs : Finset Cl := {({((0 : Fin 4), true), ((1 : Fin 4), true), ((2 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((1 : Fin 4), true), ((2 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((1 : Fin 4), false), ((2 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((1 : Fin 4), false), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((1 : Fin 4), true), ((2 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((2 : Fin 4), false), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((1 : Fin 4), false), ((2 : Fin 4), false), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((2 : Fin 4), true), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((1 : Fin 4), true), ((2 : Fin 4), false), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((1 : Fin 4), false), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((1 : Fin 4), false), ((2 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4))}

def Gfix (x : Fin 4) (b : Bool) : Finset Cl :=
  (Fs.filter (fun C => (x, b) ∉ C)).image (fun C => C.filter (fun l => l.1 ≠ x))

def mapL (x y : Fin 4) (p : Bool) (m : Fin 4 × Bool) : Fin 4 × Bool :=
  if m.1 = x then (y, if p then m.2 else !m.2) else m

def Gmerge (x y : Fin 4) (p : Bool) : Finset Cl :=
  (Fs.image (fun C => C.image (mapL x y p))).filter (fun D => ¬ taut D)

theorem c1 : MUP Fs := by decide +kernel

theorem c2 : ∀ x b, ¬ MUP (Gfix x b) := by decide +kernel

theorem m01 : ∀ p, ¬ MUP (Gmerge 0 1 p) := by decide +kernel

theorem m02 : ∀ p, ¬ MUP (Gmerge 0 2 p) := by decide +kernel

theorem m03 : ∀ p, ¬ MUP (Gmerge 0 3 p) := by decide +kernel

theorem m10 : ∀ p, ¬ MUP (Gmerge 1 0 p) := by decide +kernel

theorem m12 : ∀ p, ¬ MUP (Gmerge 1 2 p) := by decide +kernel

theorem m13 : ∀ p, ¬ MUP (Gmerge 1 3 p) := by decide +kernel

theorem m20 : ∀ p, ¬ MUP (Gmerge 2 0 p) := by decide +kernel

theorem m21 : ∀ p, ¬ MUP (Gmerge 2 1 p) := by decide +kernel

theorem m23 : ∀ p, ¬ MUP (Gmerge 2 3 p) := by decide +kernel

theorem m30 : ∀ p, ¬ MUP (Gmerge 3 0 p) := by decide +kernel

theorem m31 : ∀ p, ¬ MUP (Gmerge 3 1 p) := by decide +kernel

theorem m32 : ∀ p, ¬ MUP (Gmerge 3 2 p) := by decide +kernel

theorem c3 : ∀ x y p, x ≠ y → ¬ MUP (Gmerge x y p) := by
  intro x y p hxy
  fin_cases x <;> fin_cases y
  · exact absurd rfl hxy
  · exact m01 p
  · exact m02 p
  · exact m03 p
  · exact m10 p
  · exact absurd rfl hxy
  · exact m12 p
  · exact m13 p
  · exact m20 p
  · exact m21 p
  · exact absurd rfl hxy
  · exact m23 p
  · exact m30 p
  · exact m31 p
  · exact m32 p
  · exact absurd rfl hxy

theorem fs_eq : ({({((0 : Fin 4), true), ((1 : Fin 4), true), ((2 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((1 : Fin 4), true), ((2 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((1 : Fin 4), false), ((2 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((1 : Fin 4), false), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((1 : Fin 4), true), ((2 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((2 : Fin 4), false), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((1 : Fin 4), false), ((2 : Fin 4), false), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((2 : Fin 4), true), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((1 : Fin 4), true), ((2 : Fin 4), false), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((1 : Fin 4), false), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((1 : Fin 4), false), ((2 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4))} : Set Cl) = ↑Fs := by
  simp only [Fs, Finset.coe_insert, Finset.coe_singleton]

end PEqualNP.Outside.L_meta_9549

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_9549 : ∀ F : Set (PEqualNP.ProofComplexity.Clause (Fin 4)), F = {({((0 : Fin 4), true), ((1 : Fin 4), true), ((2 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((1 : Fin 4), true), ((2 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((1 : Fin 4), false), ((2 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((1 : Fin 4), false), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((1 : Fin 4), true), ((2 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((2 : Fin 4), false), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((1 : Fin 4), false), ((2 : Fin 4), false), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((2 : Fin 4), true), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((1 : Fin 4), true), ((2 : Fin 4), false), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((1 : Fin 4), false), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((1 : Fin 4), false), ((2 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4))} → (¬ PEqualNP.ProofComplexity.Satisfiable F ∧ ∀ C ∈ F, PEqualNP.ProofComplexity.Satisfiable (F \ {C})) ∧ (∀ (x : Fin 4) (b : Bool) (G : Set (PEqualNP.ProofComplexity.Clause (Fin 4))), G = (fun C : PEqualNP.ProofComplexity.Clause (Fin 4) => C.filter (fun l => l.1 ≠ x)) '' {C | C ∈ F ∧ (x, b) ∉ C} → ¬ (¬ PEqualNP.ProofComplexity.Satisfiable G ∧ ∀ C ∈ G, PEqualNP.ProofComplexity.Satisfiable (G \ {C}))) ∧ (∀ (x y : Fin 4) (p : Bool) (G : Set (PEqualNP.ProofComplexity.Clause (Fin 4))), x ≠ y → G = {D | (∃ C ∈ F, D = C.image (fun m => if m.1 = x then (y, if p then m.2 else !m.2) else m)) ∧ ¬ ∃ v, (v, true) ∈ D ∧ (v, false) ∈ D} → ¬ (¬ PEqualNP.ProofComplexity.Satisfiable G ∧ ∀ C ∈ G, PEqualNP.ProofComplexity.Satisfiable (G \ {C}))) := by
  intro F hF
  rw [PEqualNP.Outside.L_meta_9549.fs_eq] at hF
  subst hF
  refine ⟨(PEqualNP.Outside.L_meta_9549.mu_iff _).2 PEqualNP.Outside.L_meta_9549.c1, ?_, ?_⟩
  · intro x b G hG
    have h : G = ↑(PEqualNP.Outside.L_meta_9549.Gfix x b) := by
      rw [hG]; ext D
      simp [PEqualNP.Outside.L_meta_9549.Gfix]
    rw [h, PEqualNP.Outside.L_meta_9549.mu_iff]
    exact PEqualNP.Outside.L_meta_9549.c2 x b
  · intro x y p G hxy hG
    have h : G = ↑(PEqualNP.Outside.L_meta_9549.Gmerge x y p) := by
      rw [hG]; ext D
      constructor
      · rintro ⟨⟨C, hC, rfl⟩, h2⟩
        rw [Finset.mem_coe, PEqualNP.Outside.L_meta_9549.Gmerge, Finset.mem_filter,
          Finset.mem_image]
        exact ⟨⟨C, hC, rfl⟩, h2⟩
      · intro hD
        rw [Finset.mem_coe, PEqualNP.Outside.L_meta_9549.Gmerge, Finset.mem_filter,
          Finset.mem_image] at hD
        obtain ⟨⟨C, hC, rfl⟩, h2⟩ := hD
        exact ⟨⟨C, hC, rfl⟩, h2⟩
    rw [h, PEqualNP.Outside.L_meta_9549.mu_iff]
    exact PEqualNP.Outside.L_meta_9549.c3 x y p hxy
