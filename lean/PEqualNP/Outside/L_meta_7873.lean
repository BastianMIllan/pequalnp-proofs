import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7873_aux

def D : Finset (Fin 13) := {0, 1, 3, 9}

theorem key : ∀ a b c d : Fin 13, a < b → b < c → c < d →
    (Finset.univ.filter (fun x : Fin 13 =>
      a + x ∉ D ∧ b + x ∉ D ∧ c + x ∉ D ∧ d + x ∉ D)).card ≤ 3 := by
  decide +kernel

end PEqualNP.Outside.L_meta_7873_aux

open PEqualNP.Outside.L_meta_7873_aux in
theorem PEqualNP.Outside.L_meta_7873 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 : Finset (Fin (13 : ℕ))),   x2.card = (4 : ℕ) →     have x4 : Finset (Fin (13 : ℕ)) := {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x2, x5 + x4 ∉ x1};     x4.card ≤ (3 : ℕ) := by
  show ∀ (x2 : Finset (Fin 13)), x2.card = 4 →
    (Finset.univ.filter (fun x4 : Fin 13 => ∀ x5 ∈ x2, x5 + x4 ∉ D)).card ≤ 3
  intro x2 h
  set f := x2.orderEmbOfFin h with hf
  have hmem : ∀ x, x ∈ x2 ↔ ∃ i : Fin 4, f i = x := by
    intro x
    have := congrArg (fun s : Set (Fin 13) => x ∈ s) (Finset.range_orderEmbOfFin x2 h)
    simp only [Set.mem_range, Finset.mem_coe] at this
    rw [← this]
  have hmono : StrictMono f := f.strictMono
  have h01 : f 0 < f 1 := hmono (by decide)
  have h12 : f 1 < f 2 := hmono (by decide)
  have h23 : f 2 < f 3 := hmono (by decide)
  have heq : (Finset.univ.filter (fun x4 : Fin 13 => ∀ x5 ∈ x2, x5 + x4 ∉ D)) =
      Finset.univ.filter (fun x : Fin 13 =>
        f 0 + x ∉ D ∧ f 1 + x ∉ D ∧ f 2 + x ∉ D ∧ f 3 + x ∉ D) := by
    apply Finset.filter_congr
    intro x _
    constructor
    · intro hx
      exact ⟨hx _ ((hmem _).2 ⟨0, rfl⟩), hx _ ((hmem _).2 ⟨1, rfl⟩),
        hx _ ((hmem _).2 ⟨2, rfl⟩), hx _ ((hmem _).2 ⟨3, rfl⟩)⟩
    · rintro ⟨e0, e1, e2, e3⟩ y hy
      obtain ⟨i, rfl⟩ := (hmem y).1 hy
      fin_cases i
      · exact e0
      · exact e1
      · exact e2
      · exact e3
  rw [heq]
  exact key _ _ _ _ h01 h12 h23
