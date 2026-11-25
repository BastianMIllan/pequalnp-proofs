import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8335

def E : List ℕ := [7, 8, 10, 21, 23, 27, 36, 40, 41, 49, 53, 54, 66, 67, 69, 79, 80, 82, 92, 93, 95]

def L : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]

theorem key : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, ∃ x3 ∈ L,
    (b0 = true → x3.testBit 0 = true) ∧ (b1 = true → x3.testBit 1 = true) ∧
    (b2 = true → x3.testBit 2 = true) ∧ (b3 = true → x3.testBit 3 = true) ∧
    (b4 = true → x3.testBit 4 = true) ∧ (b5 = true → x3.testBit 5 = true) ∧
    (b6 = true → x3.testBit 6 = true) ∧
    ((b0 || b1 || b3) = false → x3.testBit 7 = true) ∧
    ((b0 || b2 || b6) = false → x3.testBit 8 = true) ∧
    ((b1 || b5 || b6) = false → x3.testBit 9 = true) ∧
    ((b0 || b4 || b5) = false → x3.testBit 10 = true) ∧
    ((b3 || b4 || b6) = false → x3.testBit 11 = true) ∧
    ((b2 || b3 || b5) = false → x3.testBit 12 = true) ∧
    ((b1 || b2 || b4) = false → x3.testBit 13 = true) := by
  intro b0 b1 b2 b3 b4 b5 b6
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> decide

theorem nb (x1 : Fin 14 → Bool)
    (hind : ¬∃ (a : Fin 14) (b : Fin 14), 14 * a.val + b.val ∈ E ∧ x1 a = true ∧ x1 b = true)
    (a b : Fin 14) (hab : 14 * a.val + b.val ∈ E) (hb : x1 b = true) : x1 a = false := by
  cases h : x1 a
  · rfl
  · exact absurd ⟨a, b, hab, h, hb⟩ hind

end PEqualNP.Outside.L_meta_8335

theorem PEqualNP.Outside.L_meta_8335 : ∀ (x1 : Fin (14 : ℕ) → Bool),   (¬∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), (14 : ℕ) * ↑x2 + ↑x3 ∈ [(7 : ℕ), (8 : ℕ), (10 : ℕ), (21 : ℕ), (23 : ℕ), (27 : ℕ), (36 : ℕ), (40 : ℕ), (41 : ℕ), (49 : ℕ), (53 : ℕ), (54 : ℕ), (66 : ℕ), (67 : ℕ), (69 : ℕ), (79 : ℕ), (80 : ℕ), (82 : ℕ), (92 : ℕ), (93 : ℕ), (95 : ℕ)] ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true) →     ∃       x3 ∈         have x4 : List ℕ :=           have x4 : List ℕ :=             have x4 : List ℕ := [(10656 : ℕ), (12353 : ℕ), (13504 : ℕ), (14849 : ℕ), (16256 : ℕ)];             (8488 : ℕ) :: (8713 : ℕ) :: (9288 : ℕ) :: (9992 : ℕ) :: (10273 : ℕ) :: x4;           have x5 : List ℕ := (5186 : ℕ) :: (6147 : ℕ) :: (7426 : ℕ) :: (8297 : ℕ) :: (8416 : ℕ) :: x4;           (4304 : ℕ) :: (4370 : ℕ) :: (4625 : ℕ) :: (5008 : ℕ) :: x5;         have x5 : List ℕ :=           have x5 : List ℕ := (2338 : ℕ) :: (2565 : ℕ) :: (3078 : ℕ) :: (3716 : ℕ) :: (4179 : ℕ) :: x4;           (1290 : ℕ) :: (1548 : ℕ) :: (2087 : ℕ) :: (2212 : ℕ) :: x5;         have x6 : List ℕ := (541 : ℕ) :: (660 : ℕ) :: (792 : ℕ) :: (1102 : ℕ) :: (1220 : ℕ) :: x5;         (127 : ℕ) :: (244 : ℕ) :: (314 : ℕ) :: (432 : ℕ) :: x6,       ∀ (x4 : Fin (14 : ℕ)), x1 x4 = Bool.true → x3.testBit ↑x4 = Bool.true := by
  intro x1 hind
  have hind' : ¬∃ (a : Fin 14) (b : Fin 14),
      14 * a.val + b.val ∈ PEqualNP.Outside.L_meta_8335.E ∧ x1 a = true ∧ x1 b = true := hind
  have nb := PEqualNP.Outside.L_meta_8335.nb x1 hind'
  obtain ⟨x3, hmem, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    PEqualNP.Outside.L_meta_8335.key (x1 0) (x1 1) (x1 2) (x1 3) (x1 4) (x1 5) (x1 6)
  refine ⟨x3, hmem, ?_⟩
  intro i hi
  match i, hi with
  | ⟨0, _⟩, hi => exact h0 hi
  | ⟨1, _⟩, hi => exact h1 hi
  | ⟨2, _⟩, hi => exact h2 hi
  | ⟨3, _⟩, hi => exact h3 hi
  | ⟨4, _⟩, hi => exact h4 hi
  | ⟨5, _⟩, hi => exact h5 hi
  | ⟨6, _⟩, hi => exact h6 hi
  | ⟨7, _⟩, hi =>
    exact h7 (by rw [nb 0 7 (by decide) hi, nb 1 7 (by decide) hi, nb 3 7 (by decide) hi]; rfl)
  | ⟨8, _⟩, hi =>
    exact h8 (by rw [nb 0 8 (by decide) hi, nb 2 8 (by decide) hi, nb 6 8 (by decide) hi]; rfl)
  | ⟨9, _⟩, hi =>
    exact h9 (by rw [nb 1 9 (by decide) hi, nb 5 9 (by decide) hi, nb 6 9 (by decide) hi]; rfl)
  | ⟨10, _⟩, hi =>
    exact h10 (by rw [nb 0 10 (by decide) hi, nb 4 10 (by decide) hi, nb 5 10 (by decide) hi]; rfl)
  | ⟨11, _⟩, hi =>
    exact h11 (by rw [nb 3 11 (by decide) hi, nb 4 11 (by decide) hi, nb 6 11 (by decide) hi]; rfl)
  | ⟨12, _⟩, hi =>
    exact h12 (by rw [nb 2 12 (by decide) hi, nb 3 12 (by decide) hi, nb 5 12 (by decide) hi]; rfl)
  | ⟨13, _⟩, hi =>
    exact h13 (by rw [nb 1 13 (by decide) hi, nb 2 13 (by decide) hi, nb 4 13 (by decide) hi]; rfl)
