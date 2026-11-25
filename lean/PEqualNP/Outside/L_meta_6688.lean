import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_6688 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Fin (x1 + x2)) (x5 : Finset (Fin x1 × Fin x2)), x5 = {x6 ∈ x3 | ¬(Fin.castAdd x2 x6.1 = x4 ∨ Fin.natAdd x1 x6.2 = x4)} → {x7 ∈ x3 | Fin.castAdd x2 x7.1 = x4 ∨ Fin.natAdd x1 x7.2 = x4}.card = (1 : ℕ) → x5.card < x3.card := by
  intro x1 x2 x3 x4 x5 h5 h1
  subst h5
  have key := Finset.card_filter_add_card_filter_not (s := x3)
    (fun x7 : Fin x1 × Fin x2 => Fin.castAdd x2 x7.1 = x4 ∨ Fin.natAdd x1 x7.2 = x4)
  omega
