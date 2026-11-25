import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6949

def mins {n : ℕ} (S : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  {x ∈ S | ∀ y ∈ S, y ⊆ x → x ⊆ y}

theorem mins_sub {n : ℕ} (S : Finset (Finset (Fin n))) : mins S ⊆ S :=
  Finset.filter_subset _ _

theorem exists_min {n : ℕ} (S : Finset (Finset (Fin n))) :
    ∀ k : ℕ, ∀ s ∈ S, s.card ≤ k → ∃ m ∈ mins S, m ⊆ s := by
  intro k
  induction k with
  | zero =>
    intro s hs hk
    by_cases hm : ∀ y ∈ S, y ⊆ s → s ⊆ y
    · exact ⟨s, Finset.mem_filter.mpr ⟨hs, hm⟩, Finset.Subset.refl _⟩
    · push_neg at hm
      obtain ⟨y, _, hys, hsy⟩ := hm
      have hlt : y.card < s.card := Finset.card_lt_card ⟨hys, hsy⟩
      omega
  | succ k ih =>
    intro s hs hk
    by_cases hm : ∀ y ∈ S, y ⊆ s → s ⊆ y
    · exact ⟨s, Finset.mem_filter.mpr ⟨hs, hm⟩, Finset.Subset.refl _⟩
    · push_neg at hm
      obtain ⟨y, hy, hys, hsy⟩ := hm
      have hlt : y.card < s.card := Finset.card_lt_card ⟨hys, hsy⟩
      obtain ⟨m, hm, hmy⟩ := ih y hy (by omega)
      exact ⟨m, hm, hmy.trans hys⟩

theorem cover {n : ℕ} (S : Finset (Finset (Fin n))) : ∀ s ∈ S, ∃ m ∈ mins S, m ⊆ s :=
  fun s hs => exists_min S s.card s hs le_rfl

theorem mins_eq {n : ℕ} (S T : Finset (Finset (Fin n))) (hTS : T ⊆ S)
    (hcov : ∀ s ∈ S, ∃ t ∈ T, t ⊆ s) : mins S = mins T := by
  ext x
  simp only [mins, Finset.mem_filter]
  constructor
  · rintro ⟨hxS, hmin⟩
    obtain ⟨t, ht, htx⟩ := hcov x hxS
    have hxt : x ⊆ t := hmin t (hTS ht) htx
    have hx : x = t := Finset.Subset.antisymm hxt htx
    subst hx
    exact ⟨ht, fun y hy hyx => hmin y (hTS hy) hyx⟩
  · rintro ⟨hxT, hmin⟩
    refine ⟨hTS hxT, fun y hy hyx => ?_⟩
    obtain ⟨t, ht, hty⟩ := hcov y hy
    exact (hmin t ht (hty.trans hyx)).trans hty

theorem part1 (n : ℕ) (A B : Finset (Finset (Fin n))) :
    mins (A ∪ B) = mins (mins A ∪ mins B) := by
  apply mins_eq _ _ (Finset.union_subset_union (mins_sub A) (mins_sub B))
  intro s hs
  rcases Finset.mem_union.mp hs with h | h
  · obtain ⟨m, hm, hms⟩ := cover A s h
    exact ⟨m, Finset.mem_union_left _ hm, hms⟩
  · obtain ⟨m, hm, hms⟩ := cover B s h
    exact ⟨m, Finset.mem_union_right _ hm, hms⟩

theorem part2 (n : ℕ) (A B : Finset (Finset (Fin n))) :
    mins (A.biUnion fun (u : Finset (Fin n)) => Finset.image (fun (v : Finset (Fin n)) => u ∪ v) B) =
      mins ((mins A).biUnion fun (u : Finset (Fin n)) =>
        Finset.image (fun (v : Finset (Fin n)) => u ∪ v) (mins B)) := by
  apply mins_eq
  · intro t ht
    simp only [Finset.mem_biUnion, Finset.mem_image] at ht ⊢
    obtain ⟨u, hu, v, hv, rfl⟩ := ht
    exact ⟨u, mins_sub A hu, v, mins_sub B hv, rfl⟩
  · intro s hs
    simp only [Finset.mem_biUnion, Finset.mem_image] at hs
    obtain ⟨u, hu, v, hv, rfl⟩ := hs
    obtain ⟨m, hm, hmu⟩ := cover A u hu
    obtain ⟨m', hm', hmv⟩ := cover B v hv
    refine ⟨m ∪ m', ?_, Finset.union_subset_union hmu hmv⟩
    simp only [Finset.mem_biUnion, Finset.mem_image]
    exact ⟨m, hm, m', hm', rfl⟩

end PEqualNP.Outside.L_meta_6949

theorem PEqualNP.Outside.L_meta_6949 : ∀ (x1 : ℕ) (x2 x3 : Finset (Finset (Fin x1))),   have x4 : Finset (Finset (Fin x1)) → Finset (Finset (Fin x1)) := fun (x4 : Finset (Finset (Fin x1))) => {x5 ∈ x4 | ∀ x6 ∈ x4, x6 ⊆ x5 → x5 ⊆ x6};   x4 (x2 ∪ x3) = x4 (x4 x2 ∪ x4 x3) ∧ x4 (x2.biUnion fun (x5 : Finset (Fin x1)) => Finset.image (fun (x6 : Finset (Fin x1)) => x5 ∪ x6) x3) = x4 ((x4 x2).biUnion fun (x5 : Finset (Fin x1)) => Finset.image (fun (x6 : Finset (Fin x1)) => x5 ∪ x6) (x4 x3)) := by
  intro n A B x4
  exact ⟨PEqualNP.Outside.L_meta_6949.part1 n A B, PEqualNP.Outside.L_meta_6949.part2 n A B⟩
