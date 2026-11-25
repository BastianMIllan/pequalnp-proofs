import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6172

-- One OR gate per rectangle: a line gate over the points when the line side is a single line,
-- otherwise a point gate over the lines.
noncomputable def ent {x2 : ℕ} (x1 : ℕ) (r : Finset (Fin x1) × Finset (Fin x2)) :
    List (ℕ × List ℕ) :=
  if r.2.card = 1 then r.2.toList.map (fun b => (x1 + b.val, r.1.toList.map (fun a => a.val)))
  else r.1.toList.map (fun a => (a.val, r.2.toList.map (fun b => x1 + b.val)))

theorem ent_shape {x1 x2 : ℕ} (r : Finset (Fin x1) × Finset (Fin x2)) (hA : r.1.Nonempty)
    (hB : r.2.Nonempty) :
    ∀ e ∈ ent x1 r, e.2 ≠ [] ∧ ((e.1 < x1 ∧ ∀ y ∈ e.2, x1 ≤ y ∧ y < x1 + x2) ∨
      x1 ≤ e.1 ∧ e.1 < x1 + x2 ∧ ∀ y ∈ e.2, y < x1) := by
  intro e he
  unfold ent at he
  split_ifs at he with h
  · obtain ⟨b, _, rfl⟩ := List.mem_map.1 he
    refine ⟨?_, Or.inr ⟨Nat.le_add_right _ _, Nat.add_lt_add_left b.isLt x1, ?_⟩⟩
    · simp [Finset.toList_eq_nil, hA.ne_empty]
    · intro y hy
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hy
      exact a.isLt
  · obtain ⟨a, _, rfl⟩ := List.mem_map.1 he
    refine ⟨?_, Or.inl ⟨a.isLt, ?_⟩⟩
    · simp [Finset.toList_eq_nil, hB.ne_empty]
    · intro y hy
      obtain ⟨b, _, rfl⟩ := List.mem_map.1 hy
      exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left b.isLt x1⟩

theorem mem_ent {x1 x2 : ℕ} (r : Finset (Fin x1) × Finset (Fin x2)) (i : Fin x1) (j : Fin x2) :
    (∃ e ∈ ent x1 r, e.1 = i.val ∧ x1 + j.val ∈ e.2 ∨ e.1 = x1 + j.val ∧ i.val ∈ e.2) ↔
      (i ∈ r.1 ∧ j ∈ r.2) := by
  unfold ent
  split_ifs with h
  · constructor
    · rintro ⟨e, he, hh⟩
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 he
      rcases hh with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exfalso
        have h1' : x1 + b.val = i.val := h1
        have := i.isLt
        omega
      · obtain ⟨a, ha, h3⟩ := List.mem_map.1 h2
        have h1' : x1 + b.val = x1 + j.val := h1
        have hbj : b = j := Fin.ext (by omega)
        have hai : a = i := Fin.ext h3
        subst hbj
        subst hai
        exact ⟨Finset.mem_toList.1 ha, Finset.mem_toList.1 hb⟩
    · rintro ⟨hi, hj⟩
      exact ⟨_, List.mem_map.2 ⟨j, Finset.mem_toList.2 hj, rfl⟩,
        Or.inr ⟨rfl, List.mem_map.2 ⟨i, Finset.mem_toList.2 hi, rfl⟩⟩⟩
  · constructor
    · rintro ⟨e, he, hh⟩
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
      rcases hh with ⟨h1, h2⟩ | ⟨h1, _⟩
      · obtain ⟨b, hb, h3⟩ := List.mem_map.1 h2
        have h3' : x1 + b.val = x1 + j.val := h3
        have hbj : b = j := Fin.ext (by omega)
        have hai : a = i := Fin.ext h1
        subst hbj
        subst hai
        exact ⟨Finset.mem_toList.1 ha, Finset.mem_toList.1 hb⟩
      · exfalso
        have h1' : a.val = x1 + j.val := h1
        have := a.isLt
        omega
    · rintro ⟨hi, hj⟩
      exact ⟨_, List.mem_map.2 ⟨i, Finset.mem_toList.2 hi, rfl⟩,
        Or.inl ⟨rfl, List.mem_map.2 ⟨j, Finset.mem_toList.2 hj, rfl⟩⟩⟩

theorem ent_cost {x1 x2 : ℕ} (x3 : Fin x1 → Fin x2 → Prop)
    (hc : ∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 →
      ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9))
    (r : Finset (Fin x1) × Finset (Fin x2)) (hA : r.1.Nonempty) (hB : r.2.Nonempty)
    (hR : ∀ a ∈ r.1, ∀ b ∈ r.2, x3 a b) :
    ((ent x1 r).map (fun e => e.2.length)).sum + (ent x1 r).length ≤ r.1.card + r.2.card := by
  obtain ⟨A, B⟩ := r
  simp only at hA hB hR ⊢
  unfold ent
  simp only
  split_ifs with h
  · obtain ⟨b, rfl⟩ := Finset.card_eq_one.1 h
    simp
  · have hA1 : A.card = 1 := by
      by_contra hne
      have h1 : 1 < A.card := by have := hA.card_pos; omega
      have h2 : 1 < B.card := by have := hB.card_pos; omega
      obtain ⟨a, ha, a', ha', haa⟩ := Finset.one_lt_card.1 h1
      obtain ⟨b, hb, b', hb', hbb⟩ := Finset.one_lt_card.1 h2
      exact hc a a' b b' haa hbb ⟨hR a ha b hb, hR a ha b' hb', hR a' ha' b hb, hR a' ha' b' hb'⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hA1
    simp

theorem cost_total {x1 x2 : ℕ} (x3 : Fin x1 → Fin x2 → Prop)
    (hc : ∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 →
      ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9))
    (L : List (Finset (Fin x1) × Finset (Fin x2)))
    (h : ∀ r ∈ L, r.1.Nonempty ∧ r.2.Nonempty ∧ ∀ a ∈ r.1, ∀ b ∈ r.2, x3 a b) :
    ((L.flatMap (ent x1)).map (fun e => e.2.length)).sum + (L.flatMap (ent x1)).length ≤
      (L.map (fun r => r.1.card + r.2.card)).sum := by
  induction L with
  | nil => simp
  | cons r L ih =>
    have hr := h r List.mem_cons_self
    have h1 := ent_cost x3 hc r hr.1 hr.2.1 hr.2.2
    have h2 := ih (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.length_append,
      List.map_cons, List.sum_cons]
    omega

end PEqualNP.Outside.L_meta_6172

theorem PEqualNP.Outside.L_meta_6172 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : List (Finset (Fin x1) × Finset (Fin x2))), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → (∀ x7 ∈ x5, x7.1.Nonempty ∧ x7.2.Nonempty ∧ ∀ x9 ∈ x7.1, ∀ x11 ∈ x7.2, x3 x9 x11) → (∀ (x8 : Fin x1) (x9 : Fin x2), x3 x8 x9 ↔ ∃ x10 ∈ x5, x8 ∈ x10.1 ∧ x9 ∈ x10.2) → ∃ (x9 : List (ℕ × List ℕ)), (∀ x10 ∈ x9, x10.2 ≠ [] ∧ ((x10.1 < x1 ∧ ∀ x12 ∈ x10.2, x1 ≤ x12 ∧ x12 < x1 + x2) ∨ x1 ≤ x10.1 ∧ x10.1 < x1 + x2 ∧ ∀ x12 ∈ x10.2, x12 < x1)) ∧ (∀ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 ↔ ∃ x12 ∈ x9, x12.1 = ↑x10 ∧ x1 + ↑x11 ∈ x12.2 ∨ x12.1 = x1 + ↑x11 ∧ ↑x10 ∈ x12.2) ∧ (List.map (fun (x10 : ℕ × List ℕ) => x10.2.length) x9).sum + x9.length - (1 : ℕ) ≤ (List.map (fun (x10 : Finset (Fin x1) × Finset (Fin x2)) => x10.1.card + x10.2.card) x5).sum - (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 hc hrect hcov
  refine ⟨x5.flatMap (PEqualNP.Outside.L_meta_6172.ent x1), ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨r, hr, he⟩ := List.mem_flatMap.1 he
    exact PEqualNP.Outside.L_meta_6172.ent_shape r (hrect r hr).1 (hrect r hr).2.1 e he
  · intro i j
    rw [hcov]
    constructor
    · rintro ⟨r, hr, hi, hj⟩
      obtain ⟨e, he, hh⟩ := (PEqualNP.Outside.L_meta_6172.mem_ent r i j).2 ⟨hi, hj⟩
      exact ⟨e, List.mem_flatMap.2 ⟨r, hr, he⟩, hh⟩
    · rintro ⟨e, he, hh⟩
      obtain ⟨r, hr, he⟩ := List.mem_flatMap.1 he
      exact ⟨r, hr, (PEqualNP.Outside.L_meta_6172.mem_ent r i j).1 ⟨e, he, hh⟩⟩
  · have := PEqualNP.Outside.L_meta_6172.cost_total x3 hc x5 hrect
    omega
