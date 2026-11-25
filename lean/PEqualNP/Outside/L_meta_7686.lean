import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7686

-- One side of a C4-free bipartite graph with all degrees above k has more than k (k + 1) vertices.
theorem side {α β : Type} [DecidableEq α] [DecidableEq β] (R : α → β → Prop) [DecidableRel R]
    (A : Finset α) (B : Finset β) (k : ℕ)
    (hC4 : ∀ a a' b b', R a b → R a b' → R a' b → R a' b' → a = a' ∨ b = b')
    (hA : A.Nonempty) (hdA : ∀ a ∈ A, k < (B.filter (fun b => R a b)).card)
    (hdB : ∀ b ∈ B, k < (A.filter (fun a => R a b)).card) :
    k * (k + 1) < A.card := by
  obtain ⟨u, hu⟩ := hA
  set N := B.filter (fun b => R u b) with hN
  let M : β → Finset α := fun b => (A.filter (fun a => R a b)).erase u
  have hsub : insert u (N.biUnion M) ⊆ A := by
    intro a ha
    rw [Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · exact hu
    · rw [Finset.mem_biUnion] at ha
      obtain ⟨b, -, hb⟩ := ha
      exact (Finset.mem_filter.1 (Finset.mem_of_mem_erase hb)).1
  have hnot : u ∉ N.biUnion M := by
    intro h
    rw [Finset.mem_biUnion] at h
    obtain ⟨b, -, hb⟩ := h
    exact (Finset.notMem_erase u _) hb
  have hdisj : (N : Set β).PairwiseDisjoint M := by
    intro b hb b' hb' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro a ha ha'
    have hb1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
    have hb2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hb')).2
    have hau := Finset.ne_of_mem_erase ha
    have ha1 := (Finset.mem_filter.1 (Finset.mem_of_mem_erase ha)).2
    have ha2 := (Finset.mem_filter.1 (Finset.mem_of_mem_erase ha')).2
    rcases hC4 u a b b' hb1 hb2 ha1 ha2 with h | h
    · exact hau h.symm
    · exact hne h
  have hcardM : ∀ b ∈ N, k ≤ (M b).card := by
    intro b hb
    have hbB := (Finset.mem_filter.1 hb).1
    have hub : u ∈ A.filter (fun a => R a b) := Finset.mem_filter.2 ⟨hu, (Finset.mem_filter.1 hb).2⟩
    have := hdB b hbB
    show k ≤ ((A.filter (fun a => R a b)).erase u).card
    rw [Finset.card_erase_of_mem hub]
    omega
  have hsum : N.card * k ≤ (N.biUnion M).card := by
    rw [Finset.card_biUnion hdisj]
    have := Finset.card_nsmul_le_sum N (fun b => (M b).card) k hcardM
    simpa [smul_eq_mul] using this
  have hN1 : k < N.card := hdA u hu
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at h1
  have h2 : (k + 1) * k ≤ N.card * k := Nat.mul_le_mul_right k hN1
  nlinarith

theorem edges {n : ℕ} (S : Finset (Fin n × Fin n)) (A B : Finset (Fin n)) :
    (S.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B)).card =
      ∑ a ∈ A, (B.filter (fun b => (a, b) ∈ S)).card := by
  have : S.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B) = (A ×ˢ B).filter (fun e => e ∈ S) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [this, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [Finset.card_filter]

end PEqualNP.Outside.L_meta_7686

theorem PEqualNP.Outside.L_meta_7686 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x1)) (x4 x5 : Finset (Fin x1)), (∀ (x6 x7 x8 x9 : Fin x1), (x6, x8) ∈ x3 → (x6, x9) ∈ x3 → (x7, x8) ∈ x3 → (x7, x9) ∈ x3 → x6 = x7 ∨ x8 = x9) → x4.Nonempty → x5.Nonempty → (∀ x9 ∈ x4, x2 < {x11 ∈ x5 | (x9, x11) ∈ x3}.card) → (∀ x10 ∈ x5, x2 < {x12 ∈ x4 | (x12, x10) ∈ x3}.card) → x2 * (x2 + (1 : ℕ)) < x4.card ∧ x2 * (x2 + (1 : ℕ)) < x5.card ∧ (x2 + (1 : ℕ)) * (x2 * (x2 + (1 : ℕ)) + (1 : ℕ)) ≤ {x11 ∈ x3 | x11.1 ∈ x4 ∧ x11.2 ∈ x5}.card := by
  intro n k S A B hC4 hA hB hdA hdB
  have h4 : k * (k + 1) < A.card :=
    PEqualNP.Outside.L_meta_7686.side (fun a b => (a, b) ∈ S) A B k
      (fun a a' b b' h1 h2 h3 h4 => hC4 a a' b b' h1 h2 h3 h4) hA hdA hdB
  have h5 : k * (k + 1) < B.card :=
    PEqualNP.Outside.L_meta_7686.side (fun b a => (a, b) ∈ S) B A k
      (fun b b' a a' h1 h2 h3 h4 => (hC4 a a' b b' h1 h3 h2 h4).symm) hB hdB hdA
  refine ⟨h4, h5, ?_⟩
  rw [PEqualNP.Outside.L_meta_7686.edges]
  have hs : A.card • (k + 1) ≤ ∑ a ∈ A, (B.filter (fun b => (a, b) ∈ S)).card :=
    Finset.card_nsmul_le_sum A _ (k + 1) (fun a ha => hdA a ha)
  rw [smul_eq_mul] at hs
  have : (k + 1) * (k * (k + 1) + 1) ≤ (k + 1) * A.card := Nat.mul_le_mul_left _ h4
  nlinarith
