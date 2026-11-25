import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10042

-- The matrix is circulant: entry (i, j) is 0 exactly when (j - i) mod 13 lies in
-- {0, 2, 5, 6, 7, 8, 11}. Mark the 39 zero entries with (j - i) mod 13 in {2, 6, 8}.
-- Every all-0 rectangle contains at most 3 marked entries, and 11 * 3 < 39.

def rows : List ℕ := [5658, 3125, 6250, 4309, 427, 854, 1708, 3416, 6832, 5473, 2755, 5510, 2829]

def M (i j : Fin 13) : Bool := (rows.getD i.val 0).testBit j.val

def sc (i j : Fin 13) : Bool :=
  decide ((j.val + 13 - i.val) % 13 = 2 ∨ (j.val + 13 - i.val) % 13 = 6 ∨
    (j.val + 13 - i.val) % 13 = 8)

theorem scZero : ∀ i j : Fin 13, sc i j = true → M i j = false := by
  decide +kernel

theorem Scard : ((Finset.univ : Finset (Fin 13 × Fin 13)).filter
    (fun p => sc p.1 p.2 = true)).card = 39 := by
  decide +kernel

def Sl : List (Fin 13 × Fin 13) := [(0, 2), (0, 6), (0, 8), (1, 3), (1, 7), (1, 9), (2, 4),
  (2, 8), (2, 10), (3, 5), (3, 9), (3, 11), (4, 6), (4, 10), (4, 12), (5, 0), (5, 7), (5, 11),
  (6, 1), (6, 8), (6, 12), (7, 0), (7, 2), (7, 9), (8, 1), (8, 3), (8, 10), (9, 2), (9, 4),
  (9, 11), (10, 3), (10, 5), (10, 12), (11, 0), (11, 4), (11, 6), (12, 1), (12, 5), (12, 7)]

theorem memS : ∀ i j : Fin 13, sc i j = true → (i, j) ∈ Sl := by
  decide +kernel

def ok : Bool := Sl.all fun p => Sl.all fun q => (q == p) || M p.1 q.2 || M q.1 p.2 ||
  Sl.all fun r => (r == p) || (r == q) || M p.1 r.2 || M r.1 p.2 || M q.1 r.2 || M r.1 q.2 ||
  Sl.all fun s => (s == p) || (s == q) || (s == r) || M p.1 s.2 || M s.1 p.2 || M q.1 s.2 ||
    M s.1 q.2 || M r.1 s.2 || M s.1 r.2

set_option maxRecDepth 100000 in
theorem okT : ok = true := by
  decide +kernel

theorem clique (p q r s : Fin 13 × Fin 13) (hp : p ∈ Sl) (hq : q ∈ Sl) (hr : r ∈ Sl)
    (hs : s ∈ Sl) (hqp : q ≠ p) (hrp : r ≠ p) (hrq : r ≠ q) (hsp : s ≠ p) (hsq : s ≠ q)
    (hsr : s ≠ r) (c1 : M p.1 q.2 = false) (c2 : M q.1 p.2 = false) (c3 : M p.1 r.2 = false)
    (c4 : M r.1 p.2 = false) (c5 : M q.1 r.2 = false) (c6 : M r.1 q.2 = false)
    (c7 : M p.1 s.2 = false) (c8 : M s.1 p.2 = false) (c9 : M q.1 s.2 = false)
    (c10 : M s.1 q.2 = false) (c11 : M r.1 s.2 = false) (c12 : M s.1 r.2 = false) : False := by
  have h := okT
  rw [ok, List.all_eq_true] at h
  have h := h p hp
  rw [List.all_eq_true] at h
  have h := h q hq
  simp only [Bool.or_eq_true, beq_iff_eq, hqp, c1, c2, Bool.false_eq_true, false_or,
    List.all_eq_true] at h
  have h := h r hr
  simp only [Bool.or_eq_true, beq_iff_eq, hrp, hrq, c3, c4, c5, c6, Bool.false_eq_true, false_or,
    List.all_eq_true] at h
  have h := h s hs
  simp only [Bool.or_eq_true, beq_iff_eq, hsp, hsq, hsr, c7, c8, c9, c10, c11, c12,
    Bool.false_eq_true, false_or, or_false] at h

theorem rect (A B : Finset (Fin 13)) (h : ∀ i ∈ A, ∀ j ∈ B, M i j = false) :
    ((A ×ˢ B).filter (fun p : Fin 13 × Fin 13 => sc p.1 p.2 = true)).card ≤ 3 := by
  by_contra hc
  push_neg at hc
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card_iff.mp (Nat.lt_of_succ_lt hc)
  have mem : ∀ s ∈ (A ×ˢ B).filter (fun p : Fin 13 × Fin 13 => sc p.1 p.2 = true),
      s.1 ∈ A ∧ s.2 ∈ B ∧ sc s.1 s.2 = true := by
    intro s hs
    rw [Finset.mem_filter, Finset.mem_product] at hs
    exact ⟨hs.1.1, hs.1.2, hs.2⟩
  have sub : (A ×ˢ B).filter (fun p : Fin 13 × Fin 13 => sc p.1 p.2 = true) ⊆ {p, q, r} := by
    intro s hs
    obtain ⟨p1, p2, p3⟩ := mem p hp
    obtain ⟨q1, q2, q3⟩ := mem q hq
    obtain ⟨r1, r2, r3⟩ := mem r hr
    obtain ⟨s1, s2, s3⟩ := mem s hs
    by_contra hn0
    have hn : s ≠ p ∧ s ≠ q ∧ s ≠ r := by
      refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> exact hn0 (by simp)
    exact clique p q r s (memS _ _ p3) (memS _ _ q3) (memS _ _ r3) (memS _ _ s3) hpq.symm hpr.symm
      hqr.symm hn.1 hn.2.1 hn.2.2 (h _ p1 _ q2) (h _ q1 _ p2) (h _ p1 _ r2) (h _ r1 _ p2)
      (h _ q1 _ r2) (h _ r1 _ q2) (h _ p1 _ s2) (h _ s1 _ p2) (h _ q1 _ s2) (h _ s1 _ q2)
      (h _ r1 _ s2) (h _ s1 _ r2)
  have := (Finset.card_le_card sub).trans Finset.card_le_three
  omega

theorem main (L : List (Finset (Fin 13) × Finset (Fin 13))) (hlen : L.length ≤ 11)
    (hz : ∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, M i j = false)
    (hc : ∀ (i : Fin 13) (j : Fin 13), M i j = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) : False := by
  have sub : (Finset.univ : Finset (Fin 13 × Fin 13)).filter (fun p => sc p.1 p.2 = true) ⊆
      L.toFinset.biUnion (fun r => (r.1 ×ˢ r.2).filter
        (fun p : Fin 13 × Fin 13 => sc p.1 p.2 = true)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨r, hr, h1, h2⟩ := hc p.1 p.2 (scZero p.1 p.2 hp.2)
    rw [Finset.mem_biUnion]
    exact ⟨r, List.mem_toFinset.mpr hr,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h2⟩, hp.2⟩⟩
  have c1 := Finset.card_le_card sub
  rw [Scard] at c1
  have c2 := Finset.card_biUnion_le (s := L.toFinset) (t := fun r => (r.1 ×ˢ r.2).filter
        (fun p : Fin 13 × Fin 13 => sc p.1 p.2 = true))
  have c3 : ∑ r ∈ L.toFinset, ((r.1 ×ˢ r.2).filter
        (fun p : Fin 13 × Fin 13 => sc p.1 p.2 = true)).card ≤ ∑ _r ∈ L.toFinset, 3 :=
    Finset.sum_le_sum (fun r hr => rect r.1 r.2 (hz r (List.mem_toFinset.mp hr)))
  rw [Finset.sum_const, smul_eq_mul] at c3
  have c4 := List.toFinset_card_le L
  omega

end PEqualNP.Outside.L_meta_10042

theorem PEqualNP.Outside.L_meta_10042 : ¬ (∃ L : List (Finset (Fin 13) × Finset (Fin 13)), L.length ≤ 11 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([5658, 3125, 6250, 4309, 427, 854, 1708, 3416, 6832, 5473, 2755, 5510, 2829] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 13) (j : Fin 13), (([5658, 3125, 6250, 4309, 427, 854, 1708, 3416, 6832, 5473, 2755, 5510, 2829] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L, hlen, hz, hc⟩
  exact PEqualNP.Outside.L_meta_10042.main L hlen hz hc
