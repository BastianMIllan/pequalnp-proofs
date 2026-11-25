import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6967

open PEqualNP.CircuitLowerBounds

def rd (L : List Gate) (R : Gate → List ℕ) (v : ℕ) : ℕ :=
  L.countP (fun g => (R g).contains v)

def both (L : List Gate) (R : Gate → List ℕ) (v w : ℕ) : ℕ :=
  L.countP (fun g => (R g).contains v && (R g).contains w)

def anyc (L : List Gate) (R : Gate → List ℕ) (v w : ℕ) : ℕ :=
  L.countP (fun g => (R g).any fun x => x == v || x == w)

theorem any_eq (l : List ℕ) (u w : ℕ) :
    (l.any fun x => x == u || x == w) = (l.contains u || l.contains w) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, Bool.or_eq_true, List.contains_iff_mem,
    List.contains_iff_mem]
  constructor
  · rintro ⟨x, hx, hxe⟩
    rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hxe
    rcases hxe with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (h | h)
    · exact ⟨u, h, by simp⟩
    · exact ⟨w, h, by simp⟩

theorem ie (L : List Gate) (p q : Gate → Bool) :
    L.countP (fun g => p g || q g) + L.countP (fun g => p g && q g) = L.countP p + L.countP q := by
  induction L with
  | nil => simp
  | cons g L ih =>
    simp only [List.countP_cons]
    cases p g <;> cases q g <;> simp <;> omega

theorem ie2 (L : List Gate) (R : Gate → List ℕ) (v w : ℕ) :
    anyc L R v w + both L R v w = rd L R v + rd L R w := by
  unfold anyc both rd
  rw [show (fun g => (R g).any fun x => x == v || x == w) =
      (fun g => (R g).contains v || (R g).contains w) from funext fun g => any_eq _ _ _]
  exact ie L _ _

theorem gate_le {n : ℕ} (l : List ℕ) (hl : l.length ≤ 2) (v : Fin n) (T : Finset (Fin n))
    (hv : v ∉ T) :
    (∑ w ∈ T, if (l.contains (v : ℕ) && l.contains (w : ℕ)) = true then 1 else 0) ≤
      if l.contains (v : ℕ) = true then 1 else 0 := by
  by_cases hcv : l.contains (v : ℕ) = true
  · rw [if_pos hcv]
    simp only [hcv, Bool.true_and]
    rw [Finset.sum_boole, Nat.cast_id]
    have hvm : (v : ℕ) ∈ l := List.contains_iff_mem.mp hcv
    have h1 : (T.filter fun w : Fin n => l.contains (w : ℕ) = true).card ≤
        (l.toFinset.erase (v : ℕ)).card := by
      apply Finset.card_le_card_of_injOn (fun w : Fin n => (w : ℕ))
      · intro w hw
        have hw' : w ∈ T ∧ l.contains (w : ℕ) = true := by simpa using hw
        have hm2 : (w : ℕ) ∈ l ∧ ¬ (w : ℕ) = (v : ℕ) :=
          ⟨List.contains_iff_mem.mp hw'.2, fun h => hv (by rw [← Fin.ext h]; exact hw'.1)⟩
        simpa using hm2
      · intro a _ b _ hab
        exact Fin.ext hab
    have h2 : (l.toFinset.erase (v : ℕ)).card + 1 = l.toFinset.card :=
      Finset.card_erase_add_one (List.mem_toFinset.mpr hvm)
    have h3 : l.toFinset.card ≤ l.length := List.toFinset_card_le l
    omega
  · have hf : l.contains (v : ℕ) = false := Bool.eq_false_iff.mpr hcv
    simp only [hf, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero,
      le_refl]

theorem sumB {n : ℕ} (L : List Gate) (R : Gate → List ℕ) (hR : ∀ g, (R g).length ≤ 2)
    (v : Fin n) (T : Finset (Fin n)) (hv : v ∉ T) :
    ∑ w ∈ T, both L R v w ≤ rd L R v := by
  unfold both rd
  induction L with
  | nil => simp
  | cons g L ih =>
    simp only [List.countP_cons, Finset.sum_add_distrib]
    exact add_le_add ih (gate_le (R g) (hR g) v T hv)

theorem core {n : ℕ} (L : List Gate) (R : Gate → List ℕ) (hR : ∀ g, (R g).length ≤ 2)
    (v : Fin n) (T : Finset (Fin n)) (b : ℕ) (hv : v ∉ T)
    (hb : ∀ w ∈ T, b ≤ rd L R w) (h7 : ∀ w ∈ T, anyc L R v w ≤ 7) :
    T.card * (rd L R v + b) ≤ 7 * T.card + rd L R v := by
  have key : ∀ w ∈ T, rd L R v + b ≤ 7 + both L R v w := by
    intro w hw
    have e := ie2 L R v w
    have := hb w hw
    have := h7 w hw
    omega
  have s1 := Finset.sum_le_sum key
  rw [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at s1
  have := sumB L R hR v T hv
  nlinarith

open Classical in
theorem card_nonadj {n : ℕ} (G : SimpleGraph (Fin n))
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ 3) (S : Finset (Fin n)) (v : Fin n) :
    ∃ T : Finset (Fin n), T ⊆ S ∧ v ∉ T ∧ (∀ w ∈ T, w ≠ v ∧ ¬ G.Adj v w) ∧
      S.card ≤ T.card + 4 := by
  refine ⟨S.filter fun w => w ≠ v ∧ ¬ G.Adj v w, Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · intro h
    rw [Finset.mem_filter] at h
    exact h.2.1 rfl
  · intro w hw
    rw [Finset.mem_filter] at hw
    exact hw.2
  · have e : (S.filter fun w => w ≠ v ∧ ¬ G.Adj v w).card +
        (S.filter fun w => ¬ (w ≠ v ∧ ¬ G.Adj v w)).card = S.card :=
      Finset.card_filter_add_card_filter_not _
    have hsub : S.filter (fun w => ¬ (w ≠ v ∧ ¬ G.Adj v w)) ⊆
        insert v (S.filter fun w => G.Adj v w) := by
      intro w hw
      rw [Finset.mem_filter] at hw
      rw [Finset.mem_insert, Finset.mem_filter]
      by_cases h : w = v
      · exact Or.inl h
      · right
        refine ⟨hw.1, ?_⟩
        by_contra h'
        exact hw.2 ⟨h, h'⟩
    have hN : (S.filter fun w => G.Adj v w).card ≤ 3 := by
      have hle : ((S.filter fun w => G.Adj v w : Finset (Fin n)) : Set (Fin n)).ncard ≤
          (G.neighborSet v).ncard := by
        apply Set.ncard_le_ncard _ (Set.toFinite _)
        intro w hw
        have hw' : w ∈ S ∧ G.Adj v w := by simpa using hw
        exact (SimpleGraph.mem_neighborSet G v w).mpr hw'.2
      rw [Set.ncard_coe_finset] at hle
      exact hle.trans (hdeg v)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le v (S.filter fun w => G.Adj v w)
    omega

theorem main {n : ℕ} (G : SimpleGraph (Fin n)) (L : List Gate) (R : Gate → List ℕ)
    (hR : ∀ g, (R g).length ≤ 2) (hn : 12 ≤ n)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ 3) :
    (∀ v : Fin n, 1 ≤ L.countP (fun g => (R g).contains (v : ℕ))) →
    (∀ u w : Fin n, u ≠ w → ¬ G.Adj u w →
      L.countP (fun g => (R g).any fun x => x == (u : ℕ) || x == (w : ℕ)) ≤ 7) →
    (∀ v : Fin n, L.countP (fun g => (R g).contains (v : ℕ)) ≤ 6) ∧
      ∀ S : Finset (Fin n), (∀ v ∈ S, 4 ≤ L.countP (fun g => (R g).contains (v : ℕ))) →
        S.card ≤ 8 := by
  intro h1 h7
  have gen : ∀ (v : Fin n) (S : Finset (Fin n)) (b : ℕ), (∀ w ∈ S, b ≤ rd L R w) →
      ∃ k, S.card ≤ k + 4 ∧ k * (rd L R v + b) ≤ 7 * k + rd L R v := by
    intro v S b hb
    obtain ⟨T, hTS, hvT, hT, hcard⟩ := card_nonadj G hdeg S v
    exact ⟨T.card, hcard, core L R hR v T b hvT (fun w hw => hb w (hTS hw))
      (fun w hw => h7 v w (hT w hw).1.symm (hT w hw).2)⟩
  refine ⟨?_, ?_⟩
  · intro v
    by_contra hc
    push Not at hc
    obtain ⟨k, hk, hk2⟩ := gen v Finset.univ 1 (fun w _ => h1 w)
    rw [Finset.card_univ, Fintype.card_fin] at hk
    have ha : 7 ≤ rd L R v := hc
    have hk8 : 8 ≤ k := by omega
    nlinarith
  · intro S hS
    by_contra hc
    push Not at hc
    obtain ⟨v, hv⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨k, hk, hk2⟩ := gen v S 4 hS
    have ha : 4 ≤ rd L R v := hS v hv
    have hk5 : 5 ≤ k := by omega
    nlinarith

theorem hR_take : ∀ g : Gate,
    (List.take (bif g.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) g.inputs).length ≤ 2 := by
  intro g
  rw [List.length_take]
  cases g.op.eval [Bool.false] <;> simp

end PEqualNP.Outside.L_meta_6967

theorem PEqualNP.Outside.L_meta_6967 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   (12 : ℕ) ≤ x1 →     (∀ (x5 : Fin x1), (x2.neighborSet x5).ncard ≤ (3 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x3 →         have x7 : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs;         have x8 : Fin x1 → ℕ := fun (x8 : Fin x1) => List.countP (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => (x7 x9).contains ↑x8) x3.gates;         (∀ (x9 : Fin x1), (1 : ℕ) ≤ x8 x9) → (∀ (x10 x11 : Fin x1), x10 ≠ x11 → ¬x2.Adj x10 x11 → List.countP (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (x7 x14).any fun (x15 : ℕ) => x15 == ↑x10 || x15 == ↑x11) x3.gates ≤ (7 : ℕ)) → (∀ (x11 : Fin x1), x8 x11 ≤ (6 : ℕ)) ∧ ∀ (x11 : Finset (Fin x1)), (∀ x12 ∈ x11, (4 : ℕ) ≤ x8 x12) → x11.card ≤ (8 : ℕ) := by
  intro n G C hn hdeg _
  exact PEqualNP.Outside.L_meta_6967.main G C.gates
    (fun g => List.take (bif g.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) g.inputs)
    PEqualNP.Outside.L_meta_6967.hR_take hn hdeg
