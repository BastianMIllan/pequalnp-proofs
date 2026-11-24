import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2408

open Classical in
theorem atMostOne {N M : ℕ} (I : Fin N → Fin M → Prop) (Wl : Finset (Fin M))
    (hI : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 →
      ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5))
    (p q : Fin N) (hpq : p ≠ q) :
    (Wl.filter (fun l => I p l ∧ I q l)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter] at hx hy
  by_contra hxy
  exact hI p q x y hpq hxy ⟨hx.2.1, hx.2.2, hy.2.1, hy.2.2⟩

open Classical in
theorem caseA {N M : ℕ} (I : Fin N → Fin M → Prop) (Wl : Finset (Fin M))
    (mk : Fin M → Finset (Fin N)) (z : Fin N → Fin N)
    (hI : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 →
      ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5))
    (hW : ∀ w ∈ Wl, 3 ≤ (mk w).card ∧ ∀ a ∈ mk w, I a w ∧ ¬ I (z a) w ∧ z a ≠ a)
    (hC : ∀ w ∈ Wl, ∀ a ∈ mk w, ∀ w' ∈ Wl, I a w' ∨ I (z a) w')
    (w : Fin M) (hw : w ∈ Wl) (a b : Fin N) (ha : a ∈ mk w) (hb : b ∈ mk w)
    (hab : z a ≠ z b) : Wl.card ≤ 4 := by
  obtain ⟨_, hm⟩ := hW w hw
  obtain ⟨Iaw, nzaw, _⟩ := hm a ha
  obtain ⟨Ibw, nzbw, _⟩ := hm b hb
  have ne1 : a ≠ z b := fun e => nzbw (e ▸ Iaw)
  have ne2 : b ≠ z a := fun e => nzaw (e ▸ Ibw)
  have hab' : a ≠ b := fun e => hab (by rw [e])
  set F1 := Wl.filter (fun l => I a l ∧ I (z b) l) with hF1
  set F2 := Wl.filter (fun l => I b l ∧ I (z a) l) with hF2
  set F3 := Wl.filter (fun l => I (z a) l ∧ I (z b) l) with hF3
  have hsub : Wl ⊆ {w} ∪ F1 ∪ F2 ∪ F3 := by
    intro w' hw'
    simp only [Finset.mem_union, Finset.mem_singleton, hF1, hF2, hF3, Finset.mem_filter]
    by_cases hww : w' = w
    · left; left; left; exact hww
    rcases hC w hw a ha w' hw' with h1 | h1 <;> rcases hC w hw b hb w' hw' with h2 | h2
    · exact absurd ⟨Iaw, Ibw, h1, h2⟩ (hI a b w w' hab' (Ne.symm hww))
    · left; left; right; exact ⟨hw', h1, h2⟩
    · left; right; exact ⟨hw', h2, h1⟩
    · right; exact ⟨hw', h1, h2⟩
  have c1 : F1.card ≤ 1 := atMostOne I Wl hI a (z b) ne1
  have c2 : F2.card ≤ 1 := atMostOne I Wl hI b (z a) ne2
  have c3 : F3.card ≤ 1 := atMostOne I Wl hI (z a) (z b) hab
  have e0 := Finset.card_le_card hsub
  have e1 := Finset.card_union_le ({w} ∪ F1 ∪ F2) F3
  have e2 := Finset.card_union_le ({w} ∪ F1) F2
  have e3 := Finset.card_union_le {w} F1
  have e4 : ({w} : Finset (Fin M)).card = 1 := Finset.card_singleton w
  omega

end PEqualNP.Outside.L_meta_2408

theorem PEqualNP.Outside.L_meta_2408 : ∀ (N M : ℕ) (I : Fin N → Fin M → Prop) (Wl : Finset (Fin M)) (mk : Fin M → Finset (Fin N)) (z : Fin N → Fin N), (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ w ∈ Wl, 3 ≤ (mk w).card ∧ ∀ a ∈ mk w, I a w ∧ ¬ I (z a) w ∧ z a ≠ a) → (∀ w ∈ Wl, ∀ a ∈ mk w, ∀ w' ∈ Wl, I a w' ∨ I (z a) w') → Wl.card ≤ 4 := by
  classical
  intro N M I Wl mk z hI hW hC
  by_cases hA : ∃ w ∈ Wl, ∃ a ∈ mk w, ∃ b ∈ mk w, z a ≠ z b
  · obtain ⟨w, hw, a, ha, b, hb, hab⟩ := hA
    exact PEqualNP.Outside.L_meta_2408.caseA I Wl mk z hI hW hC w hw a b ha hb hab
  push_neg at hA
  by_contra hc
  push_neg at hc
  have key : ∀ w ∈ Wl, ∃ P, ¬ I P w ∧ ∀ w' ∈ Wl, w' ≠ w → I P w' := by
    intro w hw
    obtain ⟨hcard, hm⟩ := hW w hw
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (mk w).card)
    refine ⟨z a, (hm a ha).2.1, ?_⟩
    intro w' hw' hne
    have hzb : z b = z a := hA w hw b hb a ha
    rcases hC w hw a ha w' hw' with h1 | h1
    · rcases hC w hw b hb w' hw' with h2 | h2
      · exact absurd ⟨(hm a ha).1, (hm b hb).1, h1, h2⟩ (hI a b w w' hab (Ne.symm hne))
      · rw [hzb] at h2
        exact h2
    · exact h1
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < Wl.card)
  obtain ⟨P, hPw, hP⟩ := key w hw
  have hc1 : 0 < (Wl.erase w).card := by
    rw [Finset.card_erase_of_mem hw]
    omega
  obtain ⟨w1, hw1⟩ := Finset.card_pos.mp hc1
  have hw1W : w1 ∈ Wl := Finset.mem_of_mem_erase hw1
  have hw1ne : w1 ≠ w := Finset.ne_of_mem_erase hw1
  obtain ⟨P1, hP1w1, hP1⟩ := key w1 hw1W
  have hPP1 : P ≠ P1 := by
    intro e
    apply hP1w1
    rw [← e]
    exact hP w1 hw1W hw1ne
  have hT : ((Wl.erase w).erase w1) ⊆ Wl.filter (fun l => I P l ∧ I P1 l) := by
    intro x hx
    have hx1 := Finset.ne_of_mem_erase hx
    have hx2 := Finset.mem_of_mem_erase hx
    have hx3 := Finset.ne_of_mem_erase hx2
    have hx4 := Finset.mem_of_mem_erase hx2
    rw [Finset.mem_filter]
    exact ⟨hx4, hP x hx4 hx3, hP1 x hx4 hx1⟩
  have h1 := Finset.card_le_card hT
  have h2 := PEqualNP.Outside.L_meta_2408.atMostOne I Wl hI P P1 hPP1
  rw [Finset.card_erase_of_mem hw1, Finset.card_erase_of_mem hw] at h1
  omega
