import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1747

def circ : PEqualNP.CircuitLowerBounds.Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [44, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [45, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [46, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [47, 43] }], output := 48 }

lemma pick (Q : Finset (Fin 13)) (h : 0 < Q.card) : ∃ a ∈ Q, ∀ x ∈ Q.erase a, a < x :=
  ⟨Q.min' (Finset.card_pos.mp h), Finset.min'_mem Q _,
    fun x hx => Finset.min'_lt_of_mem_erase_min' Q _ hx⟩

lemma four (Q : Finset (Fin 13)) (h : Q.card = 4) :
    ∃ a b c d : Fin 13, a < b ∧ b < c ∧ c < d ∧ Q = {a, b, c, d} := by
  obtain ⟨a, ha, ha'⟩ := pick Q (by omega)
  have h1 : (Q.erase a).card = 3 := by
    have := Finset.card_erase_of_mem ha
    omega
  obtain ⟨b, hb, hb'⟩ := pick (Q.erase a) (by omega)
  have h2 : ((Q.erase a).erase b).card = 2 := by
    have := Finset.card_erase_of_mem hb
    omega
  obtain ⟨c, hc, hc'⟩ := pick ((Q.erase a).erase b) (by omega)
  have h3 : (((Q.erase a).erase b).erase c).card = 1 := by
    have := Finset.card_erase_of_mem hc
    omega
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp h3
  have hdm : d ∈ ((Q.erase a).erase b).erase c := by
    rw [hd]
    exact Finset.mem_singleton_self d
  refine ⟨a, b, c, d, ha' b hb, hb' c hc, hc' d hdm, ?_⟩
  rw [← Finset.insert_erase ha, ← Finset.insert_erase hb, ← Finset.insert_erase hc, hd]

def P (a b c d : Fin 13) : Prop :=
  a < b → b < c → c < d →
    (∀ k : Fin 13, (({a, b, c, d} : Finset (Fin 13)).filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
    circ.eval (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ ({a, b, c, d} : Finset (Fin 13))))
      ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ ({a, b, c, d} : Finset (Fin 13)), r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false

lemma q_0_0 : ∀ c d : Fin 13, P 0 0 c d := by
  unfold P
  decide +kernel

lemma q_0_1 : ∀ c d : Fin 13, P 0 1 c d := by
  unfold P
  decide +kernel

lemma q_0_2 : ∀ c d : Fin 13, P 0 2 c d := by
  unfold P
  decide +kernel

lemma q_0_3 : ∀ c d : Fin 13, P 0 3 c d := by
  unfold P
  decide +kernel

lemma q_0_4 : ∀ c d : Fin 13, P 0 4 c d := by
  unfold P
  decide +kernel

lemma q_0_5 : ∀ c d : Fin 13, P 0 5 c d := by
  unfold P
  decide +kernel

lemma q_0_6 : ∀ c d : Fin 13, P 0 6 c d := by
  unfold P
  decide +kernel

lemma q_0_7 : ∀ c d : Fin 13, P 0 7 c d := by
  unfold P
  decide +kernel

lemma q_0_8 : ∀ c d : Fin 13, P 0 8 c d := by
  unfold P
  decide +kernel

lemma q_0_9 : ∀ c d : Fin 13, P 0 9 c d := by
  unfold P
  decide +kernel

lemma q_0_10 : ∀ c d : Fin 13, P 0 10 c d := by
  unfold P
  decide +kernel

lemma q_0_11 : ∀ c d : Fin 13, P 0 11 c d := by
  unfold P
  decide +kernel

lemma q_0_12 : ∀ c d : Fin 13, P 0 12 c d := by
  unfold P
  decide +kernel

lemma q_0 : ∀ b c d : Fin 13, P 0 b c d := by
  intro b
  fin_cases b
  exacts [q_0_0, q_0_1, q_0_2, q_0_3, q_0_4, q_0_5, q_0_6, q_0_7, q_0_8, q_0_9, q_0_10, q_0_11, q_0_12]

lemma q_1_0 : ∀ c d : Fin 13, P 1 0 c d := by
  unfold P
  decide +kernel

lemma q_1_1 : ∀ c d : Fin 13, P 1 1 c d := by
  unfold P
  decide +kernel

lemma q_1_2 : ∀ c d : Fin 13, P 1 2 c d := by
  unfold P
  decide +kernel

lemma q_1_3 : ∀ c d : Fin 13, P 1 3 c d := by
  unfold P
  decide +kernel

lemma q_1_4 : ∀ c d : Fin 13, P 1 4 c d := by
  unfold P
  decide +kernel

lemma q_1_5 : ∀ c d : Fin 13, P 1 5 c d := by
  unfold P
  decide +kernel

lemma q_1_6 : ∀ c d : Fin 13, P 1 6 c d := by
  unfold P
  decide +kernel

lemma q_1_7 : ∀ c d : Fin 13, P 1 7 c d := by
  unfold P
  decide +kernel

lemma q_1_8 : ∀ c d : Fin 13, P 1 8 c d := by
  unfold P
  decide +kernel

lemma q_1_9 : ∀ c d : Fin 13, P 1 9 c d := by
  unfold P
  decide +kernel

lemma q_1_10 : ∀ c d : Fin 13, P 1 10 c d := by
  unfold P
  decide +kernel

lemma q_1_11 : ∀ c d : Fin 13, P 1 11 c d := by
  unfold P
  decide +kernel

lemma q_1_12 : ∀ c d : Fin 13, P 1 12 c d := by
  unfold P
  decide +kernel

lemma q_1 : ∀ b c d : Fin 13, P 1 b c d := by
  intro b
  fin_cases b
  exacts [q_1_0, q_1_1, q_1_2, q_1_3, q_1_4, q_1_5, q_1_6, q_1_7, q_1_8, q_1_9, q_1_10, q_1_11, q_1_12]

lemma q_2_0 : ∀ c d : Fin 13, P 2 0 c d := by
  unfold P
  decide +kernel

lemma q_2_1 : ∀ c d : Fin 13, P 2 1 c d := by
  unfold P
  decide +kernel

lemma q_2_2 : ∀ c d : Fin 13, P 2 2 c d := by
  unfold P
  decide +kernel

lemma q_2_3 : ∀ c d : Fin 13, P 2 3 c d := by
  unfold P
  decide +kernel

lemma q_2_4 : ∀ c d : Fin 13, P 2 4 c d := by
  unfold P
  decide +kernel

lemma q_2_5 : ∀ c d : Fin 13, P 2 5 c d := by
  unfold P
  decide +kernel

lemma q_2_6 : ∀ c d : Fin 13, P 2 6 c d := by
  unfold P
  decide +kernel

lemma q_2_7 : ∀ c d : Fin 13, P 2 7 c d := by
  unfold P
  decide +kernel

lemma q_2_8 : ∀ c d : Fin 13, P 2 8 c d := by
  unfold P
  decide +kernel

lemma q_2_9 : ∀ c d : Fin 13, P 2 9 c d := by
  unfold P
  decide +kernel

lemma q_2_10 : ∀ c d : Fin 13, P 2 10 c d := by
  unfold P
  decide +kernel

lemma q_2_11 : ∀ c d : Fin 13, P 2 11 c d := by
  unfold P
  decide +kernel

lemma q_2_12 : ∀ c d : Fin 13, P 2 12 c d := by
  unfold P
  decide +kernel

lemma q_2 : ∀ b c d : Fin 13, P 2 b c d := by
  intro b
  fin_cases b
  exacts [q_2_0, q_2_1, q_2_2, q_2_3, q_2_4, q_2_5, q_2_6, q_2_7, q_2_8, q_2_9, q_2_10, q_2_11, q_2_12]

lemma q_3_0 : ∀ c d : Fin 13, P 3 0 c d := by
  unfold P
  decide +kernel

lemma q_3_1 : ∀ c d : Fin 13, P 3 1 c d := by
  unfold P
  decide +kernel

lemma q_3_2 : ∀ c d : Fin 13, P 3 2 c d := by
  unfold P
  decide +kernel

lemma q_3_3 : ∀ c d : Fin 13, P 3 3 c d := by
  unfold P
  decide +kernel

lemma q_3_4 : ∀ c d : Fin 13, P 3 4 c d := by
  unfold P
  decide +kernel

lemma q_3_5 : ∀ c d : Fin 13, P 3 5 c d := by
  unfold P
  decide +kernel

lemma q_3_6 : ∀ c d : Fin 13, P 3 6 c d := by
  unfold P
  decide +kernel

lemma q_3_7 : ∀ c d : Fin 13, P 3 7 c d := by
  unfold P
  decide +kernel

lemma q_3_8 : ∀ c d : Fin 13, P 3 8 c d := by
  unfold P
  decide +kernel

lemma q_3_9 : ∀ c d : Fin 13, P 3 9 c d := by
  unfold P
  decide +kernel

lemma q_3_10 : ∀ c d : Fin 13, P 3 10 c d := by
  unfold P
  decide +kernel

lemma q_3_11 : ∀ c d : Fin 13, P 3 11 c d := by
  unfold P
  decide +kernel

lemma q_3_12 : ∀ c d : Fin 13, P 3 12 c d := by
  unfold P
  decide +kernel

lemma q_3 : ∀ b c d : Fin 13, P 3 b c d := by
  intro b
  fin_cases b
  exacts [q_3_0, q_3_1, q_3_2, q_3_3, q_3_4, q_3_5, q_3_6, q_3_7, q_3_8, q_3_9, q_3_10, q_3_11, q_3_12]

lemma q_4_0 : ∀ c d : Fin 13, P 4 0 c d := by
  unfold P
  decide +kernel

lemma q_4_1 : ∀ c d : Fin 13, P 4 1 c d := by
  unfold P
  decide +kernel

lemma q_4_2 : ∀ c d : Fin 13, P 4 2 c d := by
  unfold P
  decide +kernel

lemma q_4_3 : ∀ c d : Fin 13, P 4 3 c d := by
  unfold P
  decide +kernel

lemma q_4_4 : ∀ c d : Fin 13, P 4 4 c d := by
  unfold P
  decide +kernel

lemma q_4_5 : ∀ c d : Fin 13, P 4 5 c d := by
  unfold P
  decide +kernel

lemma q_4_6 : ∀ c d : Fin 13, P 4 6 c d := by
  unfold P
  decide +kernel

lemma q_4_7 : ∀ c d : Fin 13, P 4 7 c d := by
  unfold P
  decide +kernel

lemma q_4_8 : ∀ c d : Fin 13, P 4 8 c d := by
  unfold P
  decide +kernel

lemma q_4_9 : ∀ c d : Fin 13, P 4 9 c d := by
  unfold P
  decide +kernel

lemma q_4_10 : ∀ c d : Fin 13, P 4 10 c d := by
  unfold P
  decide +kernel

lemma q_4_11 : ∀ c d : Fin 13, P 4 11 c d := by
  unfold P
  decide +kernel

lemma q_4_12 : ∀ c d : Fin 13, P 4 12 c d := by
  unfold P
  decide +kernel

lemma q_4 : ∀ b c d : Fin 13, P 4 b c d := by
  intro b
  fin_cases b
  exacts [q_4_0, q_4_1, q_4_2, q_4_3, q_4_4, q_4_5, q_4_6, q_4_7, q_4_8, q_4_9, q_4_10, q_4_11, q_4_12]

lemma q_5_0 : ∀ c d : Fin 13, P 5 0 c d := by
  unfold P
  decide +kernel

lemma q_5_1 : ∀ c d : Fin 13, P 5 1 c d := by
  unfold P
  decide +kernel

lemma q_5_2 : ∀ c d : Fin 13, P 5 2 c d := by
  unfold P
  decide +kernel

lemma q_5_3 : ∀ c d : Fin 13, P 5 3 c d := by
  unfold P
  decide +kernel

lemma q_5_4 : ∀ c d : Fin 13, P 5 4 c d := by
  unfold P
  decide +kernel

lemma q_5_5 : ∀ c d : Fin 13, P 5 5 c d := by
  unfold P
  decide +kernel

lemma q_5_6 : ∀ c d : Fin 13, P 5 6 c d := by
  unfold P
  decide +kernel

lemma q_5_7 : ∀ c d : Fin 13, P 5 7 c d := by
  unfold P
  decide +kernel

lemma q_5_8 : ∀ c d : Fin 13, P 5 8 c d := by
  unfold P
  decide +kernel

lemma q_5_9 : ∀ c d : Fin 13, P 5 9 c d := by
  unfold P
  decide +kernel

lemma q_5_10 : ∀ c d : Fin 13, P 5 10 c d := by
  unfold P
  decide +kernel

lemma q_5_11 : ∀ c d : Fin 13, P 5 11 c d := by
  unfold P
  decide +kernel

lemma q_5_12 : ∀ c d : Fin 13, P 5 12 c d := by
  unfold P
  decide +kernel

lemma q_5 : ∀ b c d : Fin 13, P 5 b c d := by
  intro b
  fin_cases b
  exacts [q_5_0, q_5_1, q_5_2, q_5_3, q_5_4, q_5_5, q_5_6, q_5_7, q_5_8, q_5_9, q_5_10, q_5_11, q_5_12]

lemma q_6_0 : ∀ c d : Fin 13, P 6 0 c d := by
  unfold P
  decide +kernel

lemma q_6_1 : ∀ c d : Fin 13, P 6 1 c d := by
  unfold P
  decide +kernel

lemma q_6_2 : ∀ c d : Fin 13, P 6 2 c d := by
  unfold P
  decide +kernel

lemma q_6_3 : ∀ c d : Fin 13, P 6 3 c d := by
  unfold P
  decide +kernel

lemma q_6_4 : ∀ c d : Fin 13, P 6 4 c d := by
  unfold P
  decide +kernel

lemma q_6_5 : ∀ c d : Fin 13, P 6 5 c d := by
  unfold P
  decide +kernel

lemma q_6_6 : ∀ c d : Fin 13, P 6 6 c d := by
  unfold P
  decide +kernel

lemma q_6_7 : ∀ c d : Fin 13, P 6 7 c d := by
  unfold P
  decide +kernel

lemma q_6_8 : ∀ c d : Fin 13, P 6 8 c d := by
  unfold P
  decide +kernel

lemma q_6_9 : ∀ c d : Fin 13, P 6 9 c d := by
  unfold P
  decide +kernel

lemma q_6_10 : ∀ c d : Fin 13, P 6 10 c d := by
  unfold P
  decide +kernel

lemma q_6_11 : ∀ c d : Fin 13, P 6 11 c d := by
  unfold P
  decide +kernel

lemma q_6_12 : ∀ c d : Fin 13, P 6 12 c d := by
  unfold P
  decide +kernel

lemma q_6 : ∀ b c d : Fin 13, P 6 b c d := by
  intro b
  fin_cases b
  exacts [q_6_0, q_6_1, q_6_2, q_6_3, q_6_4, q_6_5, q_6_6, q_6_7, q_6_8, q_6_9, q_6_10, q_6_11, q_6_12]

lemma q_7_0 : ∀ c d : Fin 13, P 7 0 c d := by
  unfold P
  decide +kernel

lemma q_7_1 : ∀ c d : Fin 13, P 7 1 c d := by
  unfold P
  decide +kernel

lemma q_7_2 : ∀ c d : Fin 13, P 7 2 c d := by
  unfold P
  decide +kernel

lemma q_7_3 : ∀ c d : Fin 13, P 7 3 c d := by
  unfold P
  decide +kernel

lemma q_7_4 : ∀ c d : Fin 13, P 7 4 c d := by
  unfold P
  decide +kernel

lemma q_7_5 : ∀ c d : Fin 13, P 7 5 c d := by
  unfold P
  decide +kernel

lemma q_7_6 : ∀ c d : Fin 13, P 7 6 c d := by
  unfold P
  decide +kernel

lemma q_7_7 : ∀ c d : Fin 13, P 7 7 c d := by
  unfold P
  decide +kernel

lemma q_7_8 : ∀ c d : Fin 13, P 7 8 c d := by
  unfold P
  decide +kernel

lemma q_7_9 : ∀ c d : Fin 13, P 7 9 c d := by
  unfold P
  decide +kernel

lemma q_7_10 : ∀ c d : Fin 13, P 7 10 c d := by
  unfold P
  decide +kernel

lemma q_7_11 : ∀ c d : Fin 13, P 7 11 c d := by
  unfold P
  decide +kernel

lemma q_7_12 : ∀ c d : Fin 13, P 7 12 c d := by
  unfold P
  decide +kernel

lemma q_7 : ∀ b c d : Fin 13, P 7 b c d := by
  intro b
  fin_cases b
  exacts [q_7_0, q_7_1, q_7_2, q_7_3, q_7_4, q_7_5, q_7_6, q_7_7, q_7_8, q_7_9, q_7_10, q_7_11, q_7_12]

lemma q_8_0 : ∀ c d : Fin 13, P 8 0 c d := by
  unfold P
  decide +kernel

lemma q_8_1 : ∀ c d : Fin 13, P 8 1 c d := by
  unfold P
  decide +kernel

lemma q_8_2 : ∀ c d : Fin 13, P 8 2 c d := by
  unfold P
  decide +kernel

lemma q_8_3 : ∀ c d : Fin 13, P 8 3 c d := by
  unfold P
  decide +kernel

lemma q_8_4 : ∀ c d : Fin 13, P 8 4 c d := by
  unfold P
  decide +kernel

lemma q_8_5 : ∀ c d : Fin 13, P 8 5 c d := by
  unfold P
  decide +kernel

lemma q_8_6 : ∀ c d : Fin 13, P 8 6 c d := by
  unfold P
  decide +kernel

lemma q_8_7 : ∀ c d : Fin 13, P 8 7 c d := by
  unfold P
  decide +kernel

lemma q_8_8 : ∀ c d : Fin 13, P 8 8 c d := by
  unfold P
  decide +kernel

lemma q_8_9 : ∀ c d : Fin 13, P 8 9 c d := by
  unfold P
  decide +kernel

lemma q_8_10 : ∀ c d : Fin 13, P 8 10 c d := by
  unfold P
  decide +kernel

lemma q_8_11 : ∀ c d : Fin 13, P 8 11 c d := by
  unfold P
  decide +kernel

lemma q_8_12 : ∀ c d : Fin 13, P 8 12 c d := by
  unfold P
  decide +kernel

lemma q_8 : ∀ b c d : Fin 13, P 8 b c d := by
  intro b
  fin_cases b
  exacts [q_8_0, q_8_1, q_8_2, q_8_3, q_8_4, q_8_5, q_8_6, q_8_7, q_8_8, q_8_9, q_8_10, q_8_11, q_8_12]

lemma q_9_0 : ∀ c d : Fin 13, P 9 0 c d := by
  unfold P
  decide +kernel

lemma q_9_1 : ∀ c d : Fin 13, P 9 1 c d := by
  unfold P
  decide +kernel

lemma q_9_2 : ∀ c d : Fin 13, P 9 2 c d := by
  unfold P
  decide +kernel

lemma q_9_3 : ∀ c d : Fin 13, P 9 3 c d := by
  unfold P
  decide +kernel

lemma q_9_4 : ∀ c d : Fin 13, P 9 4 c d := by
  unfold P
  decide +kernel

lemma q_9_5 : ∀ c d : Fin 13, P 9 5 c d := by
  unfold P
  decide +kernel

lemma q_9_6 : ∀ c d : Fin 13, P 9 6 c d := by
  unfold P
  decide +kernel

lemma q_9_7 : ∀ c d : Fin 13, P 9 7 c d := by
  unfold P
  decide +kernel

lemma q_9_8 : ∀ c d : Fin 13, P 9 8 c d := by
  unfold P
  decide +kernel

lemma q_9_9 : ∀ c d : Fin 13, P 9 9 c d := by
  unfold P
  decide +kernel

lemma q_9_10 : ∀ c d : Fin 13, P 9 10 c d := by
  unfold P
  decide +kernel

lemma q_9_11 : ∀ c d : Fin 13, P 9 11 c d := by
  unfold P
  decide +kernel

lemma q_9_12 : ∀ c d : Fin 13, P 9 12 c d := by
  unfold P
  decide +kernel

lemma q_9 : ∀ b c d : Fin 13, P 9 b c d := by
  intro b
  fin_cases b
  exacts [q_9_0, q_9_1, q_9_2, q_9_3, q_9_4, q_9_5, q_9_6, q_9_7, q_9_8, q_9_9, q_9_10, q_9_11, q_9_12]

lemma q_10_0 : ∀ c d : Fin 13, P 10 0 c d := by
  unfold P
  decide +kernel

lemma q_10_1 : ∀ c d : Fin 13, P 10 1 c d := by
  unfold P
  decide +kernel

lemma q_10_2 : ∀ c d : Fin 13, P 10 2 c d := by
  unfold P
  decide +kernel

lemma q_10_3 : ∀ c d : Fin 13, P 10 3 c d := by
  unfold P
  decide +kernel

lemma q_10_4 : ∀ c d : Fin 13, P 10 4 c d := by
  unfold P
  decide +kernel

lemma q_10_5 : ∀ c d : Fin 13, P 10 5 c d := by
  unfold P
  decide +kernel

lemma q_10_6 : ∀ c d : Fin 13, P 10 6 c d := by
  unfold P
  decide +kernel

lemma q_10_7 : ∀ c d : Fin 13, P 10 7 c d := by
  unfold P
  decide +kernel

lemma q_10_8 : ∀ c d : Fin 13, P 10 8 c d := by
  unfold P
  decide +kernel

lemma q_10_9 : ∀ c d : Fin 13, P 10 9 c d := by
  unfold P
  decide +kernel

lemma q_10_10 : ∀ c d : Fin 13, P 10 10 c d := by
  unfold P
  decide +kernel

lemma q_10_11 : ∀ c d : Fin 13, P 10 11 c d := by
  unfold P
  decide +kernel

lemma q_10_12 : ∀ c d : Fin 13, P 10 12 c d := by
  unfold P
  decide +kernel

lemma q_10 : ∀ b c d : Fin 13, P 10 b c d := by
  intro b
  fin_cases b
  exacts [q_10_0, q_10_1, q_10_2, q_10_3, q_10_4, q_10_5, q_10_6, q_10_7, q_10_8, q_10_9, q_10_10, q_10_11, q_10_12]

lemma q_11_0 : ∀ c d : Fin 13, P 11 0 c d := by
  unfold P
  decide +kernel

lemma q_11_1 : ∀ c d : Fin 13, P 11 1 c d := by
  unfold P
  decide +kernel

lemma q_11_2 : ∀ c d : Fin 13, P 11 2 c d := by
  unfold P
  decide +kernel

lemma q_11_3 : ∀ c d : Fin 13, P 11 3 c d := by
  unfold P
  decide +kernel

lemma q_11_4 : ∀ c d : Fin 13, P 11 4 c d := by
  unfold P
  decide +kernel

lemma q_11_5 : ∀ c d : Fin 13, P 11 5 c d := by
  unfold P
  decide +kernel

lemma q_11_6 : ∀ c d : Fin 13, P 11 6 c d := by
  unfold P
  decide +kernel

lemma q_11_7 : ∀ c d : Fin 13, P 11 7 c d := by
  unfold P
  decide +kernel

lemma q_11_8 : ∀ c d : Fin 13, P 11 8 c d := by
  unfold P
  decide +kernel

lemma q_11_9 : ∀ c d : Fin 13, P 11 9 c d := by
  unfold P
  decide +kernel

lemma q_11_10 : ∀ c d : Fin 13, P 11 10 c d := by
  unfold P
  decide +kernel

lemma q_11_11 : ∀ c d : Fin 13, P 11 11 c d := by
  unfold P
  decide +kernel

lemma q_11_12 : ∀ c d : Fin 13, P 11 12 c d := by
  unfold P
  decide +kernel

lemma q_11 : ∀ b c d : Fin 13, P 11 b c d := by
  intro b
  fin_cases b
  exacts [q_11_0, q_11_1, q_11_2, q_11_3, q_11_4, q_11_5, q_11_6, q_11_7, q_11_8, q_11_9, q_11_10, q_11_11, q_11_12]

lemma q_12_0 : ∀ c d : Fin 13, P 12 0 c d := by
  unfold P
  decide +kernel

lemma q_12_1 : ∀ c d : Fin 13, P 12 1 c d := by
  unfold P
  decide +kernel

lemma q_12_2 : ∀ c d : Fin 13, P 12 2 c d := by
  unfold P
  decide +kernel

lemma q_12_3 : ∀ c d : Fin 13, P 12 3 c d := by
  unfold P
  decide +kernel

lemma q_12_4 : ∀ c d : Fin 13, P 12 4 c d := by
  unfold P
  decide +kernel

lemma q_12_5 : ∀ c d : Fin 13, P 12 5 c d := by
  unfold P
  decide +kernel

lemma q_12_6 : ∀ c d : Fin 13, P 12 6 c d := by
  unfold P
  decide +kernel

lemma q_12_7 : ∀ c d : Fin 13, P 12 7 c d := by
  unfold P
  decide +kernel

lemma q_12_8 : ∀ c d : Fin 13, P 12 8 c d := by
  unfold P
  decide +kernel

lemma q_12_9 : ∀ c d : Fin 13, P 12 9 c d := by
  unfold P
  decide +kernel

lemma q_12_10 : ∀ c d : Fin 13, P 12 10 c d := by
  unfold P
  decide +kernel

lemma q_12_11 : ∀ c d : Fin 13, P 12 11 c d := by
  unfold P
  decide +kernel

lemma q_12_12 : ∀ c d : Fin 13, P 12 12 c d := by
  unfold P
  decide +kernel

lemma q_12 : ∀ b c d : Fin 13, P 12 b c d := by
  intro b
  fin_cases b
  exacts [q_12_0, q_12_1, q_12_2, q_12_3, q_12_4, q_12_5, q_12_6, q_12_7, q_12_8, q_12_9, q_12_10, q_12_11, q_12_12]

lemma quad : ∀ a b c d : Fin 13, P a b c d := by
  intro a
  fin_cases a
  exacts [q_0, q_1, q_2, q_3, q_4, q_5, q_6, q_7, q_8, q_9, q_10, q_11, q_12]

lemma inc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
    circ.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l)))
      = decide (((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 1), (2, 2), (5, 4)] : List (ℕ × ℕ))) := by
  decide +kernel

lemma rb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (13 + 13) circ := by
  unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack
  decide +kernel

end PEqualNP.Outside.L_meta_1747

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_1747 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [44, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [45, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [46, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [47, 43] }], output := 48 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 23 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (13 + 13) C ∧
  (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
     C.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l)))
       = decide (((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 1), (2, 2), (5, 4)] : List (ℕ × ℕ)))) ∧
  (∀ Q : Finset (Fin 13), Q.card = 4 →
     (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
     C.eval (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q))
             ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) := by
  rintro C rfl
  refine ⟨rfl, PEqualNP.Outside.L_meta_1747.rb, ?_, PEqualNP.Outside.L_meta_1747.inc, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, rfl⟩
  · intro Q hQ hlines
    obtain ⟨a, b, c, d, hab, hbc, hcd, rfl⟩ := PEqualNP.Outside.L_meta_1747.four Q hQ
    exact PEqualNP.Outside.L_meta_1747.quad a b c d hab hbc hcd hlines
