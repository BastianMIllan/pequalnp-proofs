import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2859

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def W (gs : List Gate) (x : List Bool) : List Bool := Circuit.wires ⟨gs, 0⟩ x

def fG (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩

theorem W_nil (x : List Bool) : W [] x = x := by simp [W, Circuit.wires]

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, Circuit.wires, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W, Circuit.wires]
  | append_singleton gs g ih =>
    rw [W_snoc, List.length_append, ih]
    simp
    omega

theorem W_ext (gs hs : List Gate) (x : List Bool) : ∃ t, W (gs ++ hs) x = W gs x ++ t := by
  induction hs using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton hs h ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t ++ [h.op.eval (h.inputs.map fun i => (W (gs ++ hs) x).getD i false)], ?_⟩
    rw [show gs ++ (hs ++ [h]) = (gs ++ hs) ++ [h] from (List.append_assoc _ _ _).symm, W_snoc,
      ht, List.append_assoc]

theorem W_prefix (gs : List Gate) (x : List Bool) (k i : ℕ) (hk : k ≤ gs.length)
    (hi : i < x.length + k) : (W gs x).getD i false = (W (gs.take k) x).getD i false := by
  obtain ⟨t, ht⟩ := W_ext (gs.take k) (gs.drop k) x
  rw [List.take_append_drop] at ht
  rw [ht, List.getD_append _ _ _ _ (by rw [W_length, List.length_take]; omega)]

theorem W_input (gs : List Gate) (x : List Bool) (n i : ℕ) (hn : x.length = n) (hi : i < n) :
    (W gs x).getD i false = x.getD i false := by
  subst hn
  rw [W_prefix gs x 0 i (Nat.zero_le _) (by omega), List.take_zero, W_nil]

theorem W_out (gs : List Gate) (x : List Bool) (n i : ℕ) (hn : x.length = n)
    (hi : n + gs.length ≤ i) : (W gs x).getD i false = false := by
  subst hn
  rw [List.getD_eq_default _ _ (by rw [W_length]; omega)]

theorem W_gate (gs : List Gate) (x : List Bool) (n j : ℕ) (g : Gate) (hn : x.length = n)
    (hg : gs[j]? = some g) (hb : ∀ i ∈ g.inputs, i < n + j) :
    (W gs x).getD (n + j) false = g.op.eval (g.inputs.map fun i => (W gs x).getD i false) := by
  subst hn
  have hj : j < gs.length := (List.getElem?_eq_some_iff.mp hg).1
  rw [W_prefix gs x (j+1) (x.length + j) (by omega) (by omega), List.take_succ, hg,
    Option.toList_some, W_snoc,
    List.getD_append_right _ _ _ _ (by rw [W_length, List.length_take]; omega)]
  have hlen : x.length + j - (W (gs.take j) x).length = 0 := by
    rw [W_length, List.length_take]; omega
  rw [hlen, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (W_prefix gs x j i (by omega) (hb i hi)).symm

theorem gate_of (n : ℕ) (C : Circuit) (hBack : ReadsBack n C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) : ∀ i ∈ g.inputs, i < n + j := by
  obtain ⟨hj, _⟩ := List.getElem?_eq_some_iff.mp hg
  have hga : gateAt C j = g := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, hg]
    rfl
  intro i hi
  exact hBack j hj i (by rw [hga]; exact hi)

theorem main : ∀ (n : ℕ) (C : Circuit) (m p : ℕ), Monotone2 C → ReadsBack n C →
    m < C.gates.length → p < n + m → Monotone2 (eraseGate n C m p) ∧
    ReadsBack n (eraseGate n C m p) ∧ (eraseGate n C m p).size + 1 = C.size ∧
    ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD p false =
      (C.wires (List.ofFn x)).getD (n + m) false →
      (eraseGate n C m p).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro n C m p hMono hBack hm hp
  have hDdef : eraseGate n C m p =
      ⟨C.gates.take m ++ (C.gates.drop (m+1)).map (fG n m p), eraseRedirect n m p C.output⟩ := by
    unfold eraseGate
    rw [if_pos hm]
    all_goals rfl
  rw [hDdef]
  generalize hDg : C.gates.take m ++ (C.gates.drop (m+1)).map (fG n m p) = Dg
  have hlenD : Dg.length + 1 = C.gates.length := by
    rw [← hDg]
    simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
    omega
  have hD1 : ∀ j < m, Dg[j]? = C.gates[j]? := by
    intro j hj
    rw [← hDg, List.getElem?_append_left (by rw [List.length_take]; omega)]
    simp [List.getElem?_take, hj]
  have hD2 : ∀ j, m ≤ j → Dg[j]? = (C.gates[j+1]?).map (fG n m p) := by
    intro j hj
    rw [← hDg, List.getElem?_append_right (by rw [List.length_take]; omega), List.getElem?_map,
      List.getElem?_drop, List.length_take]
    have he : m + 1 + (j - min m C.gates.length) = j + 1 := by omega
    rw [he]
  have hDback : ∀ j g, Dg[j]? = some g → ∀ i ∈ g.inputs, i < n + j := by
    intro j g hg i hi
    by_cases hj : j < m
    · rw [hD1 j hj] at hg
      have := gate_of n C hBack j g hg i hi
      omega
    · rw [hD2 j (by omega)] at hg
      cases h0 : C.gates[j+1]? with
      | none => rw [h0] at hg; simp at hg
      | some g0 =>
        rw [h0] at hg
        simp at hg
        subst hg
        have hin : i ∈ g0.inputs.map (eraseRedirect n m p) := hi
        obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hin
        have := gate_of n C hBack (j+1) g0 h0 i0 hi0
        unfold eraseRedirect
        split_ifs <;> omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Monotone2 at hMono ⊢
    intro g hg
    rw [← hDg] at hg
    rcases List.mem_append.mp hg with h | h
    · exact hMono g (List.mem_of_mem_take h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h
      have := hMono g0 (List.mem_of_mem_drop hg0)
      refine ⟨this.1, ?_⟩
      show (g0.inputs.map (eraseRedirect n m p)).length ≤ 2
      rw [List.length_map]
      exact this.2
  · unfold ReadsBack
    intro j hj i hi
    have hj' : j < Dg.length := hj
    have hga : gateAt ⟨Dg, eraseRedirect n m p C.output⟩ j = Dg[j] := by
      unfold gateAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
      rfl
    rw [hga] at hi
    exact hDback j _ (List.getElem?_eq_getElem hj') i hi
  · show Dg.length + 1 = C.gates.length
    exact hlenD
  · intro x hx
    change (W C.gates (List.ofFn x)).getD p false =
      (W C.gates (List.ofFn x)).getD (n + m) false at hx
    show (W Dg (List.ofFn x)).getD (eraseRedirect n m p C.output) false =
      (W C.gates (List.ofFn x)).getD C.output false
    have hxl : (List.ofFn x).length = n := List.length_ofFn
    generalize List.ofFn x = xs at hx hxl ⊢
    have hrlt : ∀ i', i' < n + m → eraseRedirect n m p i' = i' := by
      intro i' h
      unfold eraseRedirect
      split_ifs <;> omega
    have claim : ∀ i, (W Dg xs).getD (eraseRedirect n m p i) false =
        (W C.gates xs).getD i false := by
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        by_cases h1 : i < n
        · rw [hrlt i (by omega), W_input Dg xs n i hxl h1, W_input C.gates xs n i hxl h1]
        by_cases h2 : i < n + m
        · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
          have hjm : j < m := by omega
          have hjl : j < C.gates.length := by omega
          obtain ⟨g, hg⟩ : ∃ g, C.gates[j]? = some g :=
            ⟨C.gates[j], List.getElem?_eq_getElem hjl⟩
          have hb := gate_of n C hBack j g hg
          rw [hrlt _ h2, W_gate Dg xs n j g hxl (by rw [hD1 j hjm]; exact hg) hb,
            W_gate C.gates xs n j g hxl hg hb]
          congr 1
          apply List.map_congr_left
          intro i' hi'
          have h' := hb i' hi'
          rw [← ih i' (by omega), hrlt i' (by omega)]
        by_cases h3 : i = n + m
        · subst h3
          have hr : eraseRedirect n m p (n + m) = p := by
            unfold eraseRedirect
            split_ifs <;> omega
          rw [hr, ← hx, ← ih p (by omega), hrlt p hp]
        by_cases h4 : i < n + C.gates.length
        · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
          have hjl : j < C.gates.length := by omega
          obtain ⟨g, hg⟩ : ∃ g, C.gates[j]? = some g :=
            ⟨C.gates[j], List.getElem?_eq_getElem hjl⟩
          have hb := gate_of n C hBack j g hg
          have hr : eraseRedirect n m p (n + j) = n + (j - 1) := by
            unfold eraseRedirect
            split_ifs <;> omega
          have hgD : Dg[j-1]? = some (fG n m p g) := by
            rw [hD2 (j-1) (by omega), show j - 1 + 1 = j by omega, hg]
            all_goals rfl
          have hbD := hDback (j-1) _ hgD
          rw [hr, W_gate Dg xs n (j-1) _ hxl hgD hbD, W_gate C.gates xs n j g hxl hg hb]
          show g.op.eval ((g.inputs.map (eraseRedirect n m p)).map
            (fun i => (W Dg xs).getD i false)) = _
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i' hi'
          exact ih i' (hb i' hi')
        · have hr : eraseRedirect n m p i = i - 1 := by
            unfold eraseRedirect
            split_ifs <;> omega
          rw [hr, W_out Dg xs n (i - 1) hxl (by omega), W_out C.gates xs n i hxl (by omega)]
    exact claim C.output

end PEqualNP.Outside.L_meta_2859

theorem PEqualNP.Outside.L_meta_2859 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m p : ℕ), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → m < C.gates.length → p < n + m → PEqualNP.MetaComplexity.Monotone2 (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ (PEqualNP.CircuitMoves.eraseGate n C m p).size + 1 = C.size ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD p false = (C.wires (List.ofFn x)).getD (n + m) false → (PEqualNP.CircuitMoves.eraseGate n C m p).eval (List.ofFn x) = C.eval (List.ofFn x) :=
  PEqualNP.Outside.L_meta_2859.main
