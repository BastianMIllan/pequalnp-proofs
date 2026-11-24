import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2157

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem getD_app_lt {α : Type} (l l' : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_len {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def dflt : Gate := Gate.mk GateOp.or []

def run {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) w

theorem run_snoc {α : Type} (f : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    run f (gs ++ [g]) w = run f gs w ++ [f (run f gs w) g] := by
  simp [run]

theorem run_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) :
    (run f gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem run_lt {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) (d : α) (i : ℕ)
    (h : i < w.length) : (run f gs w).getD i d = w.getD i d := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [run_snoc, getD_app_lt _ _ _ _ (by rw [run_length]; omega), ih]

theorem run_gate {α : Type} (f : List α → Gate → α) (d : α)
    (hf : ∀ (g : Gate) (w w' : List α), (∀ i ∈ g.inputs, w.getD i d = w'.getD i d) → f w g = f w' g)
    (gs : List Gate) (w : List α) (L : ℕ) (hL : w.length = L) (k : ℕ) (hk : k < gs.length)
    (hr : ∀ i ∈ (gs.getD k dflt).inputs, i < L + k) :
    (run f gs w).getD (L + k) d = f (run f gs w) (gs.getD k dflt) := by
  subst hL
  induction gs using List.reverseRecOn with
  | nil => simp at hk
  | append_singleton gs g ih =>
    rw [run_snoc]
    rcases Nat.lt_or_ge k gs.length with h | h
    · have e : (gs ++ [g]).getD k dflt = gs.getD k dflt := getD_app_lt _ _ _ _ h
      rw [e] at hr ⊢
      rw [getD_app_lt _ _ _ _ (by rw [run_length]; omega), ih h hr]
      apply hf
      intro i hi
      symm
      exact getD_app_lt _ _ _ _ (by rw [run_length]; have := hr i hi; omega)
    · have hk' : k = gs.length := by
        simp only [List.length_append, List.length_singleton] at hk
        omega
      subst hk'
      have e : (gs ++ [g]).getD gs.length dflt = g := getD_app_len _ _ _
      rw [e] at hr ⊢
      have e2 : w.length + gs.length = (run f gs w).length := (run_length f gs w).symm
      rw [e2, getD_app_len]
      apply hf
      intro i hi
      symm
      exact getD_app_lt _ _ _ _ (by rw [run_length]; have := hr i hi; omega)

def evf (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem evf_congr (g : Gate) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = w'.getD i false) : evf w g = evf w' g := by
  unfold evf
  rw [List.map_congr_left h]

def wv (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn z)).getD w false

theorem wires_run (C : Circuit) (inp : List Bool) : C.wires inp = run evf C.gates inp := rfl

theorem wv_input (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) (h : w < N) :
    wv C N z w = z ⟨w, h⟩ := by
  unfold wv
  rw [wires_run, run_lt _ _ _ _ _ (by simpa using h),
    List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem wv_ge (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) (h : N + C.gates.length ≤ w) :
    wv C N z w = false := by
  unfold wv
  rw [wires_run]
  exact getD_ge _ _ _ (by rw [run_length]; simpa using h)

theorem wv_gate (C : Circuit) (N : ℕ) (z : Fin N → Bool) (hR : ReadsBack N C) (k : ℕ)
    (hk : k < C.gates.length) :
    wv C N z (N + k) = (C.gates.getD k dflt).op.eval ((C.gates.getD k dflt).inputs.map (wv C N z)) := by
  unfold wv
  rw [wires_run]
  exact run_gate evf false evf_congr C.gates _ N (by simp) k hk (hR k hk)

theorem gate_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : C.gates.getD k dflt ∈ C.gates := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem _

theorem gate_ops (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < C.gates.length) :
    ((C.gates.getD k dflt).op = GateOp.and ∨ (C.gates.getD k dflt).op = GateOp.or) ∧
    (C.gates.getD k dflt).inputs.length ≤ 2 := by
  obtain ⟨h1, h2⟩ := hM _ (gate_mem C k hk)
  refine ⟨?_, h2⟩
  simpa using h1

-- flipping one input bit
def flip (x : Fin 6 → Bool) (i : Fin 6) : Fin 6 → Bool := Function.update x i (!x i)

-- the inputs a wire really depends on, among the assignments satisfying P
noncomputable def rel (C : Circuit) (P : (Fin 6 → Bool) → Prop) (w : ℕ) : Finset (Fin 6) :=
  @Finset.filter _ (fun i => ∃ x, P x ∧ P (flip x i) ∧ wv C 6 x w ≠ wv C 6 (flip x i) w)
    (Classical.decPred _) Finset.univ

theorem mem_rel (C : Circuit) (P : (Fin 6 → Bool) → Prop) (w : ℕ) (i : Fin 6) :
    i ∈ rel C P w ↔ ∃ x, P x ∧ P (flip x i) ∧ wv C 6 x w ≠ wv C 6 (flip x i) w := by
  unfold rel
  rw [@Finset.mem_filter _ _ (Classical.decPred _)]
  simp

theorem rel_input (C : Circuit) (P : (Fin 6 → Bool) → Prop) (w : ℕ) (hw : w < 6) :
    ∀ i ∈ rel C P w, (i : ℕ) = w := by
  intro i hi
  rw [mem_rel] at hi
  obtain ⟨x, _, _, hne⟩ := hi
  rw [wv_input C 6 x w hw, wv_input C 6 _ w hw] at hne
  by_contra hiw
  apply hne
  have hne2 : (⟨w, hw⟩ : Fin 6) ≠ i := fun e => hiw (by rw [← e])
  unfold flip
  rw [Function.update_of_ne hne2]

theorem rel_input_card (C : Circuit) (P : (Fin 6 → Bool) → Prop) (w : ℕ) (hw : w < 6) :
    (rel C P w).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  apply Fin.ext
  rw [rel_input C P w hw a ha, rel_input C P w hw b hb]

theorem rel_gate (C : Circuit) (P : (Fin 6 → Bool) → Prop) (hR : ReadsBack 6 C) (k : ℕ)
    (hk : k < C.gates.length) (i : Fin 6) (hi : i ∈ rel C P (6 + k)) :
    ∃ a ∈ (C.gates.getD k dflt).inputs, i ∈ rel C P a := by
  rw [mem_rel] at hi
  obtain ⟨x, h1, h2, hne⟩ := hi
  rw [wv_gate C 6 x hR k hk, wv_gate C 6 _ hR k hk] at hne
  by_contra hno
  push Not at hno
  apply hne
  congr 1
  apply List.map_congr_left
  intro a ha
  by_contra hd
  exact hno a ha ((mem_rel C P a i).mpr ⟨x, h1, h2, hd⟩)

theorem rel_ge (C : Circuit) (P : (Fin 6 → Bool) → Prop) (w : ℕ) (hw : 6 + C.gates.length ≤ w)
    (i : Fin 6) : i ∉ rel C P w := by
  intro hi
  rw [mem_rel] at hi
  obtain ⟨x, _, _, hne⟩ := hi
  rw [wv_ge C 6 x w hw, wv_ge C 6 _ w hw] at hne
  exact hne rfl

def cnt (E : Finset ℕ) (k : ℕ) : ℕ := ((Finset.range k).filter (fun j => 6 + j ∉ E)).card

theorem cnt_mono (E : Finset ℕ) (k : ℕ) : cnt E k ≤ cnt E (k + 1) := by
  unfold cnt
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
  exact ⟨by omega, hj.2⟩

theorem cnt_succ (E : Finset ℕ) (k : ℕ) (h : 6 + k ∉ E) : cnt E (k + 1) = cnt E k + 1 := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert, if_pos h]
  apply Finset.card_insert_of_notMem
  simp

theorem count (C : Circuit) (P : (Fin 6 → Bool) → Prop) (hR : ReadsBack 6 C)
    (hfan : ∀ k < C.gates.length, (C.gates.getD k dflt).inputs.length ≤ 2) (X E : Finset ℕ)
    (hX : ∀ k < C.gates.length, ∀ a ∈ (C.gates.getD k dflt).inputs, a ∉ X)
    (hE : ∀ k < C.gates.length, 6 + k ∈ E →
      6 + k ∈ X ∨ ∃ a ∈ (C.gates.getD k dflt).inputs, rel C P (6 + k) ⊆ rel C P a) :
    ∀ k ≤ C.gates.length, ∀ T : Finset ℕ, (∀ w ∈ T, w < 6 + k) → (∀ w ∈ T, w ∉ X) →
      (T.biUnion (rel C P)).card ≤ T.card + cnt E k := by
  intro k
  induction k with
  | zero =>
    intro _ T hT _
    calc (T.biUnion (rel C P)).card ≤ ∑ w ∈ T, (rel C P w).card := Finset.card_biUnion_le
      _ ≤ ∑ w ∈ T, 1 := Finset.sum_le_sum (fun w hw => rel_input_card C P w (by have := hT w hw; omega))
      _ = T.card := by simp
      _ ≤ T.card + cnt E 0 := Nat.le_add_right _ _
  | succ k ih =>
    intro hk T hT hTX
    have hk' : k < C.gates.length := by omega
    have hm1 := cnt_mono E k
    by_cases hm : 6 + k ∈ T
    · by_cases hEk : 6 + k ∈ E
      · rcases hE k hk' hEk with hx | ⟨a, ha, hsub⟩
        · exact absurd hx (hTX _ hm)
        · have hra : a < 6 + k := hR k hk' a ha
          let T' := insert a (T.erase (6 + k))
          have h1 : T.biUnion (rel C P) ⊆ T'.biUnion (rel C P) := by
            intro i hi
            rw [Finset.mem_biUnion] at hi ⊢
            obtain ⟨w, hw, hi⟩ := hi
            by_cases hwm : w = 6 + k
            · subst hwm
              exact ⟨a, Finset.mem_insert_self _ _, hsub hi⟩
            · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwm, hw⟩), hi⟩
          have h2 := ih (by omega) T' (by
            intro w hw
            rcases Finset.mem_insert.mp hw with e | hw
            · omega
            · have := Finset.mem_erase.mp hw
              have := hT w this.2
              omega) (by
            intro w hw
            rcases Finset.mem_insert.mp hw with e | hw
            · rw [e]; exact hX k hk' a ha
            · exact hTX w (Finset.mem_erase.mp hw).2)
          have h3 := Finset.card_le_card h1
          have h4 : T'.card ≤ (T.erase (6 + k)).card + 1 := Finset.card_insert_le _ _
          have h5 := Finset.card_erase_of_mem hm
          have h6 : 1 ≤ T.card := Finset.card_pos.mpr ⟨_, hm⟩
          omega
      · have hs := cnt_succ E k hEk
        let T' := (T.erase (6 + k)) ∪ (C.gates.getD k dflt).inputs.toFinset
        have h1 : T.biUnion (rel C P) ⊆ T'.biUnion (rel C P) := by
          intro i hi
          rw [Finset.mem_biUnion] at hi ⊢
          obtain ⟨w, hw, hi⟩ := hi
          by_cases hwm : w = 6 + k
          · subst hwm
            obtain ⟨a, ha, hia⟩ := rel_gate C P hR k hk' i hi
            exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.mpr ha), hia⟩
          · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwm, hw⟩), hi⟩
        have h2 := ih (by omega) T' (by
            intro w hw
            rcases Finset.mem_union.mp hw with hw | hw
            · have := Finset.mem_erase.mp hw
              have := hT w this.2
              omega
            · exact hR k hk' w (List.mem_toFinset.mp hw)) (by
            intro w hw
            rcases Finset.mem_union.mp hw with hw | hw
            · exact hTX w (Finset.mem_erase.mp hw).2
            · exact hX k hk' w (List.mem_toFinset.mp hw))
        have h3 := Finset.card_le_card h1
        have h4 : T'.card ≤ (T.erase (6 + k)).card + (C.gates.getD k dflt).inputs.toFinset.card :=
          Finset.card_union_le _ _
        have h5 := Finset.card_erase_of_mem hm
        have h6 : 1 ≤ T.card := Finset.card_pos.mpr ⟨_, hm⟩
        have h7 := List.toFinset_card_le (C.gates.getD k dflt).inputs
        have h8 := hfan k hk'
        omega
    · have h2 := ih (by omega) T (by
        intro w hw
        have := hT w hw
        have : w ≠ 6 + k := fun e => hm (e ▸ hw)
        omega) hTX
      omega

theorem final (C : Circuit) (P : (Fin 6 → Bool) → Prop) (hR : ReadsBack 6 C)
    (hfan : ∀ k < C.gates.length, (C.gates.getD k dflt).inputs.length ≤ 2) (X E : Finset ℕ)
    (hX : ∀ k < C.gates.length, ∀ a ∈ (C.gates.getD k dflt).inputs, a ∉ X)
    (hE : ∀ k < C.gates.length, 6 + k ∈ E →
      6 + k ∈ X ∨ ∃ a ∈ (C.gates.getD k dflt).inputs, rel C P (6 + k) ⊆ rel C P a)
    (hout : C.output ∉ X) :
    (rel C P C.output).card ≤ 1 + cnt E C.gates.length := by
  by_cases ho : C.output < 6 + C.gates.length
  · have := count C P hR hfan X E hX hE C.gates.length le_rfl {C.output}
      (by intro w hw; rw [Finset.mem_singleton.mp hw]; exact ho)
      (by intro w hw; rw [Finset.mem_singleton.mp hw]; exact hout)
    rw [Finset.singleton_biUnion, Finset.card_singleton] at this
    omega
  · have hs : rel C P C.output ⊆ ∅ := fun i hi => absurd hi (rel_ge C P C.output (by omega) i)
    have := Finset.card_le_card hs
    rw [Finset.card_empty] at this
    omega

theorem reach (C : Circuit) (P : (Fin 6 → Bool) → Prop) (hR : ReadsBack 6 C) :
    ∀ w : ℕ, ∀ i : Fin 6, i ∈ rel C P w →
      w = (i : ℕ) ∨ ∃ k < C.gates.length, (i : ℕ) ∈ (C.gates.getD k dflt).inputs := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro i hi
    by_cases h6 : w < 6
    · left; exact (rel_input C P w h6 i hi).symm
    · by_cases hl : w < 6 + C.gates.length
      · have hw : w = 6 + (w - 6) := by omega
        rw [hw] at hi
        obtain ⟨a, ha, hia⟩ := rel_gate C P hR (w - 6) (by omega) i hi
        have hra : a < 6 + (w - 6) := hR (w - 6) (by omega) a ha
        rcases ih a (by omega) i hia with e | e
        · right; exact ⟨w - 6, by omega, e ▸ ha⟩
        · right; exact e
      · exact absurd hi (rel_ge C P w (by omega) i)

def f6 (z : Fin 6 → Bool) : Bool :=
  (z 0 && z 3) || (z 0 && z 4) || (z 0 && z 5) || (z 1 && z 2) || (z 1 && z 3) || (z 1 && z 4) || (z 1 && z 5)

theorem wit (C : Circuit) (P : (Fin 6 → Bool) → Prop) (hf : ∀ x, wv C 6 x C.output = f6 x)
    (i : Fin 6) (x : Fin 6 → Bool) (h1 : P x) (h2 : P (flip x i)) (h3 : f6 x ≠ f6 (flip x i)) :
    i ∈ rel C P C.output := by
  rw [mem_rel]
  exact ⟨x, h1, h2, by rw [hf, hf]; exact h3⟩

theorem card5 (s : Finset (Fin 6)) (h : ∀ i : Fin 6, i ≠ 2 → i ∈ s) : 5 ≤ s.card := by
  have : (Finset.univ.erase (2 : Fin 6)) ⊆ s := by
    intro i hi
    exact h i (Finset.mem_erase.mp hi).1
  have := Finset.card_le_card this
  rw [Finset.card_erase_of_mem (Finset.mem_univ _)] at this
  simpa using this

theorem card6 (s : Finset (Fin 6)) (h : ∀ i : Fin 6, i ∈ s) : 6 ≤ s.card := by
  have : (Finset.univ : Finset (Fin 6)) ⊆ s := fun i _ => h i
  have := Finset.card_le_card this
  simpa using this

theorem all6 (C : Circuit) (hf : ∀ x, wv C 6 x C.output = f6 x) :
    6 ≤ (rel C (fun _ => True) C.output).card := by
  apply card6
  intro i
  fin_cases i
  · exact wit C _ hf _ ![false, false, false, true, false, false] trivial trivial (by decide)
  · exact wit C _ hf _ ![false, false, true, false, false, false] trivial trivial (by decide)
  · exact wit C _ hf _ ![false, true, false, false, false, false] trivial trivial (by decide)
  · exact wit C _ hf _ ![true, false, false, false, false, false] trivial trivial (by decide)
  · exact wit C _ hf _ ![true, false, false, false, false, false] trivial trivial (by decide)
  · exact wit C _ hf _ ![true, false, false, false, false, false] trivial trivial (by decide)

theorem five (C : Circuit) (hf : ∀ x, wv C 6 x C.output = f6 x) (c : Bool) :
    5 ≤ (rel C (fun x => x 2 = c) C.output).card := by
  apply card5
  intro i hi
  cases c
  · fin_cases i
    · exact wit C _ hf _ ![false, false, false, true, false, false] rfl rfl (by decide)
    · exact wit C _ hf _ ![false, false, false, true, false, false] rfl rfl (by decide)
    · exact absurd rfl hi
    · exact wit C _ hf _ ![true, false, false, false, false, false] rfl rfl (by decide)
    · exact wit C _ hf _ ![true, false, false, false, false, false] rfl rfl (by decide)
    · exact wit C _ hf _ ![true, false, false, false, false, false] rfl rfl (by decide)
  · fin_cases i
    · exact wit C _ hf _ ![false, false, true, true, false, false] rfl rfl (by decide)
    · exact wit C _ hf _ ![false, false, true, false, false, false] rfl rfl (by decide)
    · exact absurd rfl hi
    · exact wit C _ hf _ ![true, false, true, false, false, false] rfl rfl (by decide)
    · exact wit C _ hf _ ![true, false, true, false, false, false] rfl rfl (by decide)
    · exact wit C _ hf _ ![true, false, true, false, false, false] rfl rfl (by decide)

-- a wire that is constant on the assignments satisfying P has no relevant input
theorem rel_const (C : Circuit) (P : (Fin 6 → Bool) → Prop) (w : ℕ) (c : Bool)
    (h : ∀ x, P x → wv C 6 x w = c) (i : Fin 6) : i ∉ rel C P w := by
  intro hi
  rw [mem_rel] at hi
  obtain ⟨x, h1, h2, hne⟩ := hi
  rw [h x h1, h _ h2] at hne
  exact hne rfl

-- a gate reading a constant wire h depends only on its other input
theorem rel_reader (C : Circuit) (P : (Fin 6 → Bool) → Prop) (hR : ReadsBack 6 C) (h : ℕ) (c : Bool)
    (hc : ∀ x, P x → wv C 6 x h = c) (k : ℕ) (hk : k < C.gates.length)
    (hlen : (C.gates.getD k dflt).inputs.length ≤ 2) (hmem : h ∈ (C.gates.getD k dflt).inputs) :
    ∃ a ∈ (C.gates.getD k dflt).inputs, rel C P (6 + k) ⊆ rel C P a := by
  have key : ∀ i ∈ rel C P (6 + k), ∃ a ∈ (C.gates.getD k dflt).inputs, a ≠ h ∧ i ∈ rel C P a := by
    intro i hi
    rw [mem_rel] at hi
    obtain ⟨x, h1, h2, hne⟩ := hi
    rw [wv_gate C 6 x hR k hk, wv_gate C 6 _ hR k hk] at hne
    by_contra hno
    push Not at hno
    apply hne
    congr 1
    apply List.map_congr_left
    intro a ha
    by_cases hah : a = h
    · rw [hah, hc x h1, hc _ h2]
    · by_contra hd
      exact hno a ha hah ((mem_rel C P a i).mpr ⟨x, h1, h2, hd⟩)
  revert hlen hmem key
  rcases (C.gates.getD k dflt).inputs with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, t⟩⟩⟩
  · intro _ hmem; simp at hmem
  · intro _ hmem key
    refine ⟨a1, List.mem_singleton_self _, ?_⟩
    intro i hi
    obtain ⟨a, ha, hah, _⟩ := key i hi
    have e1 := List.mem_singleton.mp ha
    have e2 := List.mem_singleton.mp hmem
    exact absurd (e1.trans e2.symm) hah
  · intro _ hmem key
    by_cases h1 : a1 = h
    · refine ⟨a2, by simp, ?_⟩
      intro i hi
      obtain ⟨a, ha, hah, hia⟩ := key i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with e | e
      · exact absurd (e.trans h1) hah
      · exact e ▸ hia
    · refine ⟨a1, by simp, ?_⟩
      intro i hi
      obtain ⟨a, ha, hah, hia⟩ := key i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hmem
      rcases hmem with e0 | e0
      · exact absurd e0.symm h1
      · rcases ha with e | e
        · exact e ▸ hia
        · exact absurd (e.trans e0.symm) hah
  · intro hlen; simp at hlen

theorem main (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack 6 C)
    (hf : ∀ x, wv C 6 x C.output = f6 x) : 6 ≤ C.gates.length := by
  by_contra hlt
  have hlen : C.gates.length ≤ 5 := by omega
  have hfan : ∀ k < C.gates.length, (C.gates.getD k dflt).inputs.length ≤ 2 :=
    fun k hk => (gate_ops C hM k hk).2
  have hall := all6 C hf
  -- some gate reads input 2
  have h2 : (2 : Fin 6) ∈ rel C (fun _ => True) C.output := by
    apply wit C _ hf _ ![false, true, false, false, false, false] trivial trivial (by decide)
  rcases reach C _ hR C.output 2 h2 with ho | ⟨k0, hk0, hin⟩
  · have := rel_input_card C (fun _ => True) C.output (by rw [ho]; decide)
    omega
  -- the controlling value of gate k0
  have hconst : ∃ c : Bool, ∀ x, x 2 = c → wv C 6 x (6 + k0) = c := by
    rcases (gate_ops C hM k0 hk0).1 with hop | hop
    · refine ⟨false, fun x hx => ?_⟩
      rw [wv_gate C 6 x hR k0 hk0, hop]
      simp only [GateOp.eval]
      rw [List.all_eq_false]
      refine ⟨false, ?_, by simp⟩
      rw [List.mem_map]
      exact ⟨2, by simpa using hin, by rw [wv_input C 6 x 2 (by decide)]; exact hx⟩
    · refine ⟨true, fun x hx => ?_⟩
      rw [wv_gate C 6 x hR k0 hk0, hop]
      simp only [GateOp.eval]
      rw [List.any_eq_true]
      refine ⟨true, ?_, rfl⟩
      rw [List.mem_map]
      exact ⟨2, by simpa using hin, by rw [wv_input C 6 x 2 (by decide)]; exact hx⟩
  obtain ⟨c, hc⟩ := hconst
  let P : (Fin 6 → Bool) → Prop := fun x => x 2 = c
  have h5 : 5 ≤ (rel C P C.output).card := five C hf c
  by_cases hout : C.output = 6 + k0
  · -- the output is constant under the restriction
    have : rel C P C.output ⊆ ∅ := fun i hi =>
      absurd hi (rel_const C P C.output c (fun x hx => by rw [hout]; exact hc x hx) i)
    have := Finset.card_le_card this
    rw [Finset.card_empty] at this
    omega
  by_cases hread : ∃ k1 < C.gates.length, 6 + k0 ∈ (C.gates.getD k1 dflt).inputs
  · obtain ⟨k1, hk1, hr1⟩ := hread
    have hlt01 : 6 + k0 < 6 + k1 := hR k1 hk1 _ hr1
    have hb := final C P hR hfan ∅ {6 + k0, 6 + k1}
      (fun _ _ _ _ => Finset.notMem_empty _)
      (by
        intro k hk hkE
        right
        rcases Finset.mem_insert.mp hkE with e | e
        · have ek : k = k0 := by omega
          subst ek
          refine ⟨2, by simpa using hin, ?_⟩
          intro i hi
          exact absurd hi (rel_const C P (6 + k) c hc i)
        · have ek : k = k1 := by
            have := Finset.mem_singleton.mp e
            omega
          subst ek
          exact rel_reader C P hR (6 + k0) c hc k hk (hfan k hk) hr1)
      (Finset.notMem_empty _)
    have hcnt : cnt {6 + k0, 6 + k1} C.gates.length ≤ C.gates.length - 2 := by
      unfold cnt
      have hs : (Finset.range C.gates.length).filter (fun j => 6 + j ∉ ({6 + k0, 6 + k1} : Finset ℕ)) ⊆
          ((Finset.range C.gates.length).erase k0).erase k1 := by
        intro j hj
        rw [Finset.mem_filter] at hj
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨fun e => hj.2.2 (by rw [e]), fun e => hj.2.1 (by rw [e]), hj.1⟩
      have := Finset.card_le_card hs
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr hk1⟩),
        Finset.card_erase_of_mem (Finset.mem_range.mpr hk0), Finset.card_range] at this
      omega
    omega
  · push Not at hread
    have hb := final C (fun _ => True) hR hfan {6 + k0} {6 + k0}
      (by
        intro k hk a ha hX
        rw [Finset.mem_singleton.mp hX] at ha
        exact hread k hk ha)
      (fun k _ hkE => Or.inl hkE)
      (by rw [Finset.mem_singleton]; exact hout)
    have hcnt : cnt {6 + k0} C.gates.length ≤ C.gates.length - 1 := by
      unfold cnt
      have hs : (Finset.range C.gates.length).filter (fun j => 6 + j ∉ ({6 + k0} : Finset ℕ)) ⊆
          (Finset.range C.gates.length).erase k0 := by
        intro j hj
        rw [Finset.mem_filter] at hj
        simp only [Finset.mem_singleton] at hj
        rw [Finset.mem_erase]
        exact ⟨fun e => hj.2 (by rw [e]), hj.1⟩
      have := Finset.card_le_card hs
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hk0), Finset.card_range] at this
      omega
    omega

end PEqualNP.Outside.L_meta_2157

theorem PEqualNP.Outside.L_meta_2157 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun z : Fin 6 → Bool => (z 0 && z 3) || (z 0 && z 4) || (z 0 && z 5) || (z 1 && z 2) || (z 1 && z 3) || (z 1 && z 4) || (z 1 && z 5)) x) → 6 ≤ C.size := by
  intro C hm hR hf
  exact PEqualNP.Outside.L_meta_2157.main C hm hR (fun x => hf x)
