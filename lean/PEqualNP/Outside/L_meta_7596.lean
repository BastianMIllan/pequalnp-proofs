import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7596

open PEqualNP.CircuitLowerBounds

theorem gd_left {α : Type} (l l' : List α) (d : α) (n : ℕ) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gd_right {α : Type} (l : List α) (a d : α) (n : ℕ) (h : l.length = n) :
    (l ++ [a]).getD n d = a := by
  subst h; simp [List.getD_eq_getElem?_getD]

theorem gd_out {α : Type} (l : List α) (d : α) (n : ℕ) (h : l.length ≤ n) :
    l.getD n d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

def step (d : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  d ++ [g.inputs.toFinset.biUnion (fun i => d.getD i ∅)]

def deps (gs : List Gate) (n : ℕ) : List (Finset ℕ) :=
  gs.foldl step ((List.range n).map fun i => {i})

theorem deps_nil (n : ℕ) : deps [] n = (List.range n).map fun i => {i} := rfl

theorem deps_snoc (gs : List Gate) (g : Gate) (n : ℕ) :
    deps (gs ++ [g]) n
      = deps gs n ++ [g.inputs.toFinset.biUnion (fun i => (deps gs n).getD i ∅)] := by
  simp [deps, List.foldl_append, step]

theorem deps_length (gs : List Gate) (n : ℕ) : (deps gs n).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [deps_nil]
  | append_singleton gs g ih => rw [deps_snoc]; simp [ih]; omega

theorem agree (gs : List Gate) (n : ℕ) (x y : List Bool) (hx : x.length = n)
    (hy : y.length = n) :
    ∀ o, (∀ v ∈ (deps gs n).getD o ∅, x.getD v false = y.getD v false) →
      (W gs x).getD o false = (W gs y).getD o false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro o h
    show x.getD o false = y.getD o false
    by_cases ho : o < n
    · apply h
      simp [deps_nil, List.getD_eq_getElem?_getD, ho]
    · rw [gd_out _ _ _ (by omega), gd_out _ _ _ (by omega)]
  | append_singleton gs g ih =>
    intro o h
    rw [W_snoc, W_snoc]
    have lx := W_length gs x
    have ly := W_length gs y
    have hl := deps_length gs n
    rcases lt_trichotomy o (n + gs.length) with ho | ho | ho
    · rw [gd_left _ _ _ _ (by omega), gd_left _ _ _ _ (by omega)]
      apply ih
      intro v hv
      apply h
      rw [deps_snoc, gd_left _ _ _ _ (by omega)]
      exact hv
    · subst ho
      rw [gd_right _ _ _ _ (by omega), gd_right _ _ _ _ (by omega)]
      congr 1
      apply List.map_congr_left
      intro i hi
      apply ih
      intro v hv
      apply h
      rw [deps_snoc, gd_right _ _ _ _ hl]
      exact Finset.mem_biUnion.2 ⟨i, List.mem_toFinset.2 hi, hv⟩
    · rw [gd_out _ _ _ (by simp; omega), gd_out _ _ _ (by simp; omega)]

theorem count (gs : List Gate) (n : ℕ) (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ O : Finset ℕ, (O.biUnion fun o => (deps gs n).getD o ∅).card ≤ gs.length + O.card := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro O
    simp only [List.length_nil, zero_add]
    refine (Finset.card_biUnion_le).trans ?_
    calc ∑ o ∈ O, ((deps [] n).getD o ∅).card ≤ ∑ _o ∈ O, 1 :=
          Finset.sum_le_sum fun o _ => by
            by_cases ho : o < n
            · simp [deps_nil, List.getD_eq_getElem?_getD, ho]
            · rw [gd_out _ _ _ (by simp [deps_nil]; omega)]; simp
      _ = O.card := by simp
  | append_singleton gs g ih =>
    intro O
    have hf' : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g' hg' => hf g' (by simp [hg'])
    have hg : g.inputs.length ≤ 2 := hf g (by simp)
    have ih' := ih hf'
    have hl := deps_length gs n
    have key : ∀ o, o ≠ n + gs.length →
        (deps (gs ++ [g]) n).getD o ∅ = (deps gs n).getD o ∅ := by
      intro o ho
      rw [deps_snoc]
      rcases lt_or_gt_of_ne ho with h | h
      · exact gd_left _ _ _ _ (by omega)
      · rw [gd_out _ _ _ (by simp; omega), gd_out _ _ _ (by omega)]
    have kN : (deps (gs ++ [g]) n).getD (n + gs.length) ∅
        = g.inputs.toFinset.biUnion (fun i => (deps gs n).getD i ∅) := by
      rw [deps_snoc]; exact gd_right _ _ _ _ hl
    simp only [List.length_append, List.length_singleton]
    by_cases hN : n + gs.length ∈ O
    · have hsub : (O.biUnion fun o => (deps (gs ++ [g]) n).getD o ∅) ⊆
          ((O.erase (n + gs.length)) ∪ g.inputs.toFinset).biUnion
            (fun o => (deps gs n).getD o ∅) := by
        intro v hv
        rw [Finset.mem_biUnion] at hv ⊢
        obtain ⟨o, hoO, hv⟩ := hv
        by_cases hoN : o = n + gs.length
        · subst hoN
          rw [kN, Finset.mem_biUnion] at hv
          obtain ⟨i, hi, hv⟩ := hv
          exact ⟨i, Finset.mem_union_right _ hi, hv⟩
        · rw [key o hoN] at hv
          exact ⟨o, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hoN, hoO⟩), hv⟩
      refine (Finset.card_le_card hsub).trans ((ih' _).trans ?_)
      have h1 := Finset.card_union_le (O.erase (n + gs.length)) g.inputs.toFinset
      have h2 := Finset.card_erase_of_mem hN
      have h3 := List.toFinset_card_le g.inputs
      have h4 : 0 < O.card := Finset.card_pos.2 ⟨_, hN⟩
      omega
    · have heq : (O.biUnion fun o => (deps (gs ++ [g]) n).getD o ∅)
          = O.biUnion (fun o => (deps gs n).getD o ∅) := by
        apply Finset.biUnion_congr rfl
        intro o ho
        exact key o (fun h => hN (h ▸ ho))
      rw [heq]
      have := ih' O
      omega

theorem relevant (N : ℕ) (C : Circuit) (x y : Fin N → Bool) (v : ℕ)
    (hxy : ∀ i : Fin N, i.val ≠ v → x i = y i)
    (hne : MetaComplexity.circuitFun N C x ≠ MetaComplexity.circuitFun N C y) :
    v ∈ (deps C.gates N).getD C.output ∅ := by
  by_contra hv
  apply hne
  show (W C.gates (List.ofFn x)).getD C.output false
    = (W C.gates (List.ofFn y)).getD C.output false
  apply agree C.gates N (List.ofFn x) (List.ofFn y) (by simp) (by simp) C.output
  intro u hu
  have huv : u ≠ v := fun h => hv (h ▸ hu)
  by_cases hu' : u < N
  · have := hxy ⟨u, hu'⟩ huv
    simp [List.getD_eq_getElem?_getD, hu', this]
  · rw [gd_out _ _ _ (by simp; omega), gd_out _ _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_7596

theorem PEqualNP.Outside.L_meta_7596 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1 × Fin x1)), (∀ x4 ∈ x2.gates, x4.inputs.length ≤ (2 : ℕ)) → (∀ (x5 : Fin (x1 + x1)), (PEqualNP.MetaComplexity.circuitFun (x1 + x1) x2 fun (x6 : Fin (x1 + x1)) => Decidable.decide (x6 = x5)) = Bool.false) → (∀ x6 ∈ x3, (PEqualNP.MetaComplexity.circuitFun (x1 + x1) x2 fun (x8 : Fin (x1 + x1)) => Decidable.decide (x8 = Fin.castAdd x1 x6.1 ∨ x8 = Fin.natAdd x1 x6.2)) = Bool.true) → (Finset.image Prod.fst x3).card + (Finset.image Prod.snd x3).card ≤ x2.size + (1 : ℕ) := by
  intro x1 x2 x3 hfan hsingle hpair
  set D := (PEqualNP.Outside.L_meta_7596.deps x2.gates (x1 + x1)).getD x2.output ∅ with hD
  set A := (Finset.image Prod.fst x3).image (fun r : Fin x1 => r.val) with hA
  set B := (Finset.image Prod.snd x3).image (fun c : Fin x1 => x1 + c.val) with hB
  have cA : A.card = (Finset.image Prod.fst x3).card :=
    Finset.card_image_of_injective _ Fin.val_injective
  have cB : B.card = (Finset.image Prod.snd x3).card :=
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))
  have disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [hA, Finset.mem_image] at hu
    rw [hB, Finset.mem_image] at hu'
    obtain ⟨r, -, rfl⟩ := hu
    obtain ⟨c, -, hc⟩ := hu'
    have := r.isLt
    omega
  have sub : A ∪ B ⊆ D := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · rw [hA, Finset.mem_image] at hu
      obtain ⟨r, hr, rfl⟩ := hu
      rw [Finset.mem_image] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      apply PEqualNP.Outside.L_meta_7596.relevant (x1 + x1) x2
        (fun x8 => decide (x8 = Fin.castAdd x1 p.1 ∨ x8 = Fin.natAdd x1 p.2))
        (fun x6 => decide (x6 = Fin.natAdd x1 p.2))
      · intro i hi
        have h : ¬ i = Fin.castAdd x1 p.1 := fun h => hi (by subst h; rfl)
        simp only [h, false_or]
      · rw [hpair p hp, hsingle]
        decide
    · rw [hB, Finset.mem_image] at hu
      obtain ⟨c, hc, rfl⟩ := hu
      rw [Finset.mem_image] at hc
      obtain ⟨p, hp, rfl⟩ := hc
      apply PEqualNP.Outside.L_meta_7596.relevant (x1 + x1) x2
        (fun x8 => decide (x8 = Fin.castAdd x1 p.1 ∨ x8 = Fin.natAdd x1 p.2))
        (fun x6 => decide (x6 = Fin.castAdd x1 p.1))
      · intro i hi
        have h : ¬ i = Fin.natAdd x1 p.2 := fun h => hi (by subst h; rfl)
        simp only [h, or_false]
      · rw [hpair p hp, hsingle]
        decide
  have hcount := PEqualNP.Outside.L_meta_7596.count x2.gates (x1 + x1) hfan {x2.output}
  rw [Finset.singleton_biUnion, Finset.card_singleton] at hcount
  have h1 := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint disj, cA, cB] at h1
  have h2 : D.card ≤ x2.gates.length + 1 := hcount
  show _ ≤ x2.gates.length + 1
  omega
