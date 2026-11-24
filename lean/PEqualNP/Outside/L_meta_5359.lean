import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5359
open PEqualNP.CircuitLowerBounds

theorem snoc {n : ℕ} (f : Fin n → Bool) (v : Bool) :
    List.ofFn (fun i : Fin (n + 1) => Fin.lastCases v f i) = List.ofFn f ++ [v] := by
  rw [List.ofFn_succ']
  simp

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

abbrev I (i j : Fin 42) : Prop :=
  (i : ℕ) < (21 : ℕ) ∧ (21 : ℕ) ≤ (j : ℕ) ∧
    ((j : ℕ) + (21 : ℕ) - (i : ℕ)) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]

abbrev F (a : Fin 42 → Bool) : Prop :=
  ∃ (i : Fin 42) (j : Fin 42), I i j ∧ a i = true ∧ a j = true

def cand1 (k : Fin 42) : Fin 42 := ⟨((k : ℕ) + 21) % 42, Nat.mod_lt _ (by norm_num)⟩

def cand2 (k : Fin 42) : Fin 42 :=
  if h : (k : ℕ) < 21 then ⟨21 + ((k : ℕ) + 5) % 21, by omega⟩
  else ⟨((k : ℕ) + 16) % 21, by omega⟩

set_option maxRecDepth 100000 in
theorem pickD : ∀ k p : Fin 42, k ≠ p →
    ∃ m ∈ [cand1 k, cand2 k], (I k m ∨ I m k) ∧ ¬ I p m ∧ ¬ I m p := by
  decide

theorem pick (k p : Fin 42) (h : k ≠ p) :
    ∃ m : Fin 42, (I k m ∨ I m k) ∧ ¬ I p m ∧ ¬ I m p := by
  obtain ⟨m, _, hm⟩ := pickD k p h
  exact ⟨m, hm⟩

def inp (x1 : Fin 42) (x2 x3 : Fin 43) (a : Fin 42 → Bool) : List Bool :=
  List.ofFn fun (j : Fin 44) =>
    Fin.lastCases ((Fin.lastCases (a 0 || a x1) a x2) || (Fin.lastCases (a 0 || a x1) a x3))
      (fun i : Fin 43 => Fin.lastCases (a 0 || a x1) a i) j

theorem inp_eq (x1 : Fin 42) (x2 x3 : Fin 43) (a : Fin 42 → Bool) :
    inp x1 x2 x3 a = List.ofFn a ++ [a 0 || a x1,
      Fin.lastCases (a 0 || a x1) a x2 || Fin.lastCases (a 0 || a x1) a x3] := by
  unfold inp
  rw [snoc, snoc]
  simp

theorem inp_len (x1 : Fin 42) (x2 x3 : Fin 43) (a : Fin 42 → Bool) :
    (inp x1 x2 x3 a).length = 44 := by
  rw [inp_eq]
  simp

theorem getD_inp (x1 : Fin 42) (x2 x3 : Fin 43) (a : Fin 42 → Bool) (i : Fin 42) :
    (inp x1 x2 x3 a).getD (i : ℕ) false = a i := by
  rw [inp_eq, List.getD_append _ _ _ _ (by simp), getD_ofFn]

theorem inp_agree (x1 : Fin 42) (x2 x3 : Fin 43) (a b : Fin 42 → Bool) (k : Fin 42)
    (hab : ∀ i, i ≠ k → a i = b i)
    (h42 : (a 0 || a x1) = (b 0 || b x1))
    (h43 : (Fin.lastCases (a 0 || a x1) a x2 || Fin.lastCases (a 0 || a x1) a x3) =
      (Fin.lastCases (b 0 || b x1) b x2 || Fin.lastCases (b 0 || b x1) b x3)) :
    ∀ i : ℕ, i ≠ (k : ℕ) → (inp x1 x2 x3 a).getD i false = (inp x1 x2 x3 b).getD i false := by
  intro i hi
  rw [inp_eq, inp_eq]
  rcases lt_or_ge i 42 with h | h
  · rw [List.getD_append _ _ _ _ (by simp [h]), List.getD_append _ _ _ _ (by simp [h])]
    exact (getD_ofFn a ⟨i, h⟩).trans
      ((hab _ (fun e => hi (congrArg Fin.val e))).trans (getD_ofFn b ⟨i, h⟩).symm)
  · rw [List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    rcases (show i - 42 = 0 ∨ i - 42 = 1 ∨ 2 ≤ i - 42 by omega) with e | e | e
    · rw [e]
      simpa using h42
    · rw [e]
      simpa using h43
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem fold_prefix : ∀ (gs : List Gate) (u : List Bool) (i : ℕ), i < u.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) u).getD i false
      = u.getD i false := by
  intro gs
  induction gs with
  | nil => intro u i _; rfl
  | cons g gs ih =>
    intro u i hi
    rw [List.foldl_cons, ih _ _ (by simp; omega), List.getD_append _ _ _ _ hi]

theorem fold_agree (k : ℕ) : ∀ (gs : List Gate), (∀ g ∈ gs, k ∉ g.inputs) →
    ∀ u v : List Bool, u.length = v.length →
      (∀ i, i ≠ k → u.getD i false = v.getD i false) →
      ∀ i, i ≠ k →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) u).getD i false
        = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v).getD i false := by
  intro gs
  induction gs with
  | nil => intro _ u v _ h; exact h
  | cons g gs ih =>
    intro avoid u v hl h i hi
    have same : g.op.eval (g.inputs.map fun a => u.getD a false) =
        g.op.eval (g.inputs.map fun a => v.getD a false) := by
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h a (fun e => avoid g List.mem_cons_self (e ▸ ha))
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => avoid g' (List.mem_cons_of_mem _ hg'))
      _ _ (by simp [hl]) _ i hi
    intro j hj
    by_cases hju : j < u.length
    · rw [List.getD_append _ _ _ _ hju, List.getD_append _ _ _ _ (by omega)]
      exact h j hj
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      rw [same, hl]

def two (p m : Fin 42) : Fin 42 → Bool := fun i => decide (i = p) || decide (i = m)

def three (k p m : Fin 42) : Fin 42 → Bool := fun i => decide (i = k) || two p m i

theorem core (x4 : Circuit) (x1 : Fin 42) (x2 x3 : Fin 43) (k p : Fin 42) (hpk : p ≠ k)
    (hun : ∀ g ∈ x4.gates, (k : ℕ) ∉ g.inputs)
    (hf : ∀ a : Fin 42 → Bool, x4.eval (inp x1 x2 x3 a) = true ↔ F a)
    (hor : ∀ a b : Fin 42 → Bool, (∀ i, i ≠ k → a i = b i) → a p = true → b p = true →
      (a 0 || a x1) = (b 0 || b x1) ∧
      (Fin.lastCases (a 0 || a x1) a x2 || Fin.lastCases (a 0 || a x1) a x3) =
      (Fin.lastCases (b 0 || b x1) b x2 || Fin.lastCases (b 0 || b x1) b x3)) : False := by
  by_cases hout : x4.output = (k : ℕ)
  · have h1 : x4.eval (inp x1 x2 x3 (fun i => decide (i = k))) = true := by
      unfold Circuit.eval Circuit.wires
      rw [hout, fold_prefix _ _ _ (by rw [inp_len]; omega), getD_inp]
      simp
    obtain ⟨i, j, hij, hi, hj⟩ := (hf _).1 h1
    simp only [decide_eq_true_eq] at hi hj
    subst hi
    subst hj
    obtain ⟨h1', h2', _⟩ := hij
    omega
  · obtain ⟨m, hm1, hm2, hm3⟩ := pick k p (Ne.symm hpk)
    have hab : ∀ i, i ≠ k → three k p m i = two p m i := by
      intro i hi
      simp [three, hi]
    have hap : three k p m p = true := by simp [three, two]
    have hbp : two p m p = true := by simp [two]
    obtain ⟨h42, h43⟩ := hor _ _ hab hap hbp
    have heq : x4.eval (inp x1 x2 x3 (three k p m)) = x4.eval (inp x1 x2 x3 (two p m)) := by
      unfold Circuit.eval Circuit.wires
      exact fold_agree k x4.gates hun _ _ (by rw [inp_len, inp_len])
        (inp_agree x1 x2 x3 _ _ k hab h42 h43) _ hout
    have fa : F (three k p m) := by
      rcases hm1 with h | h
      · exact ⟨k, m, h, by simp [three], by simp [three, two]⟩
      · exact ⟨m, k, h, by simp [three, two], by simp [three]⟩
    have fb : ¬ F (two p m) := by
      rintro ⟨i, j, hij, hi, hj⟩
      simp only [two, Bool.or_eq_true, decide_eq_true_eq] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · obtain ⟨h1, h2, _⟩ := hij
        omega
      · exact hm2 hij
      · exact hm3 hij
      · obtain ⟨h1, h2, _⟩ := hij
        omega
    have h3 := (hf _).2 fa
    rw [heq] at h3
    exact fb ((hf _).1 h3)

theorem count1 (a b c d k : ℕ) (h : List.count k [a, b, c, d] = 1) :
    (k = a ∧ k ≠ b ∧ k ≠ c ∧ k ≠ d) ∨ (k ≠ a ∧ k = b ∧ k ≠ c ∧ k ≠ d) ∨
    (k ≠ a ∧ k ≠ b ∧ k = c ∧ k ≠ d) ∨ (k ≠ a ∧ k ≠ b ∧ k ≠ c ∧ k = d) := by
  simp only [List.count_cons, List.count_nil, beq_iff_eq] at h
  split_ifs at h <;> omega

end PEqualNP.Outside.L_meta_5359

theorem PEqualNP.Outside.L_meta_5359 : ∀ (x1 : Fin (42 : ℕ)) (x2 x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = (1 : Fin (42 : ℕ)) ∨ x1 = (21 : Fin (42 : ℕ)) ∨ x1 = (22 : Fin (42 : ℕ)) →     x2 < x3 →       (x2, x3) ≠ ((0 : Fin (43 : ℕ)), x1.castSucc) →         (x3 = Fin.last (42 : ℕ) → x2 ≠ (0 : Fin (43 : ℕ)) ∧ x2 ≠ x1.castSucc) →           (∀ (x9 : Fin (42 : ℕ) → Bool),               have x10 : Fin (43 : ℕ) → Bool := fun (x10 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x9 (0 : Fin (42 : ℕ)) || x9 x1) x9 x10;               x4.eval (List.ofFn fun (x11 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x10 x2 || x10 x3) x10 x11) = Bool.true ↔ ∃ (x11 : Fin (42 : ℕ)) (x12 : Fin (42 : ℕ)), (↑x11 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x12 ∧ (↑x12 + (21 : ℕ) - ↑x11) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x9 x11 = Bool.true ∧ x9 x12 = Bool.true) →             ∀ (x10 : Fin (42 : ℕ)), List.count ↑x10 [(0 : ℕ), ↑x1, ↑x2, ↑x3] = (1 : ℕ) → ∃ x12 ∈ x4.gates, ↑x10 ∈ x12.inputs := by
  intro x1 x2 x3 x4 _ h23 _ _ hf k hk
  by_contra hno
  have hun : ∀ g ∈ x4.gates, (k : ℕ) ∉ g.inputs := fun g hg hin => hno ⟨g, hg, hin⟩
  have hf' : ∀ a : Fin 42 → Bool, x4.eval (PEqualNP.Outside.L_meta_5359.inp x1 x2 x3 a) = true ↔
      PEqualNP.Outside.L_meta_5359.F a := fun a => hf a
  have hx2 : (x2 : ℕ) < 42 := by
    have := x3.isLt
    have : (x2 : ℕ) < x3 := h23
    omega
  obtain ⟨j2, rfl⟩ : ∃ j2 : Fin 42, x2 = j2.castSucc := ⟨⟨x2, hx2⟩, Fin.ext rfl⟩
  have hk42 := k.isLt
  simp only [Fin.val_castSucc] at hk
  have n0 : ∀ h : (k : ℕ) ≠ 0, (0 : Fin 42) ≠ k := fun h e => h (by rw [← e]; rfl)
  rcases PEqualNP.Outside.L_meta_5359.count1 _ _ _ _ _ hk with
    ⟨e0, e1, e2, e3⟩ | ⟨e0, e1, e2, e3⟩ | ⟨e0, e1, e2, e3⟩ | ⟨e0, e1, e2, e3⟩
  · -- k = 0, partner x1
    have n1 : x1 ≠ k := fun h => e1 (by rw [h])
    have n2 : j2 ≠ k := fun h => e2 (by rw [h])
    cases x3 using Fin.lastCases with
    | last =>
      refine PEqualNP.Outside.L_meta_5359.core x4 x1 _ _ k x1 n1 hun hf' ?_
      intro a b hab hap hbp
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      rw [hap, hbp]
      simp
    | cast j3 =>
      simp only [Fin.val_castSucc] at e3
      have n3 : j3 ≠ k := fun h => e3 (by rw [h])
      refine PEqualNP.Outside.L_meta_5359.core x4 x1 _ _ k x1 n1 hun hf' ?_
      intro a b hab hap hbp
      simp only [Fin.lastCases_castSucc]
      rw [hap, hbp, hab j2 n2, hab j3 n3]
      simp
  · -- k = x1, partner 0
    have n2 : j2 ≠ k := fun h => e2 (by rw [h])
    cases x3 using Fin.lastCases with
    | last =>
      refine PEqualNP.Outside.L_meta_5359.core x4 x1 _ _ k 0 (n0 e0) hun hf' ?_
      intro a b hab hap hbp
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      rw [hap, hbp]
      simp
    | cast j3 =>
      simp only [Fin.val_castSucc] at e3
      have n3 : j3 ≠ k := fun h => e3 (by rw [h])
      refine PEqualNP.Outside.L_meta_5359.core x4 x1 _ _ k 0 (n0 e0) hun hf' ?_
      intro a b hab hap hbp
      simp only [Fin.lastCases_castSucc]
      rw [hap, hbp, hab j2 n2, hab j3 n3]
      simp
  · -- k = j2
    have n1 : x1 ≠ k := fun h => e1 (by rw [h])
    cases x3 using Fin.lastCases with
    | last =>
      refine PEqualNP.Outside.L_meta_5359.core x4 x1 _ _ k 0 (n0 e0) hun hf' ?_
      intro a b hab hap hbp
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      rw [hap, hbp]
      simp
    | cast j3 =>
      simp only [Fin.val_castSucc] at e3
      have n3 : j3 ≠ k := fun h => e3 (by rw [h])
      refine PEqualNP.Outside.L_meta_5359.core x4 x1 _ _ k j3 n3 hun hf' ?_
      intro a b hab hap hbp
      simp only [Fin.lastCases_castSucc]
      rw [hap, hbp, hab 0 (n0 e0), hab x1 n1]
      simp
  · -- k = x3
    have n1 : x1 ≠ k := fun h => e1 (by rw [h])
    have n2 : j2 ≠ k := fun h => e2 (by rw [h])
    cases x3 using Fin.lastCases with
    | last =>
      simp only [Fin.val_last] at e3
      omega
    | cast j3 =>
      refine PEqualNP.Outside.L_meta_5359.core x4 x1 _ _ k j2 n2 hun hf' ?_
      intro a b hab hap hbp
      simp only [Fin.lastCases_castSucc]
      rw [hap, hbp, hab 0 (n0 e0), hab x1 n1]
      simp
