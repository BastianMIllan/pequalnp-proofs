import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7314

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Put the supplied negation in front as a NOT gate; either a gate is spare
-- (fewer than 18 gates, or an unused last gate) or a NOT of the negation is bypassed.
set_option maxHeartbeats 2000000 in
theorem general (f : (Fin 10 → Bool) → Bool) (htrue : f (fun _ => true) = true) :
    ∀ (D : Circuit), FanInTwo D → D.size ≤ 18 →
      (∀ (x5 : Fin 10 → Bool), D.eval (List.ofFn x5 ++ [!x5 0]) = f x5) →
      (D.size < 18 ∨ D.output ≠ 28 ∨ ∃ (x6 : Fin D.size), (D.gates.get x6).op = GateOp.not ∧
        (D.gates.get x6).inputs.head? = some 10) → HasCircuitSize 10 f 18 := by
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run := fun (gs : List Gate) (w : List Bool) => gs.foldl step w
  have run_len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [run]
    | cons g gs ih =>
      change (run gs (step w g)).length = _
      rw [ih]
      simp [step]
      omega
  have run_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (step w g)).getD i false = _
      rw [ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have map_value (r : ℕ → ℕ) (g : Gate) (w v : List Bool)
      (h : ∀ i, w.getD i false = v.getD (r i) false) :
      g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval (((g.inputs.map r).map fun i => v.getD i false)) := by
    rw [List.map_map]
    apply congrArg g.op.eval
    apply List.map_congr_left
    intro i _
    exact h i
  have simulate_gap (k : ℕ) (hk : 0 < k) :
      let r := fun i : ℕ => if i = k then 0 else if k < i then i - 1 else i
      let mapped := fun g : Gate => Gate.mk g.op (g.inputs.map r)
      ∀ (gs : List Gate) (w v : List Bool),
        k ≤ v.length → w.length = v.length + 1 →
        (∀ i, w.getD i false = v.getD (r i) false) →
        ∀ i, (run gs w).getD i false = (run (gs.map mapped) v).getD (r i) false := by
    dsimp only
    let r := fun i : ℕ => if i = k then 0 else if k < i then i - 1 else i
    let mapped := fun g : Gate => Gate.mk g.op (g.inputs.map r)
    change ∀ (gs : List Gate) (w v : List Bool), k ≤ v.length → w.length = v.length + 1 →
      (∀ i, w.getD i false = v.getD (r i) false) →
      ∀ i, (run gs w).getD i false = (run (gs.map mapped) v).getD (r i) false
    intro gs
    induction gs with
    | nil => intro w v _ _ h; exact h
    | cons g gs ih =>
      intro w v hkv hl hlook i
      change (run gs (step w g)).getD i false =
        (run (gs.map mapped) (step v (mapped g))).getD (r i) false
      apply ih _ _ (by simp [step]; omega)
      · simp [step, hl]
      · let b := g.op.eval (g.inputs.map fun u => w.getD u false)
        have hg : step v (mapped g) = v ++ [b] := by
          change v ++ [g.op.eval ((g.inputs.map r).map fun i => v.getD i false)] = _
          rw [← map_value r g w v hlook]
        intro j
        change (w ++ [b]).getD j false = (step v (mapped g)).getD (r j) false
        rw [hg]
        by_cases hj : j < w.length
        · have hmap : r j < v.length := by
            dsimp only [r]
            split_ifs <;> omega
          rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ hmap]
          exact hlook j
        · have hkj : k < j := by omega
          have hr : r j = j - 1 := by simp [r, hkj, show j ≠ k by omega]
          rw [hr, List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega)]
          congr 1
          omega
  have reroute (D : Circuit) (hD : FanInTwo D) (hsize : D.size ≤ 18)
      (a : Gate) (ha : a ∈ D.gates) (hao : a.op = .not) (hai : a.inputs.head? = some 10)
      (f : (Fin 10 → Bool) → Bool)
      (hEval : ∀ x, D.eval (List.ofFn x ++ [!x 0]) = f x) :
      HasCircuitSize 10 f 18 := by
    obtain ⟨pre, post, hgs⟩ := List.append_of_mem ha
    let k := 11 + pre.length
    let r := fun i : ℕ => if i = k then 0 else if k < i then i - 1 else i
    let mapped := fun g : Gate => Gate.mk g.op (g.inputs.map r)
    let first : Gate := ⟨.not, [0]⟩
    refine ⟨⟨first :: pre ++ post.map mapped, r D.output⟩, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ first :: pre ++ post.map mapped at hg
      rcases List.mem_cons.mp hg with he | hg
      · subst g
        simp [first]
      · rcases List.mem_append.mp hg with hp | hp
        · exact hD g (by rw [hgs]; simp [hp])
        · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hp
          have horig := hD g₀ (by rw [hgs]; simp [hg₀])
          simpa [mapped] using horig
    · change (first :: pre ++ post.map mapped).length ≤ 18
      change D.gates.length ≤ 18 at hsize
      rw [hgs] at hsize
      simp at hsize ⊢
      omega
    · intro x
      let seed := List.ofFn x ++ [!x 0]
      have hseedLen : seed.length = 11 := by simp [seed]
      have hFirst : step (List.ofFn x) first = seed := by
        simp only [step, first, List.map_cons, List.map_nil, seed]
        change List.ofFn x ++ [!((List.ofFn x).getD 0 false)] = _
        simp [List.getD_eq_getElem?_getD]
      let v := run pre seed
      have hvLen : v.length = k := by simp [v, run_len, hseedLen, k]
      have hv0 : v.getD 0 false = x 0 := by
        rw [run_preserves pre seed 0 (by omega)]
        simp [seed, List.getD_eq_getElem?_getD]
      have hv10 : v.getD 10 false = !x 0 := by
        rw [run_preserves pre seed 10 (by omega)]
        simp [seed, List.getD_eq_getElem?_getD]
      have haStep : step v a = v ++ [x 0] := by
        have haHead : ∃ tail, a.inputs = 10 :: tail := by
          cases h : a.inputs with
          | nil => rw [h] at hai; cases hai
          | cons u tail =>
            rw [h, List.head?_cons, Option.some.injEq] at hai
            exact ⟨tail, by rw [hai]⟩
        obtain ⟨tail, htail⟩ := haHead
        simp only [step, hao, htail, List.map_cons]
        change v ++ [!v.getD 10 false] = _
        rw [hv10, Bool.not_not]
      have hLook (i : ℕ) : (v ++ [x 0]).getD i false = v.getD (r i) false := by
        obtain h | h | h := lt_trichotomy i k
        · rw [List.getD_append _ _ _ _ (by omega)]
          simp [r, show i ≠ k by omega, show ¬ k < i by omega]
        · subst i
          have hAt : (v ++ [x 0]).getD k false = x 0 := by
            rw [← hvLen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
            rfl
          rw [hAt]
          rw [show r k = 0 by simp [r]]
          exact hv0.symm
        · have hi : i ≠ k := by omega
          have hil : v.length + 1 ≤ i := by omega
          have hir : v.length ≤ i - 1 := by omega
          rw [List.getD_eq_default _ _ (by simpa using hil)]
          rw [show r i = i - 1 by simp [r, hi, h]]
          exact (List.getD_eq_default _ _ hir).symm
      have hs := simulate_gap k (by dsimp [k]; omega) post (v ++ [x 0]) v
        hvLen.ge (by simp) hLook D.output
      have hNew : (Circuit.mk (first :: pre ++ post.map mapped) (r D.output)).eval (List.ofFn x) =
          (run (post.map mapped) v).getD (r D.output) false := by
        change ((pre ++ post.map mapped).foldl step (step (List.ofFn x) first)).getD _ false = _
        rw [hFirst, List.foldl_append]
      have hOld : D.eval seed = (run post (v ++ [x 0])).getD D.output false := by
        change (D.gates.foldl step seed).getD D.output false = _
        rw [hgs, List.foldl_append, List.foldl_cons]
        change (run post (step v a)).getD D.output false = _
        rw [haStep]
      rw [hNew, ← hs, ← hOld]
      exact hEval x
  intro D hD hsize hEval hcase
  let first : Gate := ⟨.not, [0]⟩
  have hFirst (x : Fin 10 → Bool) : step (List.ofFn x) first = List.ofFn x ++ [!x 0] := by
    simp only [step, first, List.map_cons, List.map_nil]
    change List.ofFn x ++ [!((List.ofFn x).getD 0 false)] = _
    simp [List.getD_eq_getElem?_getD]
  have prepend (hlt : D.size < 18) : HasCircuitSize 10 f 18 := by
    refine ⟨⟨first :: D.gates, D.output⟩, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ first :: D.gates at hg
      rcases List.mem_cons.mp hg with he | hg
      · subst g
        simp [first]
      · exact hD g hg
    · change (first :: D.gates).length ≤ 18
      change D.gates.length < 18 at hlt
      simp
      omega
    · intro x
      change (D.gates.foldl step (step (List.ofFn x) first)).getD D.output false = f x
      rw [hFirst x]
      exact hEval x
  rcases hcase with hlt | hout | ⟨j, hjop, hjin⟩
  · exact prepend hlt
  · by_cases hlt : D.size < 18
    · exact prepend hlt
    · have h18 : D.gates.length = 18 := by
        change D.gates.length ≤ 18 at hsize
        change ¬ D.gates.length < 18 at hlt
        omega
      have hne : D.gates ≠ [] := by
        intro h
        rw [h] at h18
        simp at h18
      obtain ⟨pre, last, hgs⟩ : ∃ pre last, D.gates = pre ++ [last] :=
        ⟨D.gates.dropLast, D.gates.getLast hne, (List.dropLast_append_getLast hne).symm⟩
      have hpre : pre.length = 17 := by
        have := congrArg List.length hgs
        simp at this
        omega
      by_cases hgt : 28 < D.output
      · exfalso
        have he := hEval (fun _ => true)
        rw [htrue] at he
        have hz : D.eval (List.ofFn (fun _ : Fin 10 => true) ++ [!true]) = false := by
          change (run D.gates (List.ofFn (fun _ : Fin 10 => true) ++ [!true])).getD
            D.output false = false
          apply List.getD_eq_default
          rw [run_len]
          simp
          omega
        rw [hz] at he
        exact Bool.noConfusion he
      · have hlt28 : D.output < 28 := by omega
        refine ⟨⟨first :: pre, D.output⟩, ?_, ?_, ?_⟩
        · intro g hg
          change g ∈ first :: pre at hg
          rcases List.mem_cons.mp hg with he | hg
          · subst g
            simp [first]
          · exact hD g (by rw [hgs]; simp [hg])
        · change (first :: pre).length ≤ 18
          simp
          omega
        · intro x
          change (pre.foldl step (step (List.ofFn x) first)).getD D.output false = f x
          rw [hFirst x, ← hEval x]
          change _ = (D.gates.foldl step (List.ofFn x ++ [!x 0])).getD D.output false
          rw [hgs, List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil]
          change _ = (run pre (List.ofFn x ++ [!x 0]) ++ [_]).getD D.output false
          rw [List.getD_append _ _ _ _ (by rw [run_len]; simp; omega)]
  · exact reroute D hD hsize (D.gates.get j) (List.mem_iff_get.mpr ⟨j, rfl⟩) hjop hjin f hEval

end PEqualNP.Outside.L_meta_7314

theorem PEqualNP.Outside.L_meta_7314 : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (18 : ℕ) → (∀ (x5 : Fin (10 : ℕ) → Bool), x2.eval (List.ofFn x5 ++ [!x5 (0 : Fin (10 : ℕ))]) = x1 x5) → (x2.size < (18 : ℕ) ∨ x2.output ≠ (28 : ℕ) ∨ ∃ (x6 : Fin x2.size), (x2.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x2.gates.get x6).inputs.head? = Option.some (10 : ℕ)) → PEqualNP.MetaComplexity.HasCircuitSize (10 : ℕ) x1 (18 : ℕ) := by
  intro x1
  exact PEqualNP.Outside.L_meta_7314.general x1 (by decide)
