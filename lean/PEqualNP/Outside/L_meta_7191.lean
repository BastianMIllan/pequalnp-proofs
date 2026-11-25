import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7191

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

def substWire (k a i : ℕ) : ℕ :=
  if i < k then i else if i = k then a else i - 1

def substGate (k a : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (substWire k a)⟩

def deleteGate (m : ℕ) (C : Circuit) (j a : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a),
    substWire (m + j) a C.output⟩

lemma deleteGate_len (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length) :
    (deleteGate m C j a).gates.length = C.gates.length - 1 := by
  simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

lemma deleteGate_gateAt (m : ℕ) (C : Circuit) (j a s : ℕ) (hj : j < C.gates.length)
    (hs : s < j) :
    PEqualNP.MetaComplexity.NestedCover.gateAt (deleteGate m C j a) s =
      PEqualNP.MetaComplexity.NestedCover.gateAt C s := by
  simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, deleteGate, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega)]
  simp [hs]

lemma deleteGate_mono (m : ℕ) (C : Circuit) (j a : ℕ) (hC : Monotone2 C) :
    Monotone2 (deleteGate m C j a) := by
  intro g hg
  rcases List.mem_append.1 hg with h1 | h1
  · exact hC g (List.mem_of_mem_take h1)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
    have := hC g0 (List.mem_of_mem_drop hg0)
    simpa [substGate] using this

lemma subst_aux (k a : ℕ) :
    ∀ (gs : List Gate) (w₁ w₂ : List Bool),
      w₁.length = w₂.length + 1 → k < w₁.length → w₂.length + gs.length + 1 ≤ a →
      w₁.getD k false = false →
      (∀ i < w₁.length, i ≠ k → w₂.getD (substWire k a i) false = w₁.getD i false) →
      ∀ i < (wiresFrom gs w₁).length, i ≠ k →
        (wiresFrom (gs.map (substGate k a)) w₂).getD (substWire k a i) false =
          (wiresFrom gs w₁).getD i false := by
  intro gs
  induction gs with
  | nil =>
    intro w₁ w₂ _ _ _ _ hag i hi hne
    exact hag i hi hne
  | cons g rest ih =>
    intro w₁ w₂ hlen hk ha hkf hag
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
    have hmap : ((substGate k a g).inputs.map fun i => w₂.getD i false) =
        (g.inputs.map fun i => w₁.getD i false) := by
      simp only [substGate, List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      by_cases hik : i = k
      · subst hik
        have hs : substWire i a i = a := by simp [substWire]
        rw [hs, hkf, List.getD_eq_default _ _ (by simp at ha; omega)]
      · by_cases hi : i < w₁.length
        · exact hag i hi hik
        · have hge : w₂.length ≤ substWire k a i := by
            unfold substWire
            split_ifs <;> omega
          rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
    rw [hmap]
    apply ih _ _ (by simp [hlen]) (by simp; omega) (by simp at ha ⊢; omega)
      (by rw [getD_snoc_lt _ _ _ _ hk]; exact hkf)
    intro i hi hne
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < w₁.length
    · have hsublt : substWire k a i < w₂.length := by
        unfold substWire
        split_ifs <;> omega
      rw [getD_snoc_lt _ _ _ _ hsublt, getD_snoc_lt _ _ _ _ hlt]
      exact hag i hlt hne
    · have hieq : i = w₁.length := by omega
      have hsubeq : substWire k a i = w₂.length := by
        unfold substWire
        split_ifs <;> omega
      rw [getD_snoc_eq _ _ _ _ hsubeq, getD_snoc_eq _ _ _ _ hieq]
      rfl

lemma del_one (m : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hc : PEqualNP.MetaComplexity.NestedCover.gateAt C j = PEqualNP.NotPremium.constGate false) :
    circuitFun m (deleteGate m C j (m + C.gates.length)) = circuitFun m C := by
  set a := m + C.gates.length with ha
  funext x
  have hgj : C.gates[j] = ⟨GateOp.or, []⟩ := by
    have : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
    rw [← this, hc]
    rfl
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  show (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a))
      (List.ofFn x)).getD (substWire (m + j) a C.output) false =
    (wiresFrom C.gates (List.ofFn x)).getD C.output false
  set w₂ := wiresFrom (C.gates.take j) (List.ofFn x) with hw₂
  set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
  have hw₂_len : w₂.length = m + j := by
    rw [hw₂, wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
  have hw₁_eq : w₁ = w₂ ++ [false] := by
    rw [hw₁, wiresFrom_cons, wiresFrom_nil, hgj]
    rfl
  have hw₁_len : w₁.length = m + j + 1 := by
    rw [hw₁_eq]; simp [hw₂_len]
  have hkf : w₁.getD (m + j) false = false := by
    rw [hw₁_eq, getD_snoc_eq _ _ _ _ hw₂_len.symm]
  rw [wiresFrom_append, ← hw₂]
  conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
  have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = m + C.gates.length := by
    rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
  have hlen_lhs : (wiresFrom ((C.gates.drop (j + 1)).map (substGate (m + j) a)) w₂).length =
      m + C.gates.length - 1 := by
    rw [wiresFrom_length, hw₂_len, List.length_map, List.length_drop]; omega
  by_cases hout : C.output = m + j
  · rw [hout]
    have hs : substWire (m + j) a (m + j) = a := by simp [substWire]
    rw [hs, List.getD_eq_default _ _ (by omega), wiresFrom_getD_lt _ _ _ (by omega), hkf]
  · by_cases hlt : C.output < m + C.gates.length
    · apply subst_aux (m + j) a (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega)
        (by rw [List.length_drop]; omega) hkf _ C.output (by omega) hout
      intro i hi hne
      have hlt' : i < m + j := by omega
      simp only [substWire, hlt', ↓reduceIte]
      rw [hw₁_eq, getD_snoc_lt _ _ _ _ (by omega)]
    · have hge : m + C.gates.length - 1 ≤ substWire (m + j) a C.output := by
        unfold substWire
        split_ifs <;> omega
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

lemma main_ind (m : ℕ) : ∀ (n : ℕ) (C : Circuit) (S : Finset ℕ), S.card = n → Monotone2 C →
    S ⊆ Finset.range C.size →
    (∀ s ∈ S, PEqualNP.MetaComplexity.NestedCover.gateAt C s =
      PEqualNP.NotPremium.constGate false) →
    ∃ D : Circuit, Monotone2 D ∧ D.size + S.card ≤ C.size ∧ circuitFun m D = circuitFun m C := by
  intro n
  induction n with
  | zero =>
    intro C S hS hC _ _
    exact ⟨C, hC, by rw [hS]; omega, rfl⟩
  | succ n ih =>
    intro C S hS hC hsub hconst
    have hne : S.Nonempty := by
      rw [← Finset.card_pos, hS]; omega
    set j := S.max' hne with hjdef
    have hjS : j ∈ S := Finset.max'_mem S hne
    have hjlt : j < C.gates.length := by
      have := hsub hjS
      simpa [Circuit.size] using this
    set D1 := deleteGate m C j (m + C.gates.length) with hD1
    have hD1len : D1.gates.length = C.gates.length - 1 := deleteGate_len m C j _ hjlt
    have hlt_of : ∀ s ∈ S.erase j, s < j := by
      intro s hs
      have h1 := Finset.ne_of_mem_erase hs
      have h2 := Finset.le_max' S s (Finset.mem_of_mem_erase hs)
      rw [← hjdef] at h2
      omega
    obtain ⟨D, hD, hDs, hDf⟩ := ih D1 (S.erase j)
      (by rw [Finset.card_erase_of_mem hjS, hS]; rfl)
      (deleteGate_mono m C j _ hC)
      (by
        intro s hs
        have := hlt_of s hs
        simp only [Finset.mem_range, Circuit.size]
        omega)
      (by
        intro s hs
        rw [hD1, deleteGate_gateAt m C j _ s hjlt (hlt_of s hs)]
        exact hconst s (Finset.mem_of_mem_erase hs))
    refine ⟨D, hD, ?_, ?_⟩
    · have h1 := Finset.card_erase_of_mem hjS
      have h2 : D1.size = C.size - 1 := by simpa [Circuit.size] using hD1len
      have h3 : 0 < S.card := by rw [hS]; omega
      have h4 : C.size ≥ 1 := by simp only [Circuit.size]; omega
      omega
    · rw [hDf, hD1]
      exact del_one m C j hjlt (hconst j hjS)

end PEqualNP.Outside.L_meta_7191

theorem PEqualNP.Outside.L_meta_7191 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 x2 → x3 ⊆ Finset.range x2.size → (∀ x6 ∈ x3, PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6 = PEqualNP.NotPremium.constGate Bool.false) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.size + x3.card ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 := by
  intro x1 x2 x3 hC hsub hconst
  exact PEqualNP.Outside.L_meta_7191.main_ind x1 x3.card x2 x3 rfl hC hsub hconst
