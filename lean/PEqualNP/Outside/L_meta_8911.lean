import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8911

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma foldl_append_spec {α β : Type} (f : List α → β → α) :
    ∀ (l : List β) (acc : List α),
      (l.foldl (fun w b => w ++ [f w b]) acc).length = acc.length + l.length ∧
      (∀ i < acc.length, (l.foldl (fun w b => w ++ [f w b]) acc)[i]? = acc[i]?) ∧
      (∀ (j : ℕ) (b : β), l[j]? = some b →
        (l.foldl (fun w b => w ++ [f w b]) acc)[acc.length + j]? =
          some (f ((l.take j).foldl (fun w x => w ++ [f w x]) acc) b)) := by
  intro l
  induction l with
  | nil =>
    intro acc
    refine ⟨by simp, fun i _ => rfl, fun j b h => by simp at h⟩
  | cons a t ih =>
    intro acc
    have h1 := ih (acc ++ [f acc a])
    refine ⟨?_, ?_, ?_⟩
    · rw [List.foldl_cons, h1.1, List.length_append, List.length_singleton, List.length_cons]
      omega
    · intro i hi
      simp only [List.foldl_cons]
      have hi' : i < (acc ++ [f acc a]).length := by simp; omega
      rw [h1.2.1 i hi', List.getElem?_append_left hi]
    · intro j b hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        simp only [List.foldl_cons, Nat.add_zero, List.take_zero, List.foldl_nil]
        have hi' : acc.length < (acc ++ [f acc a]).length := by simp
        rw [h1.2.1 acc.length hi', List.getElem?_append_right (le_refl _)]
        simp
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        simp only [List.foldl_cons, List.take_succ_cons]
        have hstep := h1.2.2 j' b hj
        simp only [List.length_append, List.length_singleton] at hstep
        have heq : acc.length + (j' + 1) = acc.length + 1 + j' := by omega
        rw [heq]
        exact hstep

lemma foldl_append_take_getD {α β : Type} (f : List α → β → α) (d : α)
    (l : List β) (acc : List α) (k i : ℕ) (hi : i < acc.length + k) (hk : k ≤ l.length) :
    ((l.take k).foldl (fun w x => w ++ [f w x]) acc).getD i d =
      (l.foldl (fun w x => w ++ [f w x]) acc).getD i d := by
  have hsplit : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hlen : ((l.take k).foldl (fun w x => w ++ [f w x]) acc).length = acc.length + k := by
    rw [(foldl_append_spec f (l.take k) acc).1, List.length_take, Nat.min_eq_left hk]
  have hget := (foldl_append_spec f (l.drop k)
    ((l.take k).foldl (fun w x => w ++ [f w x]) acc)).2.1 i (by omega)
  simp only [List.getD_eq_getElem?_getD, hget]

lemma foldl_append_take_getD_out {α β : Type} (f : List α → β → α) (d : α)
    (l : List β) (acc : List α) (k i : ℕ) (hi : acc.length + k ≤ i) (hk : k ≤ l.length) :
    ((l.take k).foldl (fun w x => w ++ [f w x]) acc).getD i d = d := by
  have hlen : ((l.take k).foldl (fun w x => w ++ [f w x]) acc).length = acc.length + k := by
    rw [(foldl_append_spec f (l.take k) acc).1, List.length_take, Nat.min_eq_left hk]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact (foldl_append_spec (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false))
    C.gates x).1

lemma wires_getD_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  unfold Circuit.wires
  have hget := (foldl_append_spec (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false))
    C.gates x).2.1 i hi
  rw [List.getD_eq_getElem?_getD, hget, List.getD_eq_getElem?_getD]

lemma gate_val (C : Circuit) (y : List Bool) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) :
    (C.wires y).getD (y.length + j) false =
      g.op.eval (g.inputs.map fun k =>
        if k < y.length + j then (C.wires y).getD k false else false) := by
  have hj : j < C.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hg
    exact absurd hg (by simp)
  have hstep := (foldl_append_spec (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false))
    C.gates y).2.2 j g hg
  have hfull : ∀ k, k < y.length + j → (C.wires y).getD k false =
      ((C.gates.take j).foldl (fun w x => w ++
        [(fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) w x]) y).getD k false := by
    intro k hk
    unfold Circuit.wires
    exact (foldl_append_take_getD (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false))
      false C.gates y j k hk (le_of_lt hj)).symm
  have hout : ∀ k, ¬ k < y.length + j → false =
      ((C.gates.take j).foldl (fun w x => w ++
        [(fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) w x]) y).getD k false := by
    intro k hk
    exact (foldl_append_take_getD_out (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false))
      false C.gates y j k (by omega) (le_of_lt hj)).symm
  have hmap : (g.inputs.map fun k =>
        if k < y.length + j then (C.wires y).getD k false else false) =
      g.inputs.map fun k => ((C.gates.take j).foldl (fun w x => w ++
        [(fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) w x]) y).getD k false := by
    apply List.map_congr_left
    intro k _
    split_ifs with hk
    · exact hfull k hk
    · exact hout k hk
  rw [hmap]
  unfold Circuit.wires
  rw [List.getD_eq_getElem?_getD, hstep, Option.getD_some]

def W (m n : ℕ) (x3 : Fin m → Fin n → Bool) (C : Circuit) (i : ℕ) : Set (Fin m) :=
  {p | (C.wires (List.ofFn (x3 p))).getD i false = true}

def F (m n : ℕ) (x3 : Fin m → Fin n → Bool) : Set (Set (Fin m)) :=
  {∅, Set.univ} ∪ Set.range fun (j : Fin n) => {p : Fin m | x3 p j = true}

lemma hin (m n : ℕ) (x3 : Fin m → Fin n → Bool) (C : Circuit) (i : ℕ) (hi : i < n) :
    W m n x3 C i ∈ F m n x3 := by
  refine Or.inr ⟨⟨i, hi⟩, ?_⟩
  ext p
  simp only [W, Set.mem_setOf_eq]
  rw [wires_getD_input C _ i (by simp [hi])]
  simp [List.getD_eq_getElem?_getD, hi]

lemma hbig (m n : ℕ) (x3 : Fin m → Fin n → Bool) (C : Circuit) (i : ℕ)
    (hi : n + C.gates.length ≤ i) : W m n x3 C i = ∅ := by
  ext p
  simp only [W, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by rw [wires_length, List.length_ofFn]; omega)]
  simp

lemma gate_comb (m n : ℕ) (x3 : Fin m → Fin n → Bool) (C : Circuit) (hM : Monotone2 C)
    (k : ℕ) (hk : k < C.gates.length) (T : Set (Set (Fin m))) (hF : F m n x3 ⊆ T)
    (hT : ∀ i < n + k, W m n x3 C i ∈ T) :
    ∃ A ∈ T, ∃ B ∈ T, W m n x3 C (n + k) = A ∪ B ∨ W m n x3 C (n + k) = A ∩ B := by
  obtain ⟨g, hget⟩ : ∃ g, C.gates[k]? = some g := ⟨_, List.getElem?_eq_getElem hk⟩
  have hmem : g ∈ C.gates := List.mem_of_getElem? hget
  obtain ⟨hop, hlen⟩ := hM g hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have hempty : (∅ : Set (Fin m)) ∈ T := hF (Or.inl (by simp))
  have huniv : (Set.univ : Set (Fin m)) ∈ T := hF (Or.inl (by simp))
  have hV : ∀ a, {p : Fin m |
      (if a < n + k then (C.wires (List.ofFn (x3 p))).getD a false else false) = true} ∈ T := by
    intro a
    by_cases ha : a < n + k
    · have h := hT a ha
      simpa [W, ha] using h
    · have he : {p : Fin m |
          (if a < n + k then (C.wires (List.ofFn (x3 p))).getD a false else false) = true} = ∅ := by
        ext p
        simp [ha]
      rw [he]
      exact hempty
  have hval : ∀ p : Fin m, (C.wires (List.ofFn (x3 p))).getD (n + k) false =
      g.op.eval (g.inputs.map fun a =>
        if a < n + k then (C.wires (List.ofFn (x3 p))).getD a false else false) := by
    intro p
    have h := gate_val C (List.ofFn (x3 p)) k g hget
    rw [List.length_ofFn] at h
    exact h
  rcases hinp : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rcases hop with hop | hop
    · refine ⟨Set.univ, huniv, Set.univ, huniv, Or.inl ?_⟩
      rw [Set.union_self]
      ext p
      simp only [W, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rw [hval p, hinp, hop]
      simp [GateOp.eval]
    · refine ⟨∅, hempty, ∅, hempty, Or.inl ?_⟩
      rw [Set.union_self]
      ext p
      simp only [W, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rw [hval p, hinp, hop]
      simp [GateOp.eval]
  · refine ⟨_, hV a, _, hV a, Or.inl ?_⟩
    rw [Set.union_self]
    ext p
    simp only [W, Set.mem_setOf_eq]
    rw [hval p, hinp]
    rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
  · refine ⟨_, hV a, _, hV b, ?_⟩
    rcases hop with hop | hop
    · right
      ext p
      simp only [W, Set.mem_setOf_eq, Set.mem_inter_iff]
      rw [hval p, hinp, hop]
      simp [GateOp.eval]
    · left
      ext p
      simp only [W, Set.mem_setOf_eq, Set.mem_union]
      rw [hval p, hinp, hop]
      simp [GateOp.eval]
  · rw [hinp] at hlen
    simp at hlen

lemma build (m n : ℕ) (x3 : Fin m → Fin n → Bool) (C : Circuit) (hM : Monotone2 C) :
    ∀ k ≤ C.gates.length, ∃ L : List (Set (Fin m)), L.length ≤ k ∧
      (∀ i < L.length, L.getD i ∅ ∉ F m n x3 ∪ {s | s ∈ L.take i} ∧
        ∃ A ∈ F m n x3 ∪ {s | s ∈ L.take i}, ∃ B ∈ F m n x3 ∪ {s | s ∈ L.take i},
          L.getD i ∅ = A ∪ B ∨ L.getD i ∅ = A ∩ B) ∧
      ∀ i < n + k, W m n x3 C i ∈ F m n x3 ∪ {s | s ∈ L} := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[], by simp, by simp, fun i hi => Or.inl (hin m n x3 C i (by omega))⟩
  | succ k ih =>
    intro hk
    obtain ⟨L, hlen, hP, hW⟩ := ih (by omega)
    obtain ⟨A, hA, B, hB, hAB⟩ := gate_comb m n x3 C hM k (by omega) (F m n x3 ∪ {s | s ∈ L})
      Set.subset_union_left hW
    by_cases hs : W m n x3 C (n + k) ∈ F m n x3 ∪ {s | s ∈ L}
    · refine ⟨L, by omega, hP, fun i hi => ?_⟩
      by_cases hik : i < n + k
      · exact hW i hik
      · have hie : i = n + k := by omega
        rw [hie]
        exact hs
    · refine ⟨L ++ [W m n x3 C (n + k)], by simp; omega, ?_, ?_⟩
      · intro i hi
        rw [List.length_append, List.length_singleton] at hi
        by_cases hil : i < L.length
        · have h1 : (L ++ [W m n x3 C (n + k)]).take i = L.take i :=
            List.take_append_of_le_length hil.le
          have h2 : (L ++ [W m n x3 C (n + k)]).getD i ∅ = L.getD i ∅ := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hil]
          rw [h1, h2]
          exact hP i hil
        · have hie : i = L.length := by omega
          have h1 : (L ++ [W m n x3 C (n + k)]).take i = L := by
            rw [hie]
            simp
          have h2 : (L ++ [W m n x3 C (n + k)]).getD i ∅ = W m n x3 C (n + k) := by
            rw [hie]
            simp [List.getD_eq_getElem?_getD]
          rw [h1, h2]
          exact ⟨hs, A, hA, B, hB, hAB⟩
      · intro i hi
        by_cases hik : i < n + k
        · rcases hW i hik with h | h
          · exact Or.inl h
          · refine Or.inr ?_
            simp only [Set.mem_setOf_eq, List.mem_append] at h ⊢
            exact Or.inl h
        · have hie : i = n + k := by omega
          rw [hie]
          refine Or.inr ?_
          simp

lemma main (m n : ℕ) (x3 : Fin m → Fin n → Bool) (C : Circuit) (hM : Monotone2 C) :
    ∃ L : List (Set (Fin m)), L.length ≤ C.size ∧
      (∀ i : Fin L.length, L.getD i ∅ ∉ F m n x3 ∪ {s | s ∈ L.take i} ∧
        ∃ A ∈ F m n x3 ∪ {s | s ∈ L.take i}, ∃ B ∈ F m n x3 ∪ {s | s ∈ L.take i},
          L.getD i ∅ = A ∪ B ∨ L.getD i ∅ = A ∩ B) ∧
      {p : Fin m | circuitFun n C (x3 p) = true} ∈ F m n x3 ∪ {s | s ∈ L} := by
  obtain ⟨L, hlen, hP, hW⟩ := build m n x3 C hM C.gates.length le_rfl
  refine ⟨L, hlen, fun i => hP i.1 i.2, ?_⟩
  show W m n x3 C C.output ∈ F m n x3 ∪ {s | s ∈ L}
  by_cases ho : C.output < n + C.gates.length
  · exact hW _ ho
  · rw [hbig m n x3 C C.output (by omega)]
    exact Or.inl (Or.inl (by simp))

end PEqualNP.Outside.L_meta_8911

theorem PEqualNP.Outside.L_meta_8911 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Bool) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x4 →     have x6 : Set (Set (Fin x1)) := {∅, Set.univ} ∪ Set.range fun (x6 : Fin x2) => {x7 : Fin x1 | x3 x7 x6 = Bool.true};     ∃ (x7 : List (Set (Fin x1))),       x7.length ≤ x4.size ∧         (∀ (x8 : Fin x7.length),             have x9 : Set (Set (Fin x1)) := x6 ∪ {x9 : Set (Fin x1) | x9 ∈ List.take (↑x8) x7};             x7.getD ↑x8 ∅ ∉ x9 ∧ ∃ x10 ∈ x9, ∃ x11 ∈ x9, x7.getD ↑x8 ∅ = x10 ∪ x11 ∨ x7.getD ↑x8 ∅ = x10 ∩ x11) ∧           {x8 : Fin x1 | PEqualNP.MetaComplexity.circuitFun x2 x4 (x3 x8) = Bool.true} ∈ x6 ∪ {x8 : Set (Fin x1) | x8 ∈ x7} := by
  intro m n x3 C hM
  exact PEqualNP.Outside.L_meta_8911.main m n x3 C hM
