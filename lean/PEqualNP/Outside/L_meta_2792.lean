import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2792

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

lemma gateAt_some {C : Circuit} {k : ℕ} {g : Gate} (h : C.gates[k]? = some g) :
    gateAt C k = g := by
  simp [gateAt, List.getD_eq_getElem?_getD, h]

lemma wv_ge (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    wv n C x w = false := by
  unfold wv
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none
    (by rw [wires_eq, foldl_len, List.length_ofFn]; omega)]
  rfl

lemma wv_mono (n : ℕ) (C : Circuit) (hC : AOB n C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, wv n C x w = true → wv n C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hx
    rcases Nat.lt_or_ge w n with h | h
    · rw [wv_input n C x w h] at hx
      rw [wv_input n C y w h]
      exact hxy _ hx
    · rcases Nat.lt_or_ge w (n + C.gates.length) with h2 | h2
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [wv_rec n C x hC j hj] at hx
        rw [wv_rec n C y hC j hj]
        have hin : ∀ i ∈ (gateAt C j).inputs, wv n C x i = true → wv n C y i = true :=
          fun i hi => ih i ((hC j hj).2 i hi)
        rcases (hC j hj).1 with hop | hop
        · rw [hop] at hx ⊢
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply,
            id_eq] at hx ⊢
          intro i hi
          exact hin i hi (hx i hi)
        · rw [hop] at hx ⊢
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply,
            id_eq] at hx ⊢
          obtain ⟨i, hi, hv⟩ := hx
          exact ⟨i, hi, hin i hi hv⟩
      · rw [wv_ge n C x w h2] at hx
        exact absurd hx (by simp)

def S7 (n : ℕ) (C : Circuit) (w : ℕ) : Set ((Fin n → Bool) × (Fin n → Bool)) :=
  {p | wv (n + n) C (Fin.append p.1 p.2) w = true}

lemma mem_S7 {n : ℕ} {C : Circuit} {w : ℕ} {p : (Fin n → Bool) × (Fin n → Bool)} :
    p ∈ S7 n C w ↔ wv (n + n) C (Fin.append p.1 p.2) w = true := Iff.rfl

lemma split1 (n : ℕ) (C : Circuit) (a : Fin n → Bool) (c : Bool) (k : ℕ) :
    (C.wires (List.ofFn a ++ List.replicate n c)).getD k false =
      wv (n + n) C (Fin.append a (fun _ => c)) k := by
  unfold wv
  rw [List.ofFn_fin_append, List.ofFn_const]

lemma split2 (n : ℕ) (C : Circuit) (b : Fin n → Bool) (c : Bool) (k : ℕ) :
    (C.wires (List.replicate n c ++ List.ofFn b)).getD k false =
      wv (n + n) C (Fin.append (fun _ => c) b) k := by
  unfold wv
  rw [List.ofFn_fin_append, List.ofFn_const]

lemma app_mono {n : ℕ} (a a' b b' : Fin n → Bool) (ha : ∀ i, a i = true → a' i = true)
    (hb : ∀ i, b i = true → b' i = true) :
    ∀ i, Fin.append a b i = true → Fin.append a' b' i = true := by
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.append_left]; exact ha i
  · simp only [Fin.append_right]; exact hb i

lemma indepB (n : ℕ) (C : Circuit) (hC : AOB (n + n) C) (k : ℕ)
    (hk : ∀ a : Fin n → Bool, wv (n + n) C (Fin.append a (fun _ => false)) k =
      wv (n + n) C (Fin.append a (fun _ => true)) k) :
    ∀ a b : Fin n → Bool, wv (n + n) C (Fin.append a b) k =
      wv (n + n) C (Fin.append a (fun _ => false)) k := by
  intro a b
  have h1 := wv_mono (n + n) C hC _ _
    (app_mono a a (fun _ => false) b (fun _ h => h) (fun _ h => by simp at h)) k
  have h2 := wv_mono (n + n) C hC _ _
    (app_mono a a b (fun _ => true) (fun _ h => h) (fun _ _ => rfl)) k
  have h3 := hk a
  cases e : wv (n + n) C (Fin.append a (fun _ => false)) k
  · rw [e] at h3
    cases e2 : wv (n + n) C (Fin.append a b) k
    · rfl
    · have := h2 e2; rw [← h3] at this; exact absurd this (by simp)
  · exact h1 e

lemma indepA (n : ℕ) (C : Circuit) (hC : AOB (n + n) C) (k : ℕ)
    (hk : ∀ b : Fin n → Bool, wv (n + n) C (Fin.append (fun _ => false) b) k =
      wv (n + n) C (Fin.append (fun _ => true) b) k) :
    ∀ a b : Fin n → Bool, wv (n + n) C (Fin.append a b) k =
      wv (n + n) C (Fin.append (fun _ => false) b) k := by
  intro a b
  have h1 := wv_mono (n + n) C hC _ _
    (app_mono (fun _ => false) a b b (fun _ h => by simp at h) (fun _ h => h)) k
  have h2 := wv_mono (n + n) C hC _ _
    (app_mono a (fun _ => true) b b (fun _ _ => rfl) (fun _ h => h)) k
  have h3 := hk b
  cases e : wv (n + n) C (Fin.append (fun _ => false) b) k
  · rw [e] at h3
    cases e2 : wv (n + n) C (Fin.append a b) k
    · rfl
    · have := h2 e2; rw [← h3] at this; exact absurd this (by simp)
  · exact h1 e


theorem main : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x5]? = Option.some x6 → ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 < x9 ∧ x9 < x1 + x1 + x5) →       (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x7 → x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 ∉ x3 → ¬((∀ x11 ∈ x7.inputs, ∃ (x13 : Fin x1 → Bool), (x2.wires (List.ofFn x13 ++ List.replicate x1 Bool.false)).getD x11 Bool.false ≠ (x2.wires (List.ofFn x13 ++ List.replicate x1 Bool.true)).getD x11 Bool.false) ∨ ∀ x11 ∈ x7.inputs, ∃ (x13 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x13)).getD x11 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x13)).getD x11 Bool.false)) →         ∃ (x7 : ℕ → Set ((Fin x1 → Bool) × (Fin x1 → Bool))),           (∀ (x8 : Fin x1), x7 ↑x8 = {x9 : (Fin x1 → Bool) × (Fin x1 → Bool) | x9.1 x8 = Bool.true} ∧ x7 (x1 + ↑x8) = {x9 : (Fin x1 → Bool) × (Fin x1 → Bool) | x9.2 x8 = Bool.true}) ∧             (∀ x8 < x2.size,                 ∃ x10 < x1 + x1 + x8,                   ∃ x11 < x1 + x1 + x8,                     have x12 : Set ((Fin x1 → Bool) × (Fin x1 → Bool)) := x7 (x1 + x1 + x8);                     x12 = x7 x10 ∪ x7 x11 ∨ x12 = x7 x10 ∨ x12 = ∅ ∨ x12 = x7 x10 ∩ x7 x11 ∧ (x8 ∈ x3 ∨ ∃ (x13 : Set (Fin x1 → Bool)) (x14 : Set (Fin x1 → Bool)), x7 x10 = x13 ×ˢ Set.univ ∧ x7 x11 = Set.univ ×ˢ x14)) ∧               ∀ (x8 x9 : Fin x1 → Bool), (x8, x9) ∈ x7 x2.output ↔ PEqualNP.MetaComplexity.circuitFun (x1 + x1) x2 (Fin.append x8 x9) = Bool.true := by
  intro n C S hM hG hA
  have hC : AOB (n + n) C := by
    intro j hj
    have hs : C.gates[j]? = some (C.gates[j]) := List.getElem?_eq_getElem hj
    rw [gateAt_some hs]
    obtain ⟨a, b, hab, hlt, hb⟩ := hG j _ hs
    refine ⟨?_, ?_⟩
    · have := (hM _ (List.getElem_mem hj)).1
      simpa using this
    · intro i hi
      rw [hab] at hi
      simp at hi
      omega
  have val : ∀ (x : Fin (n + n) → Bool) (g : ℕ) (gt : Gate) (a b : ℕ),
      C.gates[g]? = some gt → gt.inputs = [a, b] →
      wv (n + n) C x (n + n + g) = gt.op.eval [wv (n + n) C x a, wv (n + n) C x b] := by
    intro x g gt a b hg hab
    have hgl : g < C.gates.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hg
      exact absurd hg (by simp)
    rw [wv_rec (n + n) C x hC g hgl, gateAt_some hg, hab]
    rfl
  refine ⟨S7 n C, ?_, ?_, ?_⟩
  · intro k
    have hk := k.isLt
    constructor
    · ext p
      rw [mem_S7, wv_input (n + n) C _ k (by omega), Set.mem_setOf_eq]
      have e : Fin.append p.1 p.2 ⟨k.val, by omega⟩ = p.1 k := Fin.append_left p.1 p.2 k
      rw [e]
    · ext p
      rw [mem_S7, wv_input (n + n) C _ (n + k) (by omega), Set.mem_setOf_eq]
      have e : Fin.append p.1 p.2 ⟨n + k.val, by omega⟩ = p.2 k := Fin.append_right p.1 p.2 k
      rw [e]
  · intro g hg
    have hgl : g < C.gates.length := hg
    have hs : C.gates[g]? = some (C.gates[g]) := List.getElem?_eq_getElem hgl
    obtain ⟨i, j, hij, hlt, hj⟩ := hG g _ hs
    have hop := (hM _ (List.getElem_mem hgl)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    dsimp only
    have hv : ∀ x, wv (n + n) C x (n + n + g) = (C.gates[g]).op.eval
        [wv (n + n) C x i, wv (n + n) C x j] := fun x => val x g _ i j hs hij
    rcases hop with hop | hop
    · by_cases hgS : g ∈ S
      · refine ⟨i, by omega, j, hj, Or.inr (Or.inr (Or.inr ⟨?_, Or.inl hgS⟩))⟩
        ext p
        rw [Set.mem_inter_iff, mem_S7, mem_S7, mem_S7, hv, hop]
        simp [GateOp.eval]
      · have hn := hA g _ hs hop hgS
        push_neg at hn
        obtain ⟨⟨k1, hk1, hk1'⟩, ⟨k2, hk2, hk2'⟩⟩ := hn
        simp only [split1, split2] at hk1' hk2'
        have iB := indepB n C hC k1 hk1'
        have iA := indepA n C hC k2 hk2'
        rw [hij] at hk1 hk2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk1 hk2
        have hk1lt : k1 < n + n + g := by rcases hk1 with rfl | rfl <;> omega
        have hk2lt : k2 < n + n + g := by rcases hk2 with rfl | rfl <;> omega
        have hw : ∀ x, wv (n + n) C x (n + n + g) =
            (wv (n + n) C x i && wv (n + n) C x j) := by
          intro x; rw [hv x, hop]; simp [GateOp.eval]
        by_cases h12 : k1 = k2
        · subst h12
          have hconst : ∀ a b : Fin n → Bool, wv (n + n) C (Fin.append a b) k1 =
              wv (n + n) C (Fin.append (fun _ => false) (fun _ => false)) k1 := by
            intro a b
            rw [iB a b, iA a (fun _ => false)]
          obtain ⟨o, ho, hv'⟩ : ∃ o, o < n + n + g ∧ ∀ x, wv (n + n) C x (n + n + g) =
              (wv (n + n) C x k1 && wv (n + n) C x o) := by
            rcases hk1 with h | h
            · subst h; exact ⟨j, hj, hw⟩
            · subst h; exact ⟨i, by omega, fun x => by rw [hw x, Bool.and_comm]⟩
          cases ec : wv (n + n) C (Fin.append (fun _ => false) (fun _ => false)) k1
          · refine ⟨o, ho, o, ho, Or.inr (Or.inr (Or.inl ?_))⟩
            ext p
            rw [mem_S7, hv', hconst, ec]
            simp
          · refine ⟨o, ho, o, ho, Or.inr (Or.inl ?_)⟩
            ext p
            rw [mem_S7, mem_S7, hv', hconst, ec]
            simp
        · refine ⟨k1, hk1lt, k2, hk2lt, Or.inr (Or.inr (Or.inr ⟨?_, Or.inr
            ⟨{a | wv (n + n) C (Fin.append a (fun _ => false)) k1 = true},
             {b | wv (n + n) C (Fin.append (fun _ => false) b) k2 = true}, ?_, ?_⟩⟩))⟩
          · ext p
            rw [Set.mem_inter_iff, mem_S7, mem_S7, mem_S7, hw]
            rcases hk1 with h1 | h1 <;> rcases hk2 with h2 | h2
            · exact absurd (h1.trans h2.symm) h12
            · subst h1; subst h2; rw [Bool.and_eq_true]
            · subst h1; subst h2; rw [Bool.and_eq_true]; exact and_comm
            · exact absurd (h1.trans h2.symm) h12
          · ext ⟨a, b⟩
            simp only [mem_S7, Set.mem_prod, Set.mem_setOf_eq, Set.mem_univ, and_true]
            rw [iB a b]
          · ext ⟨a, b⟩
            simp only [mem_S7, Set.mem_prod, Set.mem_setOf_eq, Set.mem_univ, true_and]
            rw [iA a b]
    · refine ⟨i, by omega, j, hj, Or.inl ?_⟩
      ext p
      rw [Set.mem_union, mem_S7, mem_S7, mem_S7, hv, hop]
      simp [GateOp.eval]
  · intro a b
    exact Iff.rfl

end PEqualNP.Outside.L_meta_2792

theorem PEqualNP.Outside.L_meta_2792 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x5]? = Option.some x6 → ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 < x9 ∧ x9 < x1 + x1 + x5) →       (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x7 → x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 ∉ x3 → ¬((∀ x11 ∈ x7.inputs, ∃ (x13 : Fin x1 → Bool), (x2.wires (List.ofFn x13 ++ List.replicate x1 Bool.false)).getD x11 Bool.false ≠ (x2.wires (List.ofFn x13 ++ List.replicate x1 Bool.true)).getD x11 Bool.false) ∨ ∀ x11 ∈ x7.inputs, ∃ (x13 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x13)).getD x11 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x13)).getD x11 Bool.false)) →         ∃ (x7 : ℕ → Set ((Fin x1 → Bool) × (Fin x1 → Bool))),           (∀ (x8 : Fin x1), x7 ↑x8 = {x9 : (Fin x1 → Bool) × (Fin x1 → Bool) | x9.1 x8 = Bool.true} ∧ x7 (x1 + ↑x8) = {x9 : (Fin x1 → Bool) × (Fin x1 → Bool) | x9.2 x8 = Bool.true}) ∧             (∀ x8 < x2.size,                 ∃ x10 < x1 + x1 + x8,                   ∃ x11 < x1 + x1 + x8,                     have x12 : Set ((Fin x1 → Bool) × (Fin x1 → Bool)) := x7 (x1 + x1 + x8);                     x12 = x7 x10 ∪ x7 x11 ∨ x12 = x7 x10 ∨ x12 = ∅ ∨ x12 = x7 x10 ∩ x7 x11 ∧ (x8 ∈ x3 ∨ ∃ (x13 : Set (Fin x1 → Bool)) (x14 : Set (Fin x1 → Bool)), x7 x10 = x13 ×ˢ Set.univ ∧ x7 x11 = Set.univ ×ˢ x14)) ∧               ∀ (x8 x9 : Fin x1 → Bool), (x8, x9) ∈ x7 x2.output ↔ PEqualNP.MetaComplexity.circuitFun (x1 + x1) x2 (Fin.append x8 x9) = Bool.true := by
  exact PEqualNP.Outside.L_meta_2792.main
