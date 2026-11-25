import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8189

open PEqualNP.CircuitLowerBounds
open Classical

theorem wires_snoc (gs : List Gate) (g : Gate) (o o2 : ℕ) (l : List Bool) :
    Circuit.wires ⟨gs ++ [g], o⟩ l = Circuit.wires ⟨gs, o2⟩ l ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, o2⟩ l).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wires_length (gs : List Gate) (o : ℕ) (l : List Bool) :
    (Circuit.wires ⟨gs, o⟩ l).length = l.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    rw [wires_snoc gs g o o, List.length_append, ih]
    simp
    omega

theorem foldl_prefix (r : List Gate) : ∀ l : List Bool,
    l <+: r.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l := by
  induction r with
  | nil => intro l; simp
  | cons g r ih =>
    intro l
    rw [List.foldl_cons]
    exact (List.prefix_append l _).trans (ih _)

theorem getD_snoc_lt (l : List Bool) (b : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem wires_input (C : Circuit) (y : List Bool) (i : ℕ) (hi : i < y.length) :
    (C.wires y).getD i false = y.getD i false := by
  obtain ⟨s, hs⟩ := foldl_prefix C.gates y
  unfold Circuit.wires
  rw [← hs]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wires_len (C : Circuit) (y : List Bool) :
    (C.wires y).length = y.length + C.gates.length := by
  obtain ⟨gs, o⟩ := C
  exact wires_length gs o y

theorem gate_fact_aux (n o : ℕ) (y : List Bool) (hy : y.length = n) :
    ∀ (gs : List Gate) (k : ℕ) (hk : k < gs.length),
      (Circuit.wires ⟨gs, o⟩ y).getD (n + k) false =
        (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
          if i < n + k then (Circuit.wires ⟨gs, o⟩ y).getD i false else false) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro k hk; simp at hk
  | append_singleton gs g ih =>
    intro k hk
    have hlen := wires_length gs o y
    rw [wires_snoc gs g o o]
    simp only [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | hk'
    · rw [getD_snoc_lt _ _ _ (by omega), List.getElem_append_left hk', ih k hk']
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [getD_snoc_lt _ _ _ (by omega)]
      · rfl
    · subst hk'
      have hg : ∀ h, (gs ++ [g])[gs.length]'h = g := fun h => by simp
      rw [hg]
      rw [show n + gs.length = (Circuit.wires ⟨gs, o⟩ y).length by omega, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [getD_snoc_lt _ _ _ hi]
      · exact getD_ge _ _ (by omega)

theorem gate_fact (n : ℕ) (y : List Bool) (hy : y.length = n) (C : Circuit) (k : ℕ)
    (hk : k < C.gates.length) :
    (C.wires y).getD (n + k) false = (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i =>
          if i < n + k then (C.wires y).getD i false else false) := by
  obtain ⟨gs, o⟩ := C
  exact gate_fact_aux n o y hy gs k hk

theorem sim (n o : ℕ) (V : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (hyV : ∀ i < n, y.getD i false = V i) :
    ∀ (gs : List Gate),
      (∀ (k : ℕ) (hk : k < gs.length), (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
          if i < n + k then V i else false) = V (n + k)) →
      ∀ i, (Circuit.wires ⟨gs, o⟩ y).getD i false = if i < n + gs.length then V i else false := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ i
    simp only [Circuit.wires, List.foldl_nil, List.length_nil, Nat.add_zero]
    split_ifs with hi
    · exact hyV i hi
    · exact getD_ge y i (by omega)
  | append_singleton gs g ih =>
    intro hg i
    have ih' := ih (fun k hk => by
      have := hg k (by simp; omega)
      rwa [List.getElem_append_left hk] at this)
    have hlen := wires_length gs o y
    rw [wires_snoc gs g o o]
    simp only [List.length_append, List.length_singleton]
    rcases lt_trichotomy i (n + gs.length) with hi | hi | hi
    · rw [getD_snoc_lt _ _ _ (by omega), ih' i, if_pos hi, if_pos (by omega)]
    · subst hi
      rw [if_pos (by omega)]
      have hgl : ∀ h, (gs ++ [g])[gs.length]'h = g := fun h => by simp
      have := hg gs.length (by simp)
      rw [hgl] at this
      rw [← this]
      conv_lhs => rw [show n + gs.length = (Circuit.wires ⟨gs, o⟩ y).length by omega]
      rw [getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro i _
      rw [ih' i]
    · rw [getD_ge _ _ (by simp; omega), if_neg (by omega)]

abbrev IsConst {α : Type} (f : α → Bool) : Prop := ∃ c : Bool, ∀ x, f x = c

theorem gate_core {α : Type} (op : GateOp) (l : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hl : l.length ≤ 2)
    (E E' : ℕ → α → Bool)
    (hnc : ¬ IsConst (fun x => op.eval (l.map fun i => E i x)))
    (hne : ∀ i ∈ l, (fun x => op.eval (l.map fun i => E i x)) ≠ E i)
    (hag : ∀ i ∈ l, ¬ IsConst (E i) → ∀ x, E' i x = E i x) :
    ∀ x, op.eval (l.map fun i => E' i x) = op.eval (l.map fun i => E i x) := by
  intro x
  obtain _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ := l
  · exact (hnc ⟨op.eval [], fun _ => rfl⟩).elim
  · rcases hop with rfl | rfl | rfl
    · exact (hne a (by simp) (by funext y; simp [GateOp.eval])).elim
    · exact (hne a (by simp) (by funext y; simp [GateOp.eval])).elim
    · have ha : ¬ IsConst (E a) := by
        rintro ⟨c, hc⟩
        exact hnc ⟨!c, fun y => by simp [GateOp.eval, hc y]⟩
      simp [GateOp.eval, hag a (by simp) ha x]
  · rcases hop with rfl | rfl | rfl
    · have ha : ¬ IsConst (E a) := by
        rintro ⟨c, hc⟩
        cases c
        · exact hnc ⟨false, fun y => by simp [GateOp.eval, hc y]⟩
        · exact hne b (by simp) (by funext y; simp [GateOp.eval, hc y])
      have hb : ¬ IsConst (E b) := by
        rintro ⟨c, hc⟩
        cases c
        · exact hnc ⟨false, fun y => by simp [GateOp.eval, hc y]⟩
        · exact hne a (by simp) (by funext y; simp [GateOp.eval, hc y])
      simp [GateOp.eval, hag a (by simp) ha x, hag b (by simp) hb x]
    · have ha : ¬ IsConst (E a) := by
        rintro ⟨c, hc⟩
        cases c
        · exact hne b (by simp) (by funext y; simp [GateOp.eval, hc y])
        · exact hnc ⟨true, fun y => by simp [GateOp.eval, hc y]⟩
      have hb : ¬ IsConst (E b) := by
        rintro ⟨c, hc⟩
        cases c
        · exact hne a (by simp) (by funext y; simp [GateOp.eval, hc y])
        · exact hnc ⟨true, fun y => by simp [GateOp.eval, hc y]⟩
      simp [GateOp.eval, hag a (by simp) ha x, hag b (by simp) hb x]
    · have ha : ¬ IsConst (E a) := by
        rintro ⟨c, hc⟩
        exact hnc ⟨!c, fun y => by simp [GateOp.eval, hc y]⟩
      simp [GateOp.eval, hag a (by simp) ha x]
  · simp only [List.length_cons] at hl; omega

noncomputable def Fv (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) (x : Fin n → Bool) : Bool :=
  PEqualNP.LowMerge.wireVal C (List.ofFn (Function.update x t false)) w

def Sset (n : ℕ) (C : Circuit) (t : Fin n) : Set ℕ :=
  {j | j < C.size ∧ (IsConst (Fv n C t (n + j)) ∨ ∃ v < n + j, Fv n C t (n + j) = Fv n C t v)}

noncomputable def kept (n : ℕ) (C : Circuit) (t : Fin n) (j : ℕ) : Bool :=
  decide (j ∉ Sset n C t)

noncomputable def K (n : ℕ) (C : Circuit) (t : Fin n) : List ℕ :=
  (List.range C.gates.length).filter (kept n C t)

noncomputable def pos (n : ℕ) (C : Circuit) (t : Fin n) (j : ℕ) : ℕ :=
  ((List.range j).filter (kept n C t)).length

noncomputable def r (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) : ℕ :=
  Nat.find (⟨w, rfl⟩ : ∃ u, Fv n C t u = Fv n C t w)

noncomputable def sig (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) : ℕ :=
  if r n C t w < n then r n C t w else n + pos n C t (r n C t w - n)

def dflt : Gate := ⟨GateOp.and, []⟩

noncomputable def mk (n : ℕ) (C : Circuit) (t : Fin n) (j : ℕ) : Gate :=
  ⟨(C.gates.getD j dflt).op, (C.gates.getD j dflt).inputs.map (sig n C t)⟩

noncomputable def outW (n : ℕ) (C : Circuit) (t : Fin n) : ℕ :=
  if IsConst (Fv n C t C.output) then n + (K n C t).length else sig n C t C.output

noncomputable def V (n : ℕ) (C : Circuit) (t : Fin n) (x : Fin n → Bool) (i : ℕ) : Bool :=
  if i < n then (List.ofFn x).getD i false else Fv n C t (n + (K n C t).getD (i - n) 0) x

variable (n : ℕ) (C : Circuit) (t : Fin n)

theorem Fv_ge (w : ℕ) (x : Fin n → Bool) (h : n + C.gates.length ≤ w) : Fv n C t w x = false := by
  unfold Fv PEqualNP.LowMerge.wireVal
  apply getD_ge
  rw [wires_len, List.length_ofFn]
  exact h

theorem Fv_in (w : ℕ) (x : Fin n → Bool) (h : w < n) :
    Fv n C t w x = Function.update x t false ⟨w, h⟩ := by
  unfold Fv PEqualNP.LowMerge.wireVal
  rw [wires_input _ _ _ (by rw [List.length_ofFn]; exact h)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact h)]
  simp

theorem Fv_t (x : Fin n → Bool) : Fv n C t t.val x = false := by
  rw [Fv_in n C t t.val x t.isLt]
  simp

theorem Fv_gate (j : ℕ) (hj : j < C.gates.length) :
    Fv n C t (n + j) = fun x => (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
      if i < n + j then Fv n C t i x else false) := by
  funext x
  unfold Fv PEqualNP.LowMerge.wireVal
  exact gate_fact n _ (by simp) C j hj

theorem r_spec (w : ℕ) :
    Fv n C t (r n C t w) = Fv n C t w ∧ r n C t w ≤ w ∧
      ∀ v < r n C t w, Fv n C t v ≠ Fv n C t w := by
  refine ⟨Nat.find_spec (⟨w, rfl⟩ : ∃ u, Fv n C t u = Fv n C t w),
    Nat.find_min' (⟨w, rfl⟩ : ∃ u, Fv n C t u = Fv n C t w) rfl, ?_⟩
  intro v hv
  exact Nat.find_min (⟨w, rfl⟩ : ∃ u, Fv n C t u = Fv n C t w) hv

theorem mem_S (j : ℕ) : j ∈ Sset n C t ↔
    j < C.size ∧ (IsConst (Fv n C t (n + j)) ∨ ∃ v < n + j, Fv n C t (n + j) = Fv n C t v) :=
  Iff.rfl

theorem r_kept (w : ℕ) (hnc : ¬ IsConst (Fv n C t w)) :
    (r n C t w < n ∧ r n C t w ≠ t.val) ∨
      (n ≤ r n C t w ∧ r n C t w - n < C.gates.length ∧ r n C t w - n ∉ Sset n C t) := by
  obtain ⟨h1, h2, h3⟩ := r_spec n C t w
  by_cases hu : r n C t w < n
  · left
    refine ⟨hu, ?_⟩
    intro heq
    apply hnc
    refine ⟨false, fun x => ?_⟩
    rw [← congrFun h1 x, heq, Fv_t]
  · right
    push_neg at hu
    have hj : r n C t w = n + (r n C t w - n) := by omega
    generalize hjd : r n C t w - n = j at hj ⊢
    rw [hj] at h1 h3 ⊢
    refine ⟨by omega, ?_, ?_⟩
    · by_contra hj2
      push_neg at hj2
      apply hnc
      exact ⟨false, fun x => by rw [← congrFun h1 x]; exact Fv_ge n C t _ x (by omega)⟩
    · intro hS
      obtain ⟨_, hS2⟩ := (mem_S n C t j).1 hS
      rcases hS2 with hc | ⟨v, hv, hv2⟩
      · apply hnc
        obtain ⟨c, hc⟩ := hc
        exact ⟨c, fun x => by rw [← congrFun h1 x]; exact hc x⟩
      · exact h3 v hv (hv2.symm.trans h1)

theorem K_mem (j : ℕ) : j ∈ K n C t ↔ j < C.gates.length ∧ j ∉ Sset n C t := by
  simp [K, kept, List.mem_filter, List.mem_range]

theorem K_nodup : (K n C t).Nodup := by
  unfold K
  exact List.Nodup.filter _ List.nodup_range

theorem filter_succ (j : ℕ) (hS : j ∉ Sset n C t) :
    (List.range (j + 1)).filter (kept n C t) = (List.range j).filter (kept n C t) ++ [j] := by
  rw [List.range_succ, List.filter_append]
  simp [kept, hS]

theorem pos_K (j : ℕ) (hj : j < C.gates.length) (hS : j ∉ Sset n C t) :
    (K n C t).getD (pos n C t j) 0 = j ∧ pos n C t j < (K n C t).length := by
  have e : List.range C.gates.length =
      List.range (j + 1) ++ (List.range (C.gates.length - (j + 1))).map ((j + 1) + ·) := by
    rw [← List.range_add]
    congr 1
    omega
  unfold K pos
  rw [e, List.filter_append, filter_succ n C t j hS]
  constructor
  · rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
    simp
  · simp only [List.length_append, List.length_singleton]
    omega

theorem pos_lt (j0 j : ℕ) (hlt : j0 < j) (hS : j0 ∉ Sset n C t) : pos n C t j0 < pos n C t j := by
  have e : List.range j = List.range (j0 + 1) ++ (List.range (j - (j0 + 1))).map ((j0 + 1) + ·) := by
    rw [← List.range_add]
    congr 1
    omega
  unfold pos
  rw [e, List.filter_append, filter_succ n C t j0 hS]
  simp only [List.length_append, List.length_singleton]
  omega

theorem pos_getElem (k : ℕ) (hk : k < (K n C t).length) : pos n C t ((K n C t)[k]) = k := by
  have hm : (K n C t)[k] ∈ K n C t := List.getElem_mem hk
  rw [K_mem] at hm
  obtain ⟨h1, h2⟩ := pos_K n C t _ hm.1 hm.2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at h1
  exact (List.Nodup.getElem_inj_iff (K_nodup n C t)).1 h1

theorem trans_lemma (w : ℕ) (hnc : ¬ IsConst (Fv n C t w)) :
    (∀ x, V n C t x (sig n C t w) = Fv n C t w x) ∧
    (∀ j, j < C.gates.length → j ∉ Sset n C t → w < n + j → sig n C t w < n + pos n C t j) ∧
    sig n C t w < n + (K n C t).length := by
  obtain ⟨h1, h2, h3⟩ := r_spec n C t w
  rcases r_kept n C t w hnc with ⟨hu, ht⟩ | ⟨hu, hj, hS⟩
  · have hs : sig n C t w = r n C t w := by unfold sig; rw [if_pos hu]
    rw [hs]
    refine ⟨fun x => ?_, fun j _ _ _ => by omega, by omega⟩
    rw [← congrFun h1 x, Fv_in n C t _ x hu]
    unfold V
    rw [if_pos hu, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hu)]
    have hne : (⟨r n C t w, hu⟩ : Fin n) ≠ t := fun h => ht (congrArg Fin.val h)
    simp [Function.update_of_ne hne]
  · have hs : sig n C t w = n + pos n C t (r n C t w - n) := by
      unfold sig; rw [if_neg (by omega)]
    rw [hs]
    obtain ⟨hK1, hK2⟩ := pos_K n C t _ hj hS
    refine ⟨fun x => ?_, fun j hjl _ hw => ?_, by omega⟩
    · unfold V
      rw [if_neg (by omega),
        show n + pos n C t (r n C t w - n) - n = pos n C t (r n C t w - n) by omega,
        hK1, show n + (r n C t w - n) = r n C t w by omega, congrFun h1 x]
    · have := pos_lt n C t (r n C t w - n) j (by omega) hS
      omega

theorem newgate (hfan : PEqualNP.MetaComplexity.FanInTwo C) (x : Fin n → Bool) (k : ℕ)
    (hk : k < (K n C t).length) :
    (mk n C t ((K n C t)[k])).op.eval ((mk n C t ((K n C t)[k])).inputs.map fun i =>
      if i < n + k then V n C t x i else false) = V n C t x (n + k) := by
  have hm : (K n C t)[k] ∈ K n C t := List.getElem_mem hk
  rw [K_mem] at hm
  obtain ⟨hjl, hS⟩ := hm
  have hpk := pos_getElem n C t k hk
  have hget : (K n C t).getD k 0 = (K n C t)[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  generalize (K n C t)[k] = j at hjl hS hpk hget ⊢
  have hV : V n C t x (n + k) = Fv n C t (n + j) x := by
    unfold V
    rw [if_neg (by omega), show n + k - n = k by omega, hget]
  rw [hV]
  have hgd : C.gates.getD j dflt = C.gates[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some]
  have hgate := Fv_gate n C t j hjl
  have hfj := hfan (C.gates[j]) (List.getElem_mem hjl)
  have hSS : ¬ IsConst (Fv n C t (n + j)) ∧ ∀ v < n + j, Fv n C t (n + j) ≠ Fv n C t v := by
    refine ⟨fun h => hS ((mem_S n C t j).2 ⟨hjl, Or.inl h⟩),
      fun v hv h => hS ((mem_S n C t j).2 ⟨hjl, Or.inr ⟨v, hv, h⟩⟩)⟩
  rw [hgate] at hSS
  obtain ⟨hnc, hdup⟩ := hSS
  have hop : (C.gates[j]).op = GateOp.and ∨ (C.gates[j]).op = GateOp.or ∨
      (C.gates[j]).op = GateOp.not := by
    have := hfj.1
    simpa using this
  unfold mk
  rw [hgd, List.map_map, hgate]
  refine gate_core _ _ hop hfj.2 (fun i y => if i < n + j then Fv n C t i y else false)
    (fun i y => if sig n C t i < n + k then V n C t y (sig n C t i) else false) hnc ?_ ?_ x
  · intro i _ heq
    by_cases hij : i < n + j
    · exact hdup i hij (heq.trans (by funext y; simp [hij]))
    · exact hnc ⟨false, fun y => (congrFun heq y).trans (by simp [hij])⟩
  · intro i _ hncE y
    by_cases hij : i < n + j
    · have hFi : ¬ IsConst (Fv n C t i) := by
        rintro ⟨c, hc⟩
        exact hncE ⟨c, fun y => by simp [hij, hc y]⟩
      obtain ⟨T1, T2, _⟩ := trans_lemma n C t i hFi
      have hlt := T2 j hjl hS hij
      rw [hpk] at hlt
      show (if sig n C t i < n + k then V n C t y (sig n C t i) else false) =
        (if i < n + j then Fv n C t i y else false)
      rw [if_pos hlt, if_pos hij]
      exact T1 y
    · exact (hncE ⟨false, fun y => by simp [hij]⟩).elim

theorem main (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hex : ∃ x8 : Fin n → Bool,
      PEqualNP.MetaComplexity.circuitFun n C (Function.update x8 t false) = false) :
    ∃ x9, x9 + (Sset n C t).ncard ≤ C.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n
      (fun x => PEqualNP.MetaComplexity.circuitFun n C (Function.update x t false)) x9 := by
  obtain ⟨x8, hx8⟩ := hex
  refine ⟨(K n C t).length, ?_, ⟨⟨(K n C t).map (mk n C t), outW n C t⟩, ?_, ?_, ?_⟩⟩
  · have e1 : (K n C t).toFinset.card = (K n C t).length :=
      List.toFinset_card_of_nodup (K_nodup n C t)
    have e2 : (K n C t).toFinset =
        (Finset.range C.gates.length).filter (fun j => j ∉ Sset n C t) := by
      ext j
      simp [K_mem]
    have e3 : Sset n C t =
        ↑((Finset.range C.gates.length).filter (fun j => j ∈ Sset n C t)) := by
      ext j
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
      constructor
      · intro h
        exact ⟨((mem_S n C t j).1 h).1, h⟩
      · intro h
        exact h.2
    rw [e3, Set.ncard_coe_finset, ← e1, e2, add_comm,
      Finset.card_filter_add_card_filter_not, Finset.card_range]
    exact le_rfl
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
    rw [K_mem] at hj
    have hgd : C.gates.getD j dflt = C.gates[j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj.1, Option.getD_some]
    have hfj := hfan (C.gates[j]) (List.getElem_mem hj.1)
    unfold mk
    rw [hgd]
    exact ⟨hfj.1, by simpa using hfj.2⟩
  · simp [Circuit.size]
  · intro x
    have hsim := sim n (outW n C t) (V n C t x) (List.ofFn x) (by simp)
      (fun i hi => by unfold V; rw [if_pos hi]) ((K n C t).map (mk n C t))
      (fun k hk => by
        rw [List.length_map] at hk
        simp only [List.getElem_map]
        exact newgate n C t hfan x k hk)
    unfold Circuit.eval
    rw [hsim]
    show (if outW n C t < n + ((K n C t).map (mk n C t)).length then V n C t x (outW n C t)
      else false) = Fv n C t C.output x
    rw [List.length_map]
    unfold outW
    by_cases hc : IsConst (Fv n C t C.output)
    · rw [if_pos hc, if_neg (by omega)]
      obtain ⟨c, hc⟩ := hc
      have hcf : c = false := by rw [← hc x8]; exact hx8
      rw [hc x, hcf]
    · rw [if_neg hc]
      obtain ⟨T1, _, T3⟩ := trans_lemma n C t C.output hc
      rw [if_pos T3, T1 x]

end PEqualNP.Outside.L_meta_8189

theorem PEqualNP.Outside.L_meta_8189 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1),   let x4 : Type := Fin x1;   have x5 : ℕ → (x4 → Bool) → Bool := fun (x5 : ℕ) (x6 : x4 → Bool) => PEqualNP.LowMerge.wireVal x2 (List.ofFn (Function.update x6 x3 Bool.false)) x5;   have x6 : Set ℕ := {x6 : ℕ | x6 < x2.size ∧ ((∃ (x7 : Bool), ∀ (x8 : x4 → Bool), x5 (x1 + x6) x8 = x7) ∨ ∃ x7 < x1 + x6, x5 (x1 + x6) = x5 x7)};   PEqualNP.MetaComplexity.FanInTwo x2 → (∃ (x8 : x4 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x8 x3 Bool.false) = Bool.false) → ∃ (x9 : ℕ), x9 + x6.ncard ≤ x2.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x10 : Fin x1 → Bool) => PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x10 x3 Bool.false)) x9 := by
  intro n C t
  exact PEqualNP.Outside.L_meta_8189.main n C t
