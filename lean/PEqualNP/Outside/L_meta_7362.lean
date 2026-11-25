import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7362


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem W_inp (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, List.getD_append _ _ _ _ (by rw [W_len]; omega)]; exact ih

theorem W_oob (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (W gs x).getD i false = false := by
  apply List.getD_eq_default; rw [W_len]; exact hi

theorem W_spec (gs : List Gate) (x : List Bool) : ∀ (k : ℕ) (g : Gate), gs[k]? = some g →
    (W gs x).getD (x.length + k) false =
      g.op.eval (g.inputs.map fun i =>
        if i < x.length + k then (W gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro k g h; simp at h
  | append_singleton gs a ih =>
    intro k g h
    rw [W_snoc]
    rcases Nat.lt_or_ge k gs.length with hk | hk
    · rw [List.getElem?_append_left hk] at h
      rw [List.getD_append _ _ _ _ (by rw [W_len]; omega), ih k g h]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < x.length + k
      · simp only [hi, if_true]
        rw [List.getD_append _ _ _ _ (by rw [W_len]; omega)]
      · simp only [hi, if_false]
    · rcases Nat.lt_or_ge k (gs.length + 1) with hk1 | hk1
      · have hk2 : k = gs.length := by omega
        subst hk2
        have hag : a = g := by simpa using h
        subst hag
        rw [List.getD_append_right _ _ _ _ (by rw [W_len]), W_len]
        simp only [Nat.sub_self, List.getD_cons_zero]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < x.length + gs.length
        · simp only [hi, if_true]
          rw [List.getD_append _ _ _ _ (by rw [W_len]; omega)]
        · simp only [hi, if_false]
          exact W_oob gs x i (by omega)
      · rw [List.getElem?_eq_none (by simp; omega)] at h
        cases h

def sh (p : ℕ) (i : ℕ) : ℕ := if p < i then i - 1 else i

def up (p : ℕ) (m : ℕ) : ℕ := if m < p then m else m + 1

def del (G : List Gate) (j : ℕ) (T : Gate → Gate) : List Gate :=
  G.take j ++ (G.drop (j + 1)).map T

theorem del_len (G : List Gate) (j : ℕ) (T : Gate → Gate) (hj : j < G.length) :
    (del G j T).length + 1 = G.length := by
  simp [del]; omega

theorem del_lt (G : List Gate) (j : ℕ) (T : Gate → Gate) (k : ℕ) (g : Gate) (hj : j < G.length)
    (hk : k < j) (h : (del G j T)[k]? = some g) : G[k]? = some g := by
  unfold del at h
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take] at h
  simpa [hk] using h

theorem del_ge (G : List Gate) (j : ℕ) (T : Gate → Gate) (k : ℕ) (g : Gate) (hj : j < G.length)
    (hk : j ≤ k) (h : (del G j T)[k]? = some g) : ∃ g0, G[k + 1]? = some g0 ∧ g = T g0 := by
  unfold del at h
  rw [List.getElem?_append_right (by simp; omega)] at h
  simp only [List.length_take, List.getElem?_map, List.getElem?_drop] at h
  have e : j + 1 + (k - min j G.length) = k + 1 := by
    rw [Nat.min_eq_left (by omega)]; omega
  rw [e] at h
  cases hg : G[k + 1]? with
  | none => rw [hg] at h; simp at h
  | some g0 => rw [hg] at h; exact ⟨g0, rfl, by simpa using h.symm⟩

theorem sim (G : List Gate) (j : ℕ) (T : Gate → Gate) (x : List Bool) (n : ℕ) (hx : x.length = n)
    (hj : j < G.length)
    (hT : ∀ (k : ℕ) (g : Gate), j ≤ k → G[k + 1]? = some g → ∀ ρ ρ' : ℕ → Bool,
      (∀ i, i ≠ n + j → ρ' (sh (n + j) i) = ρ i) →
      ρ (n + j) = (W G x).getD (n + j) false →
      (∀ i, i < n + j → ρ i = (W G x).getD i false) →
      (∀ i, i < n → ρ' i = x.getD i false) →
      (∀ i, n + G.length ≤ i + 1 → ρ' i = false) →
      (T g).op.eval ((T g).inputs.map ρ') = g.op.eval (g.inputs.map ρ)) :
    ∀ m, (W (del G j T) x).getD m false = (W G x).getD (up (n + j) m) false := by
  subst hx
  have hlen := del_len G j T hj
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases Nat.lt_or_ge m x.length with hm | hm
  · rw [W_inp _ _ _ hm, show up (x.length + j) m = m by simp only [up]; split_ifs <;> omega,
      W_inp _ _ _ hm]
  · obtain ⟨k, rfl⟩ : ∃ k, m = x.length + k := ⟨m - x.length, by omega⟩
    rcases Nat.lt_or_ge k (del G j T).length with hk | hk
    · have hg : (del G j T)[k]? = some (del G j T)[k] := List.getElem?_eq_getElem hk
      rw [W_spec _ _ k _ hg]
      rcases Nat.lt_or_ge k j with hkj | hkj
      · have hg0 := del_lt G j T k _ hj hkj hg
        rw [show up (x.length + j) (x.length + k) = x.length + k by
          simp only [up]; split_ifs <;> omega, W_spec _ _ k _ hg0]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < x.length + k
        · simp only [hi, if_true]
          rw [ih i hi, show up (x.length + j) i = i by simp only [up]; split_ifs <;> omega]
        · simp only [hi, if_false]
      · obtain ⟨g0, hg0, hgT⟩ := del_ge G j T k _ hj hkj hg
        rw [show up (x.length + j) (x.length + k) = x.length + (k + 1) by
          simp only [up]; split_ifs <;> omega, W_spec _ _ (k + 1) _ hg0, hgT]
        apply hT k g0 hkj hg0
        · intro i hi
          by_cases h1 : x.length + j < i
          · have e1 : sh (x.length + j) i = i - 1 := by simp only [sh]; split_ifs; rfl
            rw [e1]
            by_cases h2 : i < x.length + (k + 1)
            · have h3 : i - 1 < x.length + k := by omega
              simp only [h2, h3, if_true]
              rw [ih (i - 1) h3]
              congr 1
              simp only [up]; split_ifs <;> omega
            · have h3 : ¬ i - 1 < x.length + k := by omega
              simp only [h2, h3, if_false]
          · have e1 : sh (x.length + j) i = i := by simp only [sh]; split_ifs; rfl
            rw [e1]
            have h2 : i < x.length + (k + 1) := by omega
            have h3 : i < x.length + k := by omega
            simp only [h2, h3, if_true]
            rw [ih i h3]
            congr 1
            simp only [up]; split_ifs <;> omega
        · have h2 : x.length + j < x.length + (k + 1) := by omega
          simp only [h2, if_true]
        · intro i hi
          have h2 : i < x.length + (k + 1) := by omega
          simp only [h2, if_true]
        · intro i hi
          have h3 : i < x.length + k := by omega
          simp only [h3, if_true]
          exact W_inp _ _ _ hi
        · intro i hi
          have h3 : ¬ i < x.length + k := by omega
          simp only [h3, if_false]
    · rw [W_oob _ _ _ (by omega), W_oob _ _ _ (by simp only [up]; split_ifs <;> omega)]

def Ts (p t : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map fun i => if i = p then t else sh p i⟩

theorem Ts_fan (p t : ℕ) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (Ts p t g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (Ts p t g).inputs.length ≤ 2 := by
  refine ⟨h.1, ?_⟩
  simp only [Ts, List.length_map]
  exact h.2

def FT (G : List Gate) : Prop :=
  ∀ g ∈ G, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
theorem fin2 (n : ℕ) (h : (Fin n → Bool) → Bool) (G : List Gate) (out : ℕ) (hF : FT G)
    (hf : ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD out false = h x)
    (j : ℕ) (hj : j < G.length) (T : Gate → Gate)
    (hTF : ∀ g ∈ G, (T g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (T g).inputs.length ≤ 2)
    (hT : ∀ (x : Fin n → Bool) (k : ℕ) (g : Gate), j ≤ k → G[k + 1]? = some g →
      ∀ ρ ρ' : ℕ → Bool,
      (∀ i, i ≠ n + j → ρ' (sh (n + j) i) = ρ i) →
      ρ (n + j) = (W G (List.ofFn x)).getD (n + j) false →
      (∀ i, i < n + j → ρ i = (W G (List.ofFn x)).getD i false) →
      (∀ i, i < n → ρ' i = (List.ofFn x).getD i false) →
      (∀ i, n + G.length ≤ i + 1 → ρ' i = false) →
      (T g).op.eval ((T g).inputs.map ρ') = g.op.eval (g.inputs.map ρ))
    (ho : out = n + j → ∃ o, o < n + j ∧
      ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD o false = h x) :
    ∃ (G' : List Gate) (out' : ℕ), FT G' ∧ G'.length + 1 = G.length ∧
      (∀ x : Fin n → Bool, (W G' (List.ofFn x)).getD out' false = h x) ∧
      ∀ (x : Fin n → Bool) (m : ℕ), m < n + j →
        (W G' (List.ofFn x)).getD m false = (W G (List.ofFn x)).getD m false := by
  have key : ∀ (x : Fin n → Bool) (m : ℕ),
      (W (del G j T) (List.ofFn x)).getD m false
        = (W G (List.ofFn x)).getD (up (n + j) m) false := by
    intro x
    exact sim G j T (List.ofFn x) n (by simp) hj (fun k g hk hg => hT x k g hk hg)
  have hlen := del_len G j T hj
  have hFT : FT (del G j T) := by
    intro g hg
    unfold del at hg
    rcases List.mem_append.mp hg with h1 | h1
    · exact hF g (List.mem_of_mem_take h1)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h1
      exact hTF g0 (List.mem_of_mem_drop hg0)
  have hlow : ∀ (x : Fin n → Bool) (m : ℕ), m < n + j →
      (W (del G j T) (List.ofFn x)).getD m false = (W G (List.ofFn x)).getD m false := by
    intro x m hm
    rw [key x m, show up (n + j) m = m by simp only [up]; split_ifs <;> omega]
  by_cases hout : out = n + j
  · obtain ⟨o, hon, hox⟩ := ho hout
    exact ⟨del G j T, o, hFT, hlen, fun x => by rw [hlow x o hon]; exact hox x, hlow⟩
  · refine ⟨del G j T, sh (n + j) out, hFT, hlen, ?_, hlow⟩
    intro x
    rw [key x, ← hf x]
    congr 1
    simp only [up, sh]
    split_ifs <;> omega


def eff (g : Gate) : List ℕ :=
  g.inputs.take (bif g.op.eval [false] then 1 else 2)

theorem eff_eval (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (ρ : ℕ → Bool) : g.op.eval (g.inputs.map ρ) = g.op.eval ((eff g).map ρ) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hl⟩ := h
  cases op with
  | and =>
    simp only [eff] at hl ⊢
    rw [show (bif GateOp.and.eval [false] then 1 else 2) = 2 by rfl,
      List.take_of_length_le hl]
  | or =>
    simp only [eff] at hl ⊢
    rw [show (bif GateOp.or.eval [false] then 1 else 2) = 2 by rfl,
      List.take_of_length_le hl]
  | not =>
    simp only [eff]
    rw [show (bif GateOp.not.eval [false] then 1 else 2) = 1 by rfl]
    cases inputs with
    | nil => rfl
    | cons a l => simp [GateOp.eval]
  | mod m => simp at hop
  | maj => simp at hop

theorem eff_Ts (p t : ℕ) (g : Gate) : eff (Ts p t g) = (eff g).map (fun i => if i = p then t else sh p i) := by
  simp only [eff, Ts, List.map_take]

theorem main (n : ℕ) (C : Circuit) (j : ℕ) (hF : FanInTwo C) (hj : j < C.gates.length)
    (hout : C.output ≠ n + j) (hdead : ∀ g ∈ C.gates, n + j ∉ eff g) :
    HasCircuitSize n (fun x : Fin n → Bool => C.eval (List.ofFn x)) (C.size - 1) := by
  have hFT : FT C.gates := hF
  obtain ⟨G', out', hF', hlen, hf', _⟩ := fin2 n (fun x : Fin n → Bool => C.eval (List.ofFn x))
    C.gates C.output hFT (fun x => rfl) j hj (Ts (n + j) 0)
    (fun g hg => Ts_fan _ _ g (hFT g hg))
    (by
      intro x k g _ hg ρ ρ' h1 _ _ _ _
      have hmem : g ∈ C.gates := List.mem_of_getElem? hg
      rw [eff_eval _ (Ts_fan _ _ g (hFT g hmem)), eff_eval _ (hFT g hmem), eff_Ts]
      show g.op.eval _ = g.op.eval _
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      have hne : i ≠ n + j := fun e => hdead g hmem (e ▸ hi)
      simp only [Function.comp_apply, hne, if_false]
      exact h1 i hne)
    (fun e => absurd e hout)
  refine ⟨⟨G', out'⟩, hF', ?_, fun x => hf' x⟩
  show G'.length ≤ C.gates.length - 1
  omega


theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem ind_out {n : ℕ} (a : Fin n) (o : ℕ)
    (h : (List.ofFn (fun i : Fin n => decide (i = a))).getD o false = true) : o = a.val := by
  by_cases ho : o < n
  · rw [ofFn_getD _ o ho] at h
    have := of_decide_eq_true h
    rw [← this]
  · rw [List.getD_eq_default _ _ (by simp; omega)] at h
    exact absurd h (by simp)

theorem indep (G : List Gate) (n : ℕ) (x y : Fin n → Bool) (v : ℕ)
    (hxy : ∀ i : Fin n, i.val ≠ v → x i = y i)
    (hv : ∀ g ∈ G, v ∉ g.inputs) :
    ∀ m, m ≠ v → (W G (List.ofFn x)).getD m false = (W G (List.ofFn y)).getD m false := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm
  rcases Nat.lt_or_ge m n with hmn | hmn
  · rw [W_inp _ _ _ (by simpa using hmn), W_inp _ _ _ (by simpa using hmn)]
    rw [ofFn_getD x m hmn, ofFn_getD y m hmn]
    exact hxy ⟨m, hmn⟩ hm
  · obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
    rcases Nat.lt_or_ge k G.length with hk | hk
    · have hg : G[k]? = some G[k] := List.getElem?_eq_getElem hk
      have h1 := W_spec G (List.ofFn x) k _ hg
      have h2 := W_spec G (List.ofFn y) k _ hg
      simp only [List.length_ofFn] at h1 h2
      rw [h1, h2]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hiv : i ≠ v := fun e => hv _ (List.getElem_mem hk) (e ▸ hi)
      by_cases hik : i < n + k
      · simp only [hik, if_true]
        exact ih i hik hiv
      · simp only [hik, if_false]
    · rw [W_oob _ _ _ (by simp; omega), W_oob _ _ _ (by simp; omega)]

theorem sum_split (l : List Gate) (f : Gate → ℕ) (p : Gate → Bool) :
    (l.map (fun g => f g + (p g).toNat)).sum = (l.map f).sum + l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    cases p a <;> simp <;> omega

theorem sum_le_two (l : List Gate)
    (h : ∀ g ∈ l, g.inputs.length + (g.op.eval [false]).toNat ≤ 2) :
    (l.map (fun g => g.inputs.length + (g.op.eval [false]).toNat)).sum ≤ 2 * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun g hg => h g (by simp [hg]))
    omega

theorem dcount (S : Finset ℕ) (l : List Gate) :
    ∑ w ∈ S, (l.filter (fun g => g.inputs.contains w)).length ≤ (l.map (fun g => g.inputs.length)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    have e : ∀ w ∈ S, ((if a.inputs.contains w = true then a :: l.filter (fun g => g.inputs.contains w)
        else l.filter (fun g => g.inputs.contains w)).length)
        = (l.filter (fun g => g.inputs.contains w)).length + (if w ∈ a.inputs.toFinset then 1 else 0) := by
      intro w _
      by_cases hw : w ∈ a.inputs
      · have : a.inputs.contains w = true := by simpa using hw
        simp [this, hw]
      · have : ¬ a.inputs.contains w = true := by simpa using hw
        simp [this, hw]
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_boole]
    have h3 : ((S.filter (fun w => w ∈ a.inputs.toFinset)).card : ℕ) ≤ a.inputs.length := by
      calc (S.filter (fun w => w ∈ a.inputs.toFinset)).card ≤ a.inputs.toFinset.card :=
            Finset.card_le_card (fun w hw => (Finset.mem_filter.mp hw).2)
        _ ≤ a.inputs.length := List.toFinset_card_le _
    simp only [Nat.cast_id] at h3 ⊢
    omega


theorem final : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : Fin x1 → ℕ := fun (x6 : Fin x1) => (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.inputs.contains ↑x6) x5.gates).length;   PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → (∀ x9 ∈ x5.gates, x9.inputs.length + (x9.op.eval [Bool.false]).toNat ≤ (2 : ℕ)) → (∀ x10 ∉ x4, (2 : ℕ) ≤ x6 x10) → x4.card + (3 : ℕ) * x4ᶜ.card + List.countP (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.false]) x5.gates ≤ x5.size + (1 : ℕ) + {x11 ∉ x4 | x6 x11 = (2 : ℕ)}.card := by
  intro n G _ A C
  dsimp only
  intro hmin hfun hfan hread
  have hfun' : ∀ x : Fin n → Bool, (W C.gates (List.ofFn x)).getD C.output false
      = NestedCover.graphFun G A x := fun x => congrFun hfun x
  have tind : ∀ v ∈ A, NestedCover.graphFun G A (fun i => decide (i = v)) = true := by
    intro v hv
    unfold NestedCover.graphFun
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl ⟨v, hv, by simp⟩
  have tzero : NestedCover.graphFun G A (fun _ => false) = false := by
    unfold NestedCover.graphFun
    simp
  by_cases hs : C.gates.length = 0
  · have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero hs
    have hAc : Aᶜ = ∅ := by
      ext v
      simp only [Finset.mem_compl, Finset.notMem_empty, iff_false, not_not]
      by_contra hv
      have := hread v hv
      simp [hnil] at this
    have hA1 : A.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      have e1 := hfun' (fun i => decide (i = a))
      have e2 := hfun' (fun i => decide (i = b))
      rw [tind a ha, hnil] at e1
      rw [tind b hb, hnil] at e2
      have o1 := ind_out a C.output (by simpa [W, W_inp] using e1)
      have o2 := ind_out b C.output (by simpa [W, W_inp] using e2)
      exact Fin.ext (o1.symm.trans o2)
    have hc : C.gates.countP (fun g => g.op.eval [false]) = 0 := by rw [hnil]; rfl
    have hsz : C.size = 0 := hs
    rw [hAc, Finset.card_empty, hc, hsz]
    omega
  have hs1 : 1 ≤ C.gates.length := by omega
  have hFan := hmin.1
  have hout : ∀ v : Fin n, C.output ≠ v.val := by
    intro v hv
    have := hmin.2 ⟨[], C.output⟩ (by intro g hg; simp at hg) (by
      funext x
      show (W [] (List.ofFn x)).getD C.output false = (W C.gates (List.ofFn x)).getD C.output false
      rw [hv, W_inp _ _ _ (by simp), W_inp _ _ _ (by simp)])
    have h0 : C.gates.length ≤ 0 := this
    omega
  have hAread : ∀ v ∈ A, 1 ≤ (C.gates.filter (fun g => g.inputs.contains v.val)).length := by
    intro v hv
    by_contra h0
    have h00 : ∀ g ∈ C.gates, v.val ∉ g.inputs := by
      intro g hg hm
      apply h0
      exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hg, by simpa using hm⟩)
    have e := indep C.gates n (fun i => decide (i = v)) (fun _ => false) v.val
      (by intro i hi; simp only [decide_eq_false_iff_not]; exact fun e => hi (congrArg Fin.val e))
      h00 C.output (hout v)
    have g1 := hfun' (fun i => decide (i = v))
    have g2 := hfun' (fun _ => false)
    rw [e, g2, tind v hv, tzero] at g1
    exact absurd g1 (by decide)
  have hgread : ∀ j < C.gates.length, C.output ≠ n + j →
      1 ≤ (C.gates.filter (fun g => g.inputs.contains (n + j))).length := by
    intro j hj ho
    by_contra h0
    have hdead : ∀ g ∈ C.gates, n + j ∉ eff g := by
      intro g hg hm
      apply h0
      have hm' : n + j ∈ g.inputs := List.mem_of_mem_take hm
      exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hg, by simpa using hm'⟩)
    obtain ⟨D, hD, hDs, hDf⟩ := main n C j hFan hj ho hdead
    have h1 := hmin.2 D hD (funext fun x => hDf x)
    have h2 : C.gates.length ≤ C.gates.length - 1 := le_trans h1 hDs
    omega
  have e := sum_split C.gates (fun g => g.inputs.length) (fun g => g.op.eval [false])
  have h2 := sum_le_two C.gates hfan
  beta_reduce at e
  have hL : (C.gates.map (fun g => g.inputs.length)).sum
      + C.gates.countP (fun g => g.op.eval [false]) ≤ 2 * C.gates.length := by omega
  have hdisj : Disjoint (Finset.range n)
      (((Finset.range C.gates.length).filter (fun j => C.output ≠ n + j)).image (fun j => n + j)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_range] at ha
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
    omega
  have hdc := dcount (Finset.range n ∪
      ((Finset.range C.gates.length).filter (fun j => C.output ≠ n + j)).image (fun j => n + j)) C.gates
  rw [Finset.sum_union hdisj] at hdc
  have hT : (((Finset.range C.gates.length).filter (fun j => C.output ≠ n + j)).image (fun j => n + j)).card
      ≤ ∑ w ∈ ((Finset.range C.gates.length).filter (fun j => C.output ≠ n + j)).image (fun j => n + j),
        (C.gates.filter (fun g => g.inputs.contains w)).length := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    exact hgread j hj.1 hj.2
  have hTc : C.gates.length ≤
      (((Finset.range C.gates.length).filter (fun j => C.output ≠ n + j)).image (fun j => n + j)).card + 1 := by
    rw [Finset.card_image_of_injective _ (add_right_injective n)]
    have h3 : (Finset.range C.gates.length).card ≤
        ((Finset.range C.gates.length).filter (fun j => C.output ≠ n + j)).card
        + ((Finset.range C.gates.length).filter (fun j => ¬ C.output ≠ n + j)).card := by
      refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
      intro j hj
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases h : C.output ≠ n + j
      · exact Or.inl ⟨hj, h⟩
      · exact Or.inr ⟨hj, h⟩
    have h4 : ((Finset.range C.gates.length).filter (fun j => ¬ C.output ≠ n + j)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, not_not] at ha hb
      omega
    rw [Finset.card_range] at h3
    omega
  have hP : ∑ w ∈ Finset.range n, (C.gates.filter (fun g => g.inputs.contains w)).length
      = ∑ v : Fin n, (C.gates.filter (fun g => g.inputs.contains v.val)).length :=
    (Fin.sum_univ_eq_sum_range (fun i => (C.gates.filter (fun g => g.inputs.contains i)).length) n).symm
  have hpt : ∑ v : Fin n, (if v ∈ A then 1 else 3)
      ≤ ∑ v : Fin n, ((C.gates.filter (fun g => g.inputs.contains v.val)).length
        + if v ∉ A ∧ (C.gates.filter (fun g => g.inputs.contains v.val)).length = 2 then 1 else 0) := by
    apply Finset.sum_le_sum
    intro v _
    by_cases hv : v ∈ A
    · simp only [hv, if_true, not_true_eq_false, false_and, if_false]
      have := hAread v hv
      omega
    · have := hread v hv
      simp only [hv, if_false, not_false_eq_true, true_and]
      split_ifs <;> omega
  have hlhs : ∑ v : Fin n, (if v ∈ A then 1 else 3) = A.card + 3 * Aᶜ.card := by
    have c1 : (Finset.univ.filter (fun v : Fin n => v ∈ A)) = A := by ext v; simp
    have c2 : (Finset.univ.filter (fun v : Fin n => ¬ v ∈ A)) = Aᶜ := by ext v; simp
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
    simp only [c1, c2]
    omega
  rw [Finset.sum_add_distrib, Finset.sum_boole] at hpt
  have hK : ((Finset.univ.filter (fun v : Fin n => v ∉ A ∧
      (C.gates.filter (fun g => g.inputs.contains v.val)).length = 2)).card : ℕ)
      ≤ ({x11 ∉ A | (C.gates.filter (fun g => g.inputs.contains x11.val)).length = 2} : Finset (Fin n)).card := by
    apply Finset.card_le_card
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨h1, h2⟩ := hv
    simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_univ, true_and, h1, not_false_eq_true]
    all_goals simpa using h2
  have hsz : C.size = C.gates.length := rfl
  rw [hsz]
  simp only [Nat.cast_id] at hpt hK
  omega

end PEqualNP.Outside.L_meta_7362

theorem PEqualNP.Outside.L_meta_7362 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : Fin x1 → ℕ := fun (x6 : Fin x1) => (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.inputs.contains ↑x6) x5.gates).length;   PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → (∀ x9 ∈ x5.gates, x9.inputs.length + (x9.op.eval [Bool.false]).toNat ≤ (2 : ℕ)) → (∀ x10 ∉ x4, (2 : ℕ) ≤ x6 x10) → x4.card + (3 : ℕ) * x4ᶜ.card + List.countP (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.false]) x5.gates ≤ x5.size + (1 : ℕ) + {x11 ∉ x4 | x6 x11 = (2 : ℕ)}.card :=
  PEqualNP.Outside.L_meta_7362.final
