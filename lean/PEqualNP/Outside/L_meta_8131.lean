import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_8131

-- The wire-table invariants and gate simplification are adapted from L-meta-551.
private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

private lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

private lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

private def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

private lemma simplifyGate_nok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, NOkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; exact ⟨⟨Or.inl rfl, by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inl rfl), by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inr rfl), by simp⟩, by simp⟩
  · simp at hg
  · simp at hg

private lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

private def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

private def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

private lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

private lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

private lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

private def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

private lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

private lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)


private lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]

-- A gate whose (normalised) inputs see a fixed false wire 0 or a fixed true wire 10 in
-- the right way has a constant status.
private def Cond (g : Gate) : Prop :=
  g.op = GateOp.not ∧ (g.inputs.head? = some 0 ∨ g.inputs.head? = some 10) ∨
    g.op = GateOp.and ∧ 0 ∈ g.inputs ∨ g.op = GateOp.or ∧ 10 ∈ g.inputs

private lemma simpAnd_const (m : ℕ) (L : List (Bool ⊕ ℕ)) (hlen : L.length ≤ 2)
    (hc : Sum.inl false ∈ L) : ∃ c, (simpAnd m L).2 = Sum.inl c := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
    simp_all [simpAnd]

private lemma simpOr_const (m : ℕ) (L : List (Bool ⊕ ℕ)) (hlen : L.length ≤ 2)
    (hc : Sum.inl true ∈ L) : ∃ c, (simpOr m L).2 = Sum.inl c := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
    simp_all [simpOr]

private lemma cond_status (g : Gate) (hok : OkGate g) (hc : Cond g) (m : ℕ)
    (s : ℕ → Bool ⊕ ℕ) (h0 : s 0 = Sum.inl false) (h10 : s 10 = Sum.inl true) :
    ∃ c, (simplifyGate (normGate g).op m ((normGate g).inputs.map s)).2 = Sum.inl c := by
  obtain ⟨op, ins⟩ := g
  rcases hc with ⟨hop, hh⟩ | ⟨hop, hm⟩ | ⟨hop, hm⟩
  · simp only at hop
    subst hop
    rcases ins with _ | ⟨a, l⟩
    · simp at hh
    · simp only [List.head?_cons, Option.some.injEq] at hh
      rcases hh with rfl | rfl
      · simp [normGate, simplifyGate, simpNot, h0]
      · simp [normGate, simplifyGate, simpNot, h10]
  · simp only at hop hm
    subst hop
    simp only [normGate, simplifyGate]
    apply simpAnd_const
    · simpa using hok.2
    · exact List.mem_map.mpr ⟨0, hm, h0⟩
  · simp only at hop hm
    subst hop
    simp only [normGate, simplifyGate]
    apply simpOr_const
    · simpa using hok.2
    · exact List.mem_map.mpr ⟨10, hm, h10⟩

private lemma elimPass_count (n : ℕ) (K : ℕ → Prop) (qb : Gate → Bool)
    (hq : ∀ g, qb g = true → ∃ w ∈ g.inputs, K w)
    (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ gs, NOkGate g)
    (h0 : acc.1.getD 0 (Sum.inl false) = Sum.inl false)
    (h10 : acc.1.getD 10 (Sum.inl false) = Sum.inl true)
    (ha : 10 < acc.1.length)
    (hK : ∀ w, K w → w < acc.1.length → ∃ c, acc.1.getD w (Sum.inl false) = Sum.inl c)
    (hC : ∀ k (hk : k < gs.length), K (acc.1.length + k) →
      ∃ g0, OkGate g0 ∧ Cond g0 ∧ gs.get ⟨k, hk⟩ = normGate g0) :
    (elimPass n gs acc).2.length + gs.countP qb ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    let ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
    let part := simplifyGate g.op (n + acc.2.length) ins
    have hstep : (elimStep n acc g).1 = acc.1 ++ [part.2] := rfl
    have h0' : (elimStep n acc g).1.getD 0 (Sum.inl false) = Sum.inl false := by
      rw [hstep, getD_snoc_lt _ _ _ _ (by omega), h0]
    have h10' : (elimStep n acc g).1.getD 10 (Sum.inl false) = Sum.inl true := by
      rw [hstep, getD_snoc_lt _ _ _ _ ha, h10]
    have ha' : 10 < (elimStep n acc g).1.length := by rw [hstep]; simp; omega
    have hK' : ∀ w, K w → w < (elimStep n acc g).1.length →
        ∃ c, (elimStep n acc g).1.getD w (Sum.inl false) = Sum.inl c := by
      intro w hw hlt
      rw [hstep] at hlt ⊢
      simp only [List.length_append, List.length_singleton] at hlt
      by_cases hwl : w < acc.1.length
      · rw [getD_snoc_lt _ _ _ _ hwl]
        exact hK w hw hwl
      · have hweq : w = acc.1.length := by omega
        rw [getD_snoc_eq _ _ _ _ hweq]
        have hk0 : K (acc.1.length + 0) := by simpa [← hweq] using hw
        obtain ⟨g0, hok0, hc0, hg0⟩ := hC 0 (by simp) hk0
        have hg : g = normGate g0 := by simpa using hg0
        have := cond_status g0 hok0 hc0 (n + acc.2.length)
          (fun i => acc.1.getD i (Sum.inl false)) h0 h10
        rw [← hg] at this
        exact this
    have hC' : ∀ k (hk : k < gs.length), K ((elimStep n acc g).1.length + k) →
        ∃ g0, OkGate g0 ∧ Cond g0 ∧ gs.get ⟨k, hk⟩ = normGate g0 := by
      intro k hk hKk
      rw [hstep] at hKk
      simp only [List.length_append, List.length_singleton] at hKk
      obtain ⟨g0, h1, h2, h3⟩ := hC (k + 1) (by simp; omega)
        (by rw [show acc.1.length + (k + 1) = acc.1.length + 1 + k by omega]; exact hKk)
      exact ⟨g0, h1, h2, by simpa using h3⟩
    have ht := ih (elimStep n acc g) (fun a hm => h a (List.mem_cons_of_mem _ hm)) h0' h10' ha'
      hK' hC'
    have hb : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      change (acc.2 ++ part.1.toList).length ≤ _
      rw [List.length_append]
      exact Nat.add_le_add_left (toList_opt_len_le _) _
    rw [elimPass_cons, List.countP_cons, List.length_cons]
    cases he : qb g with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    | true =>
      have hn : part.1 = none := by
        have hg := h g List.mem_cons_self
        apply simplifyGate_none_of_const _ _ _ hg.1.1
        · simpa [ins] using hg.1.2
        · intro hn
          simpa [ins] using hg.2 hn
        · obtain ⟨w, hw, hKw⟩ := hq g he
          by_cases hwl : w < acc.1.length
          · obtain ⟨c, hc⟩ := hK w hKw hwl
            exact ⟨c, List.mem_map.mpr ⟨w, hw, hc⟩⟩
          · exact ⟨false, List.mem_map.mpr ⟨w, hw, List.getD_eq_default _ _ (by omega)⟩⟩
      have hd : (elimStep n acc g).2.length = acc.2.length := by
        change (acc.2 ++ part.1.toList).length = _
        simp [hn]
      simp only [↓reduceIte]
      omega

private def initial : List (Bool ⊕ ℕ) × List Gate :=
  ([Sum.inl false, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4,
    Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inr 8, Sum.inl true], [])

private lemma fixed_eq (x : Fin 9 → Bool) :
    (false :: (List.ofFn x ++ [true])) =
      [false, x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, true] := by
  simp [List.ofFn_succ]

private lemma first_inv (x : Fin 9 → Bool) :
    ElimInv 9 (List.ofFn x) (false :: (List.ofFn x ++ [true])) initial := by
  rw [fixed_eq]
  refine ⟨List.length_ofFn, rfl, ?_⟩
  intro i
  by_cases hi : i < 11
  · interval_cases i <;>
      simp [initial, statValid, statVal, wiresFrom_nil, List.getD]
  · rw [List.getD_eq_default _ _ (by simp [initial]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

private lemma card_filter_get {α : Type*} (p : α → Prop) [DecidablePred p] (l : List α) :
    (Finset.univ.filter fun i : Fin l.length => p (l.get i)).card =
      l.countP (fun a => decide (p a)) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [Finset.card_filter]
    have hs := Fin.sum_univ_succ (n := t.length) (fun i => if p ((a :: t).get i) then (1 : ℕ) else 0)
    refine hs.trans ?_
    rw [List.countP_cons, ← ih, Finset.card_filter]
    show (if p a then 1 else 0) + (∑ i : Fin t.length, if p (t.get i) then (1 : ℕ) else 0) =
      (∑ i : Fin t.length, if p (t.get i) then (1 : ℕ) else 0) + (if decide (p a) = true then 1 else 0)
    simp only [decide_eq_true_eq]
    omega

private def Kw (C : Circuit) (x5 : ℕ) : Prop :=
  x5 = 0 ∨ x5 = 10 ∨ ∃ (x6 : Fin C.size), x5 = 11 + ↑x6 ∧
    ((C.gates.get x6).op = GateOp.not ∧ ((C.gates.get x6).inputs.head? = some 0 ∨
      (C.gates.get x6).inputs.head? = some 10) ∨
     (C.gates.get x6).op = GateOp.and ∧ 0 ∈ (C.gates.get x6).inputs ∨
     (C.gates.get x6).op = GateOp.or ∧ 10 ∈ (C.gates.get x6).inputs)

private def Rd (g : Gate) (x5 : ℕ) : Prop :=
  g.inputs.head? = some x5 ∨ g.op ≠ GateOp.not ∧ x5 ∈ g.inputs

private lemma rd_norm (g : Gate) (hg : OkGate g) (w : ℕ) : Rd g w ↔ w ∈ (normGate g).inputs := by
  obtain ⟨op, ins⟩ := g
  rcases hg with ⟨hop, _⟩
  cases op
  · simp only [Rd, normGate, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    constructor
    · rintro (h | h)
      · exact List.mem_of_mem_head? h
      · exact h
    · intro h; exact Or.inr h
  · simp only [Rd, normGate, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    constructor
    · rintro (h | h)
      · exact List.mem_of_mem_head? h
      · exact h
    · intro h; exact Or.inr h
  · simp only [Rd, normGate, ne_eq, not_true_eq_false, false_and, or_false]
    rcases ins with _ | ⟨a, l⟩
    · simp
    · simp [eq_comm]
  · simp at hop
  · simp at hop

private theorem remove (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 18)
    (hcnt : 3 ≤ {x4 : Fin C.size | ∃ x5, Kw C x5 ∧ Rd (C.gates.get x4) x5}.ncard) :
    HasCircuitSize 9 (fun x => C.eval (false :: (List.ofFn x ++ [true]))) 15 := by
  classical
  let gs := C.gates.map normGate
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok a (hfan a ha)
  let qb : Gate → Bool := fun g => decide (∃ w ∈ g.inputs, Kw C w)
  let acc := elimPass 9 gs initial
  have hcount : 3 ≤ gs.countP qb := by
    have h1 : {x4 : Fin C.size | ∃ x5, Kw C x5 ∧ Rd (C.gates.get x4) x5}.ncard =
        C.gates.countP (fun a => decide (∃ x5, Kw C x5 ∧ Rd a x5)) := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
      exact card_filter_get (fun a => ∃ x5, Kw C x5 ∧ Rd a x5) C.gates
    have h2 : gs.countP qb = C.gates.countP (fun a => decide (∃ x5, Kw C x5 ∧ Rd a x5)) := by
      rw [List.countP_map]
      apply List.countP_congr
      intro a ha
      simp only [Function.comp, qb, decide_eq_true_eq]
      constructor
      · rintro ⟨w, hw, hk⟩
        exact ⟨w, hk, (rd_norm a (hfan a ha) w).2 hw⟩
      · rintro ⟨w, hk, hr⟩
        exact ⟨w, (rd_norm a (hfan a ha) w).1 hr, hk⟩
    omega
  have hs : acc.2.length + 3 ≤ C.size := by
    have ht := elimPass_count 9 (Kw C) qb
      (fun g hg => by simpa [qb] using hg) gs initial hnok rfl rfl (by decide)
      (by
        intro w hw hlt
        simp only [initial, List.length_cons, List.length_nil] at hlt
        rcases hw with rfl | rfl | ⟨x6, rfl, _⟩
        · exact ⟨false, rfl⟩
        · exact ⟨true, rfl⟩
        · omega)
      (by
        intro k hk hKk
        simp only [initial, List.length_cons, List.length_nil] at hKk
        rcases hKk with h | h | ⟨x6, hx6, hc⟩
        · omega
        · omega
        · have hk6 : k = x6.val := by omega
          refine ⟨C.gates.get x6, hfan _ (List.get_mem _ _), hc, ?_⟩
          simp only [gs, List.get_eq_getElem, List.getElem_map]
          subst hk6
          rfl)
    change acc.2.length + gs.countP qb ≤ 0 + gs.length at ht
    have hl : gs.length = C.size := List.length_map _
    omega
  have hv (x : Fin 9 → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        C.eval (false :: (List.ofFn x ++ [true])) := by
    have hr := ((elimInv_pass 9 (List.ofFn x) gs (false :: (List.ofFn x ++ [true])) initial
      (fun g hg => (hnok g hg).1) (first_inv x)).2.2 C.output).2
    show _ = (wiresFrom C.gates (false :: (List.ofFn x ++ [true]))).getD C.output false
    exact hr.trans (congrArg (fun w => w.getD C.output false)
      (wiresFrom_norm C.gates (false :: (List.ofFn x ++ [true]))))
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    cases b with
    | false =>
      refine ⟨⟨[], 9⟩, by simp [FanInTwo], by simp [Circuit.size], ?_⟩
      intro x
      have hx := hv x
      rw [ho] at hx
      show _ = C.eval (false :: (List.ofFn x ++ [true]))
      rw [← hx]
      change (List.ofFn x).getD 9 false = false
      exact List.getD_eq_default _ _ (by simp)
    | true =>
      refine ⟨⟨[⟨GateOp.and, []⟩], 9⟩, by simp [FanInTwo], by simp [Circuit.size], ?_⟩
      intro x
      have hx := hv x
      rw [ho] at hx
      show _ = C.eval (false :: (List.ofFn x ++ [true]))
      rw [← hx]
      change (List.ofFn x ++ [GateOp.eval GateOp.and []]).getD 9 false = true
      rw [getD_snoc_eq _ _ _ _ (by simp)]
      rfl
  | inr i =>
    refine ⟨⟨acc.2, i⟩, elimPass_ok 9 gs _ (by simp [initial]), ?_, ?_⟩
    · change acc.2.length ≤ 15
      omega
    · intro x
      have hx := hv x
      rw [ho] at hx
      exact hx

end PEqualNP.Outside.L_meta_8131

theorem PEqualNP.Outside.L_meta_8131 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (3 : ℕ) ≤ {x4 : Fin x1.size | ∃ (x5 : ℕ), (x5 = (0 : ℕ) ∨ x5 = (10 : ℕ) ∨ ∃ (x6 : Fin x1.size), x5 = (11 : ℕ) + ↑x6 ∧ ((x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((x1.gates.get x6).inputs.head? = Option.some (0 : ℕ) ∨ (x1.gates.get x6).inputs.head? = Option.some (10 : ℕ)) ∨ (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ (x1.gates.get x6).inputs ∨ (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (10 : ℕ) ∈ (x1.gates.get x6).inputs)) ∧ ((x1.gates.get x4).inputs.head? = Option.some x5 ∨ (x1.gates.get x4).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5 ∈ (x1.gates.get x4).inputs)}.ncard → PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) (fun (x5 : Fin (9 : ℕ) → Bool) => x1.eval (Bool.false :: (List.ofFn x5 ++ [Bool.true]))) (15 : ℕ) := by
  intro C hfan hsize hcnt
  exact PEqualNP.Outside.L_meta_8131.remove C hfan hsize hcnt
