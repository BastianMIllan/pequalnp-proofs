import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2006

-- Constant propagation and duplicate-input removal, adapted from L-meta-1708 (after L-meta-726).

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def Ok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def GOK (n i : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < n + i

abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def mkG (op : GateOp) (m j k : ℕ) : Option Gate × Stat :=
  if j = k then (none, Sum.inr j) else (some ⟨op, [min j k, max j k]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => mkG GateOp.and m j k
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => mkG GateOp.or m j k
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (n i : ℕ)
    (ins : List Stat) (hlen : ins.length ≤ 2) (hv : ∀ s ∈ ins, s.Valid (n + i))
    (g : Gate) (hg : (simplify op (n + i) ins).1 = some g) : GOK n i g := by
  rcases hop with rfl | rfl
  all_goals
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, simpOr] at hg
    · cases a <;> simp [simplify, simpAnd, simpOr] at hg
    · rcases a with c | j <;> rcases b with e | k
      · simp [simplify, simpAnd, simpOr] at hg
      · cases c <;> simp [simplify, simpAnd, simpOr] at hg
      · cases e <;> simp [simplify, simpAnd, simpOr] at hg
      · have hj : j < n + i := hv (Sum.inr j) (by simp)
        have hk : k < n + i := hv (Sum.inr k) (by simp)
        simp only [simplify, simpAnd, simpOr, mkG] at hg
        split_ifs at hg with hjk
        all_goals (try simp only [Option.some.injEq] at hg)
        all_goals (first | (simp at hg; done) |
          (subst hg; exact ⟨by simp, min j k, max j k, rfl, by omega, by omega⟩))
    · simp at hlen

theorem mkG_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (w : List Bool)
    (j k : ℕ) (hj : j < w.length) (hk : k < w.length) :
    ((mkG op w.length j k).2).Valid (w.length + (mkG op w.length j k).1.toList.length) ∧
    ((mkG op w.length j k).2).val (wiresFrom (mkG op w.length j k).1.toList w)
      = op.eval [w.getD j false, w.getD k false] := by
  unfold mkG
  split_ifs with hjk
  · subst hjk
    refine ⟨by simpa [Stat.Valid] using hj, ?_⟩
    rcases hop with rfl | rfl <;> simp [Stat.val, wiresFrom, GateOp.eval]
  · refine ⟨by simp [Stat.Valid], ?_⟩
    have hw : wiresFrom [⟨op, [min j k, max j k]⟩] w
        = w ++ [op.eval [w.getD (min j k) false, w.getD (max j k) false]] := rfl
    show (wiresFrom [⟨op, [min j k, max j k]⟩] w).getD w.length false = _
    rw [hw, getD_snoc_eq]
    rcases le_total j k with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]
      rcases hop with rfl | rfl <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl
  all_goals
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with e | k
      · cases c <;> cases e <;>
          simp_all [simplify, simpAnd, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases c <;>
          simp_all [simplify, simpAnd, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases e <;>
          simp_all [simplify, simpAnd, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · have hj : j < w.length := hv (Sum.inr j) (by simp)
        have hk : k < w.length := hv (Sum.inr k) (by simp)
        simp only [simplify, simpAnd, simpOr, List.map_cons, List.map_nil, Stat.val]
        exact mkG_sound _ (by simp) w j k hj hk
    · simp at hlen

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ (∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false) ∧
  (∀ (i : ℕ) (g : Gate), acc.2[i]? = some g → GOK n i g)

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi, h3⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hvi : ∀ s ∈ ins, s.Valid (n + acc.2.length) := by
      intro s hs
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
      exact (hi a).1
    have hlen : ins.length ≤ 2 := by simpa [hins] using hgok.2
    have hs := simplify_sound g.op hgok.1 w' ins hlen (by rw [lw']; exact hvi)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_, ?_⟩
    · intro i
      show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
        ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
      rw [hnew, List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil
        rw [getD_snoc_eq, hl, getD_snoc_eq]
        exact ⟨hs.1, by rw [hs.2, hvals]⟩
      · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
        refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
        rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
        exact (hi i).2
    · intro i g' hg'
      change (acc.2 ++ r.1.toList)[i]? = some g' at hg'
      by_cases hi' : i < acc.2.length
      · rw [List.getElem?_append_left hi'] at hg'
        exact h3 i g' hg'
      · rw [List.getElem?_append_right (by omega)] at hg'
        have hb := (List.getElem?_eq_some_iff.1 hg').1
        have hmem := List.mem_of_getElem? hg'
        have := toList_length_le r.1
        have hieq : i = acc.2.length := by omega
        subst hieq
        exact simplify_ok g.op hgok.1 n acc.2.length ins hlen hvi g' (Option.mem_toList.1 hmem)

def initStats (n : ℕ) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr i.val)

theorem inv_init (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initStats n, []) := by
  refine ⟨by simp [initStats], ?_, by simp⟩
  intro i
  by_cases hlt : i < n
  · simp [initStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem main : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∃ (x4 : Fin x1 → Bool) (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x4 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x5) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ x5.output < x1 + x5.size ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x6]? = Option.some x7 → ∃ (x9 : ℕ) (x10 : ℕ), x7.inputs = [x9, x10] ∧ x9 < x10 ∧ x10 < x1 + x6 := by
  intro n C hmono hnc
  have hok : ∀ g ∈ C.gates, Ok g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    refine ⟨?_, h2⟩
    simpa using h1
  set acc := elim n C.gates (initStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc := by
    intro y
    exact inv_elim n _ (by simp) C.gates _ _ hok (inv_init n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
        = C.eval (List.ofFn y) := by
    intro y
    exact ((hinv y).2.1 C.output).2
  have hlen := elim_len n C.gates (initStats n, [])
  rw [← hacc] at hlen
  simp only [List.length_nil, zero_add] at hlen
  have hgates := (hinv (fun _ => false)).2.2
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    show C.eval (List.ofFn a) = C.eval (List.ofFn b)
    rw [← hval a, ← hval b, hst]
    rfl
  | inr j =>
    have hvj := ((hinv (fun _ => false)).2.1 C.output).1
    rw [hst] at hvj
    refine ⟨⟨acc.2, j⟩, ?_, hlen, ?_, hvj, ?_⟩
    · intro g hg
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hg
      obtain ⟨hop, a, b, hin, -, -⟩ := hgates i g hi
      refine ⟨?_, by rw [hin]; simp⟩
      rcases hop with h | h <;> simp [h]
    · funext x
      have := hval x
      rw [hst] at this
      exact this
    · intro i g hg
      exact (hgates i g hg).2

end PEqualNP.Outside.L_meta_2006

theorem PEqualNP.Outside.L_meta_2006 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∃ (x4 : Fin x1 → Bool) (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x4 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x5) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ x5.output < x1 + x5.size ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x6]? = Option.some x7 → ∃ (x9 : ℕ) (x10 : ℕ), x7.inputs = [x9, x10] ∧ x9 < x10 ∧ x10 < x1 + x6 :=
  PEqualNP.Outside.L_meta_2006.main
