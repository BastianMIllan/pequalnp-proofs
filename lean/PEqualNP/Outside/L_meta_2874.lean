import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2874

-- Star cover circuit: one OR chain per star, an AND with its center, an OR chain over the stars.

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def dg : Gate := ⟨GateOp.or, []⟩

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_append (gs gs' : List Gate) (w : List Bool) :
    wf (gs ++ gs') w = wf gs' (wf gs w) := by
  simp [wf, List.foldl_append]

theorem wf_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wf gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wf], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wf (g :: gs) w
        = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wf (gs : List Gate) (w : List Bool) :
    (wf gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wf_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wf (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wf gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wf_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val (pre : List Gate) (x : List Bool) (w : ℕ) : Bool := (wf pre x).getD w false

theorem val_ext (pre gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length + pre.length) :
    val (pre ++ gs) x w = val pre x w := by
  unfold val
  rw [wf_append, getD_wf _ _ _ (by rw [length_wf]; exact hw)]

theorem val_input (pre : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    val pre x i = x.getD i false := by
  unfold val
  exact getD_wf _ _ _ hi

theorem val_new (pre : List Gate) (g : Gate) (x : List Bool) :
    val (pre ++ [g]) x (x.length + pre.length) = g.op.eval (g.inputs.map (val pre x)) := by
  unfold val
  rw [wf_append]
  have step : wf [g] (wf pre x)
      = wf pre x ++ [g.op.eval (g.inputs.map fun i => (wf pre x).getD i false)] := rfl
  rw [step, ← length_wf pre x]
  simp

theorem val_beyond (pre : List Gate) (x : List Bool) (w : ℕ) (hw : x.length + pre.length ≤ w) :
    val pre x w = false := by
  unfold val
  exact List.getD_eq_default _ _ (by rw [length_wf]; exact hw)

theorem gd_lt (pre : List Gate) (g : Gate) (j : ℕ) (hj : j < pre.length) :
    (pre ++ [g]).getD j dg = pre.getD j dg := List.getD_append _ _ _ _ hj

theorem gd_eq (pre : List Gate) (g : Gate) : (pre ++ [g]).getD pre.length dg = g := by simp

structure Inv (a n : ℕ) (pre : List Gate) (S : Bool → Finset ℕ) : Prop where
  inp : ∀ (b : Bool) (i : ℕ), i < n → decide (a ≤ i) = b → i ∈ S b
  ao : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  rb : ∀ j < pre.length, ∀ i ∈ (pre.getD j dg).inputs, i < n + j
  sd : ∀ (b : Bool), ∀ w ∈ S b, (w < n ∧ decide (a ≤ w) = b) ∨ ∃ j < pre.length, w = n + j ∧
    (pre.getD j dg).op = GateOp.or ∧ ∀ i ∈ (pre.getD j dg).inputs, i ∈ S b
  an : ∀ j < pre.length, (pre.getD j dg).op = GateOp.and → ∃ (u v : ℕ) (c : Bool),
    (pre.getD j dg).inputs = [u, v] ∧ u ∈ S c ∧ v ∈ S (!c)

def S0 (a n : ℕ) : Bool → Finset ℕ := fun b => (Finset.range n).filter (fun i => decide (a ≤ i) = b)

theorem inv_nil (a n : ℕ) : Inv a n [] (S0 a n) where
  inp := by intro b i hi hb; simp [S0, hi, hb]
  ao := by simp
  rb := by simp
  sd := by
    intro b w hw
    left
    simp only [S0, Finset.mem_filter, Finset.mem_range] at hw
    exact hw
  an := by simp

theorem inv_snoc {a n : ℕ} {pre : List Gate} {S S' : Bool → Finset ℕ} (h : Inv a n pre S)
    (g : Gate) (hsub : ∀ b, S b ⊆ S' b)
    (hnew : ∀ (b : Bool), ∀ w ∈ S' b, w ∈ S b ∨
      (w = n + pre.length ∧ g.op = GateOp.or ∧ ∀ i ∈ g.inputs, i ∈ S' b))
    (hao : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ∀ i ∈ g.inputs, i < n + pre.length)
    (han : g.op = GateOp.and → ∃ (u v : ℕ) (c : Bool), g.inputs = [u, v] ∧ u ∈ S' c ∧ v ∈ S' (!c)) :
    Inv a n (pre ++ [g]) S' where
  inp := fun b i hi hb => hsub b (h.inp b i hi hb)
  ao := by
    intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | hg'
    · exact h.ao g' hg'
    · subst hg'; exact hao
  rb := by
    intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · rw [gd_lt _ _ _ hj] at hi; exact h.rb j hj i hi
    · subst hj; rw [gd_eq] at hi; exact hrb i hi
  sd := by
    intro b w hw
    rcases hnew b w hw with hw | ⟨e, hop, hin⟩
    · rcases h.sd b w hw with h1 | ⟨j, hj, e, hop, hin⟩
      · exact Or.inl h1
      · right
        refine ⟨j, by simp; omega, e, ?_, ?_⟩
        · rw [gd_lt _ _ _ hj]; exact hop
        · rw [gd_lt _ _ _ hj]; intro i hi; exact hsub b (hin i hi)
    · right
      refine ⟨pre.length, by simp, e, ?_, ?_⟩
      · rw [gd_eq]; exact hop
      · rw [gd_eq]; exact hin
  an := by
    intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · rw [gd_lt _ _ _ hj] at hop ⊢
      obtain ⟨u, v, c, e, hu, hv⟩ := h.an j hj hop
      exact ⟨u, v, c, e, hsub c hu, hsub (!c) hv⟩
    · subst hj; rw [gd_eq] at hop ⊢; exact han hop

def ins (S : Bool → Finset ℕ) (b0 : Bool) (w : ℕ) : Bool → Finset ℕ :=
  fun b => if b = b0 then insert w (S b) else S b

theorem sub_ins (S : Bool → Finset ℕ) (b0 : Bool) (w : ℕ) (b : Bool) : S b ⊆ ins S b0 w b := by
  unfold ins; split_ifs
  · exact Finset.subset_insert _ _
  · exact le_rfl

theorem mem_ins (S : Bool → Finset ℕ) (b0 : Bool) (w : ℕ) : w ∈ ins S b0 w b0 := by
  simp [ins]

theorem inv_or_side {a n : ℕ} {pre : List Gate} {S : Bool → Finset ℕ} (h : Inv a n pre S)
    (b : Bool) (u v : ℕ) (hu : u ∈ S b) (hv : v ∈ S b) (hu' : u < n + pre.length)
    (hv' : v < n + pre.length) :
    Inv a n (pre ++ [⟨GateOp.or, [u, v]⟩]) (ins S b (n + pre.length)) := by
  refine inv_snoc h _ (sub_ins S b _) ?_ (by simp) ?_ (by simp)
  · intro b' w hw
    unfold ins at hw
    split_ifs at hw with hb
    · subst hb
      rcases Finset.mem_insert.mp hw with hw | hw
      · right
        refine ⟨hw, rfl, ?_⟩
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with hi | hi <;> subst hi
        · exact sub_ins S b' _ b' hu
        · exact sub_ins S b' _ b' hv
      · exact Or.inl hw
    · exact Or.inl hw
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> assumption

theorem inv_plain {a n : ℕ} {pre : List Gate} {S : Bool → Finset ℕ} (h : Inv a n pre S)
    (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (u v : ℕ)
    (hu' : u < n + pre.length) (hv' : v < n + pre.length)
    (han : op = GateOp.and → ∃ c : Bool, u ∈ S c ∧ v ∈ S (!c)) :
    Inv a n (pre ++ [⟨op, [u, v]⟩]) S := by
  refine inv_snoc h _ (fun b => le_rfl) (fun b w hw => Or.inl hw) ⟨hop, by simp⟩ ?_ ?_
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> assumption
  · intro ha
    obtain ⟨c, h1, h2⟩ := han ha
    exact ⟨u, v, c, rfl, h1, h2⟩

def side (a n : ℕ) (b : Bool) (i : ℕ) : Prop := i < n ∧ decide (a ≤ i) = b

theorem chain (a n : ℕ) (b : Bool) : ∀ (L : List ℕ) (r : ℕ) (pre : List Gate)
    (S : Bool → Finset ℕ), Inv a n pre S → r ∈ S b → r < n + pre.length →
    (∀ i ∈ L, side a n b i) →
    ∃ (gs : List Gate) (S' : Bool → Finset ℕ) (r' : ℕ), Inv a n (pre ++ gs) S' ∧
      (∀ c, S c ⊆ S' c) ∧ gs.length = L.length ∧ r' ∈ S' b ∧ r' < n + (pre ++ gs).length ∧
      ∀ x : List Bool, x.length = n →
        val (pre ++ gs) x r' = (val pre x r || L.any (fun i => x.getD i false)) := by
  intro L
  induction L with
  | nil =>
    intro r pre S h hr hr' _
    refine ⟨[], S, r, by simpa using h, fun c => le_rfl, rfl, hr, by simpa using hr', ?_⟩
    intro x _
    simp
  | cons i L ih =>
    intro r pre S h hr hr' hL
    have hi := hL i (by simp)
    have h1 := inv_or_side h b r i hr (h.inp b i hi.1 hi.2) hr' (by have := hi.1; omega)
    obtain ⟨gs, S', r', h2, hsub, hlen, hm, hlt, hval⟩ :=
      ih (n + pre.length) _ _ h1 (mem_ins S b _) (by simp)
        (fun j hj => hL j (by simp [hj]))
    have e : pre ++ (⟨GateOp.or, [r, i]⟩ :: gs) = pre ++ [⟨GateOp.or, [r, i]⟩] ++ gs := by simp
    refine ⟨⟨GateOp.or, [r, i]⟩ :: gs, S', r', by rw [e]; exact h2,
      fun c => (sub_ins S b _ c).trans (hsub c), by simp [hlen], hm, by rw [e]; exact hlt, ?_⟩
    intro x hx
    rw [e, hval x hx]
    have hn := val_new pre ⟨GateOp.or, [r, i]⟩ x
    rw [hx] at hn
    rw [hn]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id,
      Bool.or_false]
    rw [val_input pre x i (by rw [hx]; exact hi.1)]
    simp [Bool.or_assoc]

theorem star (a n : ℕ) (b : Bool) (c v : ℕ) (L : List ℕ) (pre : List Gate)
    (S : Bool → Finset ℕ) (h : Inv a n pre S) (hc : side a n (!b) c) (hv : side a n b v)
    (hL : ∀ i ∈ L, side a n b i) :
    ∃ (gs : List Gate) (S' : Bool → Finset ℕ) (r' : ℕ), Inv a n (pre ++ gs) S' ∧
      gs.length = L.length + 1 ∧ r' < n + (pre ++ gs).length ∧
      ∀ x : List Bool, x.length = n →
        val (pre ++ gs) x r' = (x.getD c false && (x.getD v false || L.any (fun i => x.getD i false))) := by
  obtain ⟨gs, S', r', h2, _, hlen, hm, hlt, hval⟩ :=
    chain a n b L v pre S h (h.inp b v hv.1 hv.2) (by have := hv.1; omega) hL
  have hc' : c < n + (pre ++ gs).length := by have := hc.1; simp; omega
  have h3 := inv_plain h2 GateOp.and (Or.inl rfl) c r' hc' hlt
    (fun _ => ⟨!b, h2.inp (!b) c hc.1 hc.2, by simpa using hm⟩)
  refine ⟨gs ++ [⟨GateOp.and, [c, r']⟩], S', n + (pre ++ gs).length, by simpa using h3,
    by simp [hlen], by simp, ?_⟩
  intro x hx
  have hn := val_new (pre ++ gs) ⟨GateOp.and, [c, r']⟩ x
  rw [hx] at hn
  rw [← List.append_assoc, hn]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id,
    Bool.and_true]
  rw [hval x hx, val_input _ x c (by rw [hx]; exact hc.1), val_input pre x v (by rw [hx]; exact hv.1)]

def oval (pre : List Gate) (x : List Bool) : Option ℕ → Bool
  | none => false
  | some r => val pre x r

def ival (x : List Bool) (it : ℕ × Bool × List ℕ) : Bool :=
  x.getD it.1 false && it.2.2.any (fun i => x.getD i false)

def cost (it : ℕ × Bool × List ℕ) : ℕ := if it.2.2 = [] then 0 else it.2.2.length + 1

theorem top (a n : ℕ) : ∀ (items : List (ℕ × Bool × List ℕ)) (acc : Option ℕ) (pre : List Gate)
    (S : Bool → Finset ℕ), Inv a n pre S → (∀ r, acc = some r → r < n + pre.length) →
    (∀ it ∈ items, side a n (!it.2.1) it.1 ∧ ∀ i ∈ it.2.2, side a n it.2.1 i) →
    ∃ (gs : List Gate) (S' : Bool → Finset ℕ) (out : Option ℕ), Inv a n (pre ++ gs) S' ∧
      (∀ r, out = some r → r < n + (pre ++ gs).length) ∧
      (acc.isSome → gs.length ≤ (items.map cost).sum) ∧
      (acc = none → gs.length + 1 ≤ (items.map cost).sum ∨ gs = []) ∧
      ∀ x : List Bool, x.length = n →
        oval (pre ++ gs) x out = (oval pre x acc || items.any (ival x)) := by
  intro items
  induction items with
  | nil =>
    intro acc pre S h hacc _
    refine ⟨[], S, acc, by simpa using h, by simpa using hacc, by simp, by simp, ?_⟩
    intro x _
    simp
  | cons it rest ih =>
    intro acc pre S h hacc hgood
    obtain ⟨c, b, L⟩ := it
    have hg := hgood (c, b, L) (by simp)
    have hrest : ∀ it ∈ rest, side a n (!it.2.1) it.1 ∧ ∀ i ∈ it.2.2, side a n it.2.1 i :=
      fun it hit => hgood it (by simp [hit])
    cases L with
    | nil =>
      obtain ⟨gs, S', out, h2, hout, hs1, hs2, hval⟩ := ih acc pre S h hacc hrest
      refine ⟨gs, S', out, h2, hout, ?_, ?_, ?_⟩
      · intro hs; have := hs1 hs; simp [cost]; exact this
      · intro hs; have := hs2 hs; simp [cost]; exact this
      · intro x hx; rw [hval x hx]; simp [ival]
    | cons v L =>
      obtain ⟨gs1, S1, r1, h1, hlen1, hlt1, hval1⟩ :=
        star a n b c v L pre S h hg.1 (hg.2 v (by simp)) (fun i hi => hg.2 i (by simp [hi]))
      have hcost : cost (c, b, v :: L) = L.length + 2 := by simp [cost]
      cases acc with
      | none =>
        obtain ⟨gs2, S', out, h2, hout, hs1, _, hval⟩ :=
          ih (some r1) (pre ++ gs1) S1 h1 (by intro r hr; cases hr; exact hlt1) hrest
        refine ⟨gs1 ++ gs2, S', out, by simpa using h2, by simpa using hout, by simp, ?_, ?_⟩
        · intro _; left
          have := hs1 rfl
          simp only [List.map_cons, List.sum_cons, hcost, List.length_append]
          omega
        · intro x hx
          rw [← List.append_assoc, hval x hx]
          simp only [oval, Bool.false_or, List.any_cons]
          rw [hval1 x hx]
          simp [ival]
      | some r0 =>
        have hr0 : r0 < n + pre.length := hacc r0 rfl
        have h1' := inv_plain h1 GateOp.or (Or.inr rfl) r0 r1 (by simp; omega) hlt1
          (fun e => by cases e)
        obtain ⟨gs2, S', out, h2, hout, hs1, _, hval⟩ :=
          ih (some (n + (pre ++ gs1).length)) _ _ h1' (by intro r hr; cases hr; simp) hrest
        have e : pre ++ (gs1 ++ [⟨GateOp.or, [r0, r1]⟩] ++ gs2)
            = pre ++ gs1 ++ [⟨GateOp.or, [r0, r1]⟩] ++ gs2 := by simp
        refine ⟨gs1 ++ [⟨GateOp.or, [r0, r1]⟩] ++ gs2, S', out, by rw [e]; exact h2,
          by rw [e]; exact hout, ?_, by simp, ?_⟩
        · intro _
          have := hs1 rfl
          simp only [List.map_cons, List.sum_cons, hcost, List.length_append,
            List.length_singleton]
          omega
        · intro x hx
          rw [e, hval x hx]
          have hn := val_new (pre ++ gs1) ⟨GateOp.or, [r0, r1]⟩ x
          rw [hx] at hn
          simp only [oval, List.any_cons]
          rw [hn]
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id,
            Bool.or_false]
          rw [hval1 x hx, val_ext pre gs1 x r0 (by rw [hx]; exact hr0)]
          simp [ival, Bool.or_assoc]

theorem cost_le : ∀ items : List (ℕ × Bool × List ℕ),
    (items.map cost).sum ≤ (items.map (fun it => it.2.2.length)).sum + items.length := by
  intro items
  induction items with
  | nil => simp
  | cons it rest ih =>
    have : cost it ≤ it.2.2.length + 1 := by unfold cost; split_ifs <;> omega
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem getD_ofFn' {n : ℕ} (X : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn X).getD i false = X ⟨i, hi⟩ := by simp [hi]

theorem main (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1))
    (x5 : Finset (Fin x2)) (hcov : ∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) :
    ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool → Finset ℕ),
      PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧
        x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧
          (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x9 =
            Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x3 ∧
              x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) ∧
          (∀ (x10 : Bool), ∀ x11 ∈ x8 x10, x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨
            ∃ x13 < x7.size, x11 = x1 + x2 + x13 ∧
              (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x13).op =
                PEqualNP.CircuitLowerBounds.GateOp.or ∧
              ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x13).inputs, x14 ∈ x8 x10) ∧
          ∀ x10 < x7.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).op =
            PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Bool),
              (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).inputs = [x13, x14] ∧
              x13 ∈ x8 x15 ∧ x14 ∈ x8 !x15 := by
  classical
  let sP := x3.filter (fun e => e.1 ∈ x4)
  let sL := x3.filter (fun e => ¬ e.1 ∈ x4)
  let pIt : Fin x1 → ℕ × Bool × List ℕ := fun p =>
    (p.val, true, (sP.filter (fun e => e.1 = p)).toList.map (fun e => x1 + e.2.val))
  let lIt : Fin x2 → ℕ × Bool × List ℕ := fun l =>
    (x1 + l.val, false, (sL.filter (fun e => e.2 = l)).toList.map (fun e => e.1.val))
  let items := x4.toList.map pIt ++ x5.toList.map lIt
  have hgood : ∀ it ∈ items, side x1 (x1 + x2) (!it.2.1) it.1 ∧
      ∀ i ∈ it.2.2, side x1 (x1 + x2) it.2.1 i := by
    intro it hit
    simp only [items, List.mem_append, List.mem_map, Finset.mem_toList] at hit
    rcases hit with ⟨p, _, rfl⟩ | ⟨l, _, rfl⟩
    · refine ⟨⟨show p.val < x1 + x2 by have := p.2; omega, by simp [pIt]⟩, ?_⟩
      intro i hi
      simp only [pIt, List.mem_map, Finset.mem_toList] at hi
      obtain ⟨e, _, rfl⟩ := hi
      exact ⟨show x1 + e.2.val < x1 + x2 by have := e.2.2; omega, by simp [pIt]⟩
    · refine ⟨⟨show x1 + l.val < x1 + x2 by have := l.2; omega, by simp [lIt]⟩, ?_⟩
      intro i hi
      simp only [lIt, List.mem_map, Finset.mem_toList] at hi
      obtain ⟨e, _, rfl⟩ := hi
      exact ⟨show e.1.val < x1 + x2 by have := e.1.2; omega, by simp [lIt]⟩
  obtain ⟨gs, S', out, hI, hout, _, hs2, hval⟩ :=
    top x1 (x1 + x2) items none [] (S0 x1 (x1 + x2)) (inv_nil x1 (x1 + x2)) (by simp) hgood
  simp only [List.nil_append] at hI hout hval
  -- size of the cover
  have hlenP : ∀ p, (pIt p).2.2.length = (sP.filter (fun e => e.1 = p)).card := by
    intro p; simp [pIt]
  have hlenL : ∀ l, (lIt l).2.2.length = (sL.filter (fun e => e.2 = l)).card := by
    intro l; simp [lIt]
  have hcP : sP.card = ∑ p ∈ x4, (sP.filter (fun e => e.1 = p)).card :=
    Finset.card_eq_sum_card_fiberwise (by
      intro e he
      simp only [sP, Finset.coe_filter, Set.mem_ofPred_eq] at he
      exact he.2)
  have hcL : sL.card = ∑ l ∈ x5, (sL.filter (fun e => e.2 = l)).card :=
    Finset.card_eq_sum_card_fiberwise (by
      intro e he
      simp only [sL, Finset.coe_filter, Set.mem_ofPred_eq] at he
      rcases hcov e he.1 with h | h
      · exact absurd h he.2
      · exact h)
  have hsplit : sP.card + sL.card = x3.card := Finset.card_filter_add_card_filter_not _
  have hsumlen : (items.map (fun it => it.2.2.length)).sum = x3.card := by
    simp only [items, List.map_append, List.sum_append, List.map_map]
    have e1 : ((x4.toList.map ((fun it : ℕ × Bool × List ℕ => it.2.2.length) ∘ pIt))).sum
        = ∑ p ∈ x4, (sP.filter (fun e => e.1 = p)).card := by
      rw [Finset.sum_map_toList]; exact Finset.sum_congr rfl (fun p _ => hlenP p)
    have e2 : ((x5.toList.map ((fun it : ℕ × Bool × List ℕ => it.2.2.length) ∘ lIt))).sum
        = ∑ l ∈ x5, (sL.filter (fun e => e.2 = l)).card := by
      rw [Finset.sum_map_toList]; exact Finset.sum_congr rfl (fun l _ => hlenL l)
    rw [e1, e2, ← hcP, ← hcL, hsplit]
  have hitlen : items.length = x4.card + x5.card := by simp [items]
  have hcost := cost_le items
  -- value of the item disjunction
  have hany : ∀ X : Fin (x1 + x2) → Bool, items.any (ival (List.ofFn X)) =
      decide (∃ (p : Fin x1) (l : Fin x2), (p, l) ∈ x3 ∧
        X (Fin.castAdd x2 p) = true ∧ X (Fin.natAdd x1 l) = true) := by
    intro X
    have gP : ∀ p : Fin x1, (List.ofFn X).getD p.val false = X (Fin.castAdd x2 p) := by
      intro p; rw [getD_ofFn' X p.val (by have := p.2; omega)]; rfl
    have gL : ∀ l : Fin x2, (List.ofFn X).getD (x1 + l.val) false = X (Fin.natAdd x1 l) := by
      intro l; rw [getD_ofFn' X (x1 + l.val) (by have := l.2; omega)]; rfl
    rw [Bool.eq_iff_iff, decide_eq_true_iff, List.any_eq_true]
    constructor
    · rintro ⟨it, hit, hv⟩
      simp only [items, List.mem_append, List.mem_map, Finset.mem_toList] at hit
      rcases hit with ⟨p, _, rfl⟩ | ⟨l, _, rfl⟩
      · simp only [ival, pIt, Bool.and_eq_true, List.any_eq_true, List.mem_map,
          Finset.mem_toList] at hv
        obtain ⟨hp, i, ⟨e, he, rfl⟩, hi⟩ := hv
        simp only [sP, Finset.mem_filter] at he
        obtain ⟨⟨he3, _⟩, rfl⟩ := he
        exact ⟨e.1, e.2, he3, by rw [← gP]; exact hp, by rw [← gL]; exact hi⟩
      · simp only [ival, lIt, Bool.and_eq_true, List.any_eq_true, List.mem_map,
          Finset.mem_toList] at hv
        obtain ⟨hl, i, ⟨e, he, rfl⟩, hi⟩ := hv
        simp only [sL, Finset.mem_filter] at he
        obtain ⟨⟨he3, _⟩, rfl⟩ := he
        exact ⟨e.1, e.2, he3, by rw [← gP]; exact hi, by rw [← gL]; exact hl⟩
    · rintro ⟨p, l, hpl, hp, hl⟩
      by_cases h4 : p ∈ x4
      · refine ⟨pIt p, ?_, ?_⟩
        · simp only [items, List.mem_append, List.mem_map, Finset.mem_toList]
          exact Or.inl ⟨p, h4, rfl⟩
        · simp only [ival, pIt, Bool.and_eq_true, List.any_eq_true, List.mem_map,
            Finset.mem_toList]
          refine ⟨by rw [gP]; exact hp, x1 + l.val, ⟨(p, l), ?_, rfl⟩, by rw [gL]; exact hl⟩
          simp [sP, hpl, h4]
      · have h5 : l ∈ x5 := by
          rcases hcov (p, l) hpl with h | h
          · exact absurd h h4
          · exact h
        refine ⟨lIt l, ?_, ?_⟩
        · simp only [items, List.mem_append, List.mem_map, Finset.mem_toList]
          exact Or.inr ⟨l, h5, rfl⟩
        · simp only [ival, lIt, Bool.and_eq_true, List.any_eq_true, List.mem_map,
            Finset.mem_toList]
          refine ⟨by rw [gL]; exact hl, p.val, ⟨(p, l), ?_, rfl⟩, by rw [gP]; exact hp⟩
          simp [sL, hpl, h4]
  refine ⟨⟨gs, out.getD (x1 + x2 + gs.length)⟩, S', ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg; exact (hI.ao g hg).1
  · intro j hj i hi; exact hI.rb j hj i hi
  · intro g hg; exact (hI.ao g hg).2
  · show gs.length ≤ _
    rcases hs2 rfl with h | h
    · omega
    · simp [h]
  · intro X
    have hv := hval (List.ofFn X) (by simp)
    simp only [oval, Bool.false_or] at hv
    rw [← hany X, ← hv]
    show (wf gs (List.ofFn X)).getD (out.getD (x1 + x2 + gs.length)) false = _
    cases out with
    | none =>
      simp only [Option.getD_none]
      exact val_beyond gs (List.ofFn X) _ (by simp)
    | some r => rfl
  · intro b w hw
    exact hI.sd b w hw
  · intro j hj hop
    exact hI.an j hj hop

end PEqualNP.Outside.L_meta_2874

theorem PEqualNP.Outside.L_meta_2874 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)),   (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) →     ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool → Finset ℕ),       PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧         x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧           (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x3 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) ∧             have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x7;             (∀ (x10 : Bool), ∀ x11 ∈ x8 x10, x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨ ∃ x13 < x7.size, x11 = x1 + x2 + x13 ∧ (x9 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (x9 x13).inputs, x14 ∈ x8 x10) ∧ ∀ x10 < x7.size, (x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Bool), (x9 x10).inputs = [x13, x14] ∧ x13 ∈ x8 x15 ∧ x14 ∈ x8 !x15 := by
  intro x1 x2 x3 x4 x5 hcov
  obtain ⟨C, S, h1, h2, h3, h4, h5⟩ := PEqualNP.Outside.L_meta_2874.main x1 x2 x3 x4 x5 hcov
  exact ⟨C, S, h1, h2, h3, h4, h5⟩
