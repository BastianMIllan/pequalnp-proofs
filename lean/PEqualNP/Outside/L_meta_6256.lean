import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6256

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def Next (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ p g, C.gates[p]? = some g ∧ b = n+p ∧ a ∈ g.inputs

def Live (n : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  ReflTransGen (Next n C) i C.output

def LNext (n : ℕ) (C : Circuit) (a b : ℕ) : Prop := Next n C a b ∧ Live n C b

def Trace (n : ℕ) (C : Circuit) (P : ℕ → Prop) (i j : ℕ) : Prop :=
  ReflTransGen (fun a b => P a ∧ LNext n C a b) i j

theorem next_le {n : ℕ} {C : Circuit} {a b : ℕ} (h : ReflTransGen (Next n C) a b) :
    a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.le

theorem trace_le {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.2.1.1.le

theorem live_before {n : ℕ} {C : Circuit} {a b : ℕ} (hn : Next n C a b) (h : Live n C b) :
    Live n C a := (ReflTransGen.single hn).trans h

theorem trace_start {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) (hb : P b) : P a := by
  rcases h.cases_head with rfl | ⟨_, hs, _⟩
  · exact hb
  · exact hs.1

theorem align {n : ℕ} {C : Circuit} {P Q : ℕ → Prop} {v b : ℕ}
    (p : Trace n C P v b)
    (unique : ∀ a j j', a < b → P a → LNext n C a j → LNext n C a j' → j = j') :
    ∀ d, Trace n C Q v d → (d < b ∧ P d) ∨ Trace n C Q b d := by
  induction p using ReflTransGen.head_induction_on with
  | refl =>
    intro d q
    exact Or.inr q
  | head hp pt ih =>
    intro d q
    have hlt := hp.2.1.1.trans_le (trace_le pt)
    rcases q.cases_head with rfl | ⟨j, hq, qt⟩
    · exact Or.inl ⟨hlt, hp.1⟩
    · have e := unique _ _ _ hlt hp.1 hp.2 hq.2
      subst j
      exact ih _ qt

theorem difference {n : ℕ} (C : Circuit) (x y : Fin n → Bool) :
    ∀ j, Live n C j → val C x j ≠ val C y j →
      ∃ i : Fin n, x i ≠ y i ∧ Trace n C (fun a => val C x a ≠ val C y a) i.val j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hd
    by_cases hin : j < n
    · let i : Fin n := ⟨j,hin⟩
      exact ⟨i, by simpa only [← val_input C x i, ← val_input C y i] using hd, .refl⟩
    have hb : j < n+C.gates.length := by
      by_contra! he
      exact hd ((val_beyond C x he).trans (val_beyond C y he).symm)
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hdiff : ∃ i ∈ g.inputs, i < n+p ∧ val C x i ≠ val C y i := by
      by_contra! hn
      apply hd
      rw [val_gate C x hg, val_gate C y hg]
      apply congrArg _
      apply List.map_congr_left
      intro i hi
      by_cases hj : i < n+p
      · simp [operand, hj, hn i hi hj]
      · simp [operand, hj]
    obtain ⟨a, ha, hlt, ha'⟩ := hdiff
    have hs : Next n C a (n+p) := ⟨hlt,p,g,hg,rfl,ha⟩
    obtain ⟨i, hi, hpath⟩ := ih a hlt (live_before hs hj) ha'
    exact ⟨i, hi, hpath.tail ⟨ha',hs,hj⟩⟩


variable {n : ℕ} {C : Circuit}

def point (s : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ s)


theorem point_insert {s : Finset (Fin n)} {v u : Fin n} (h : u ≠ v) :
    point (insert v s) u = point s u := by simp [point, h]

noncomputable def readers (n : ℕ) (C : Circuit) (a : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (fun b => LNext n C a b)

theorem next_in_range {a b : ℕ} (h : Next n C a b) : b < n+C.gates.length := by
  obtain ⟨_,p,g,hg,rfl,_⟩ := h
  exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.1 hg).1 n

theorem mem_readers {a b : ℕ} : b ∈ readers n C a ↔ LNext n C a b := by
  classical
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨next_in_range h.1, h⟩⟩


noncomputable def living (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (Live n C)

theorem mem_living {w : ℕ} : w ∈ living n C ↔ w < n+C.gates.length ∧ Live n C w := by
  classical
  simp [living]

theorem live_readers_nonempty {a : ℕ} (ha : Live n C a) (hneq : a ≠ C.output) :
    (readers n C a).Nonempty := by
  rcases ha.cases_head with h | ⟨b,hb,hpath⟩
  · exact (hneq h).elim
  · exact ⟨b,mem_readers.2 ⟨hb,hpath⟩⟩

theorem readers_filter (a : ℕ) :
    open Classical in readers n C a = (living n C).filter (fun b => LNext n C a b) := by
  classical
  ext b
  simp only [mem_readers,Finset.mem_filter,mem_living]
  exact ⟨fun h => ⟨⟨next_in_range h.1,h.2⟩,h⟩, And.right⟩

theorem incoming_bound {j : ℕ} (hC : Monotone2 C) (hj : j ∈ living n C) :
    open Classical in ((living n C).filter fun i => LNext n C i j).card ≤ if j<n then 0 else 2 := by
  classical
  by_cases hi : j < n
  · rw [ite_eq_left hi]
    apply Nat.le_of_eq
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hm
    obtain ⟨_,⟨_,p,g,hg,hp,_⟩,_⟩ := Finset.mem_filter.mp hm
    omega
  rw [ite_eq_right hi]
  have hj' := (mem_living.1 hj).1
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have he : j=n+p := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hsub : ((living n C).filter fun i => LNext n C i j) ⊆ g.inputs.toFinset := by
    intro a ha
    obtain ⟨_,⟨_,q,g',hg',hq,hm⟩,_⟩ := Finset.mem_filter.1 ha
    have ep : p=q := by omega
    subst q
    rw [hg] at hg'
    cases hg'
    exact List.mem_toFinset.2 hm
  exact (Finset.card_le_card hsub).trans (g.inputs.toFinset_card_le.trans
    (hC g (List.mem_of_getElem? hg)).2)


theorem input_live' {u v : Fin n}
    (hx : val C (point {u}) C.output = false) (hy : val C (point {v,u}) C.output = true) :
    Live n C v.val := by
  obtain ⟨i,hi,trace⟩ := difference C (point {u}) (point {v,u}) C.output ReflTransGen.refl
    (by rw [hx,hy]; decide)
  have ei : i=v := by
    by_contra h
    exact hi ((point_insert h).symm)
  subst i
  rcases trace.cases_head with h | ⟨b,hb,_⟩
  · rw [h]
    exact .refl
  · exact live_before hb.2.1 hb.2.2

theorem live_budget (hC : Monotone2 C) (T : Finset ℕ) (hT : ∀ a ∈ T, a < n ∧ Live n C a)
    (ho : C.output < n + C.gates.length) :
    T.card ≤ C.size + 1 := by
  classical
  have ho' : C.output ∈ living n C := mem_living.2 ⟨ho, .refl⟩
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let R := W.erase C.output
  have hSub : T ∪ S ⊆ W := by
    intro a ha
    rcases Finset.mem_union.1 ha with h | h
    · obtain ⟨h1, h2⟩ := hT a h
      exact mem_living.2 ⟨by omega, h2⟩
    · exact (Finset.mem_filter.1 h).1
  have hI : T ∩ S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_inter.1 ha
    exact (Finset.mem_filter.1 h2).2 (hT a h1).1
  have hW : T.card + S.card ≤ W.card := by
    have h := Finset.card_union_add_card_inter T S
    rw [hI, Finset.card_empty] at h
    have := Finset.card_le_card hSub
    omega
  have hR : R.card + 1 = W.card := Finset.card_erase_add_one ho'
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a-n)
    · intro a ha
      have h : a < n+C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a-n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a-n=b-n at hab
      omega
  have hlow : R.card ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a=C.output then 0 else 1 : ℕ)) = R.card := by
      calc
        _ = ∑ a ∈ W, (if a≠C.output then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a=C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R,Finset.filter_ne']
    rw [← eR]
    apply Finset.sum_le_sum
    intro a ha
    have hl := (mem_living.1 ha).2
    by_cases heq : a=C.output
    · simp [heq]
    · simpa [heq] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm :
      (∑ a ∈ W, (readers n C a).card) =
        ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2*S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j<n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j<n then 0 else 2 : ℕ)) = 2*S.card := by
      simp [S,Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change T.card ≤ C.gates.length+1
  omega

theorem main : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1 × Fin x1)), PEqualNP.TopForm.IsAO2 (x1 + x1) x2 → (∀ (x5 : Fin (x1 + x1)), (PEqualNP.MetaComplexity.circuitFun (x1 + x1) x2 fun (x6 : Fin (x1 + x1)) => Decidable.decide (x6 = x5)) = Bool.false) → (∀ x6 ∈ x3, (PEqualNP.MetaComplexity.circuitFun (x1 + x1) x2 fun (x8 : Fin (x1 + x1)) => Decidable.decide (x8 = Fin.castAdd x1 x6.1 ∨ x8 = Fin.natAdd x1 x6.2)) = Bool.true) → (Finset.image Prod.fst x3).card + (Finset.image Prod.snd x3).card ≤ x2.size + (1 : ℕ) := by
  intro N C E hAO hsing hpair
  classical
  rcases E.eq_empty_or_nonempty with rfl | ⟨p0, hp0⟩
  · simp
  have hC : Monotone2 C := by
    intro g hg
    refine ⟨?_, (hAO.2.2 g hg).le⟩
    rcases hAO.1 g hg with h | h <;> simp [h]
  have hs1 : ∀ u : Fin (N+N), val C (point {u}) C.output = false := by
    intro u
    have e : point ({u} : Finset (Fin (N+N))) = fun i => decide (i = u) := by
      funext i; simp [point]
    rw [e]; exact hsing u
  have hp1 : ∀ p ∈ E, val C (point {Fin.castAdd N p.1, Fin.natAdd N p.2}) C.output = true := by
    intro p hp
    have e : point ({Fin.castAdd N p.1, Fin.natAdd N p.2} : Finset (Fin (N+N))) =
        fun i => decide (i = Fin.castAdd N p.1 ∨ i = Fin.natAdd N p.2) := by
      funext i; simp [point]
    rw [e]; exact hpair p hp
  have hp2 : ∀ p ∈ E, val C (point {Fin.natAdd N p.2, Fin.castAdd N p.1}) C.output = true := by
    intro p hp
    rw [Finset.pair_comm]; exact hp1 p hp
  have ho : C.output < (N+N) + C.gates.length := by
    by_contra h
    have := hp1 p0 hp0
    rw [val_beyond C _ (Nat.le_of_not_gt h)] at this
    exact Bool.false_ne_true this
  let T1 := E.image (fun p => (Fin.castAdd N p.1 : Fin (N+N)).val)
  let T2 := E.image (fun p => (Fin.natAdd N p.2 : Fin (N+N)).val)
  have hT : ∀ a ∈ T1 ∪ T2, a < N + N ∧ Live (N+N) C a := by
    intro a ha
    rcases Finset.mem_union.1 ha with h | h
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 h
      exact ⟨(Fin.castAdd N p.1).isLt, input_live' (hs1 _) (hp1 p hp)⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 h
      exact ⟨(Fin.natAdd N p.2).isLt, input_live' (hs1 _) (hp2 p hp)⟩
  have hb := live_budget hC (T1 ∪ T2) hT ho
  have hdisj : T1 ∩ T2 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_inter.1 ha
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨q, _, hq⟩ := Finset.mem_image.1 h2
    have e1 : (Fin.castAdd N p.1 : Fin (N+N)).val = p.1.val := rfl
    have e2 : (Fin.natAdd N q.2 : Fin (N+N)).val = N + q.2.val := rfl
    have := p.1.isLt
    omega
  have hu := Finset.card_union_add_card_inter T1 T2
  rw [hdisj, Finset.card_empty] at hu
  have c1 : T1.card = (E.image Prod.fst).card := by
    have : T1 = (E.image Prod.fst).image (fun a : Fin N => a.val) := by
      rw [Finset.image_image]; rfl
    rw [this, Finset.card_image_of_injective _ Fin.val_injective]
  have c2 : T2.card = (E.image Prod.snd).card := by
    have : T2 = (E.image Prod.snd).image (fun a : Fin N => N + a.val) := by
      rw [Finset.image_image]; rfl
    rw [this, Finset.card_image_of_injective]
    intro a b h
    exact Fin.ext (by simpa using h)
  omega

end PEqualNP.Outside.L_meta_6256

theorem PEqualNP.Outside.L_meta_6256 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1 × Fin x1)), PEqualNP.TopForm.IsAO2 (x1 + x1) x2 → (∀ (x5 : Fin (x1 + x1)), (PEqualNP.MetaComplexity.circuitFun (x1 + x1) x2 fun (x6 : Fin (x1 + x1)) => Decidable.decide (x6 = x5)) = Bool.false) → (∀ x6 ∈ x3, (PEqualNP.MetaComplexity.circuitFun (x1 + x1) x2 fun (x8 : Fin (x1 + x1)) => Decidable.decide (x8 = Fin.castAdd x1 x6.1 ∨ x8 = Fin.natAdd x1 x6.2)) = Bool.true) → (Finset.image Prod.fst x3).card + (Finset.image Prod.snd x3).card ≤ x2.size + (1 : ℕ) :=
  PEqualNP.Outside.L_meta_6256.main
