import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8895

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.HeptadCover

-- one gate step of the wire values, and of the line degrees
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dstep (d : List ℕ) (g : Gate) : List ℕ :=
  d ++ [g.lineDegree d]

def init (N : ℕ) (marked : Finset ℕ) : List ℕ :=
  (List.range N).map fun i => if i ∈ marked then 1 else 0

theorem getD_snoc_lt {α : Type} (l : List α) (a d : α) (i : ℕ) (h : i < l.length) :
    (l ++ [a]).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_big {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) :
    l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem len_fold (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem dlen_fold (gs : List Gate) : ∀ d : List ℕ,
    (gs.foldl dstep d).length = d.length + gs.length := by
  induction gs with
  | nil => intro d; simp
  | cons g gs ih =>
    intro d
    rw [List.foldl_cons, ih]
    simp only [dstep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem foldr_union_card (l : List ℕ) (F : ℕ → Finset ℕ) (c : ℕ → ℕ)
    (h : ∀ j ∈ l, (F j).card ≤ c j) :
    ((l.map F).foldr (fun (a b : Finset ℕ) => a ∪ b) ∅).card ≤ (l.map c).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons, List.sum_cons]
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add (h a (by simp)) (ih (fun j hj => h j (by simp [hj]))))

theorem subset_foldr_union (l : List ℕ) (F : ℕ → Finset ℕ) (j : ℕ) (hj : j ∈ l) :
    F j ⊆ (l.map F).foldr (fun (a b : Finset ℕ) => a ∪ b) ∅ := by
  induction l with
  | nil => simp at hj
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp hj with h | h
    · subst h
      exact fun x hx => Finset.mem_union_left _ hx
    · exact fun x hx => Finset.mem_union_right _ (ih h hx)

theorem le_foldr_max (l : List ℕ) (c : ℕ → ℕ) (j : ℕ) (hj : j ∈ l) :
    c j ≤ (l.map c).foldr max 0 := by
  induction l with
  | nil => simp at hj
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp hj with h | h
    · subst h
      exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

-- a true wire of an AND/OR circuit stays true when the unmarked true inputs are kept and only
-- at most (line degree) marked true inputs are kept
theorem support (marked : Finset ℕ) (x : List Bool) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (gs.foldl step x).getD i false = true →
      ∃ S : Finset ℕ, S.card ≤ (gs.foldl dstep (init x.length marked)).getD i 0 ∧
        ∀ y : List Bool, y.length = x.length →
          (∀ j, x.getD j false = true → (j ∉ marked ∨ j ∈ S) → y.getD j false = true) →
          (gs.foldl step y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    simp only [List.foldl_nil] at hi ⊢
    have hlt : i < x.length := by
      by_contra h
      rw [getD_big _ _ _ (Nat.le_of_not_lt h)] at hi
      exact Bool.false_ne_true hi
    by_cases hm : i ∈ marked
    · refine ⟨{i}, ?_, ?_⟩
      · simp [init, List.getD_eq_getElem?_getD, hlt, hm]
      · intro y _ hy
        exact hy i hi (Or.inr (Finset.mem_singleton_self i))
    · refine ⟨∅, by simp, ?_⟩
      intro y _ hy
      exact hy i hi (Or.inl hm)
  | append_singleton gs g ih =>
    intro i hi
    have hgs' : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' h' => hgs g' (List.mem_append_left _ h')
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or :=
      hgs g (List.mem_append_right _ (List.mem_singleton_self g))
    have ih' := ih hgs'
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at hi ⊢
    have hwl : (gs.foldl step x).length = x.length + gs.length := len_fold gs x
    have hdl : (gs.foldl dstep (init x.length marked)).length = x.length + gs.length := by
      rw [dlen_fold]; simp [init]
    have hyl : ∀ y : List Bool, y.length = x.length →
        (gs.foldl step y).length = x.length + gs.length := by
      intro y hy; rw [len_fold, hy]
    rcases lt_trichotomy i (gs.foldl step x).length with hlt | heq | hgt
    · rw [step, getD_snoc_lt _ _ _ _ hlt] at hi
      obtain ⟨S, hS, hy⟩ := ih' i hi
      refine ⟨S, ?_, ?_⟩
      · rw [dstep, getD_snoc_lt _ _ _ _ (by omega)]
        exact hS
      · intro y hyl' hcond
        rw [step, getD_snoc_lt _ _ _ _ (by rw [hyl y hyl']; omega)]
        exact hy y hyl' hcond
    · subst heq
      rw [step, getD_snoc_eq] at hi
      have hidx : ∀ y : List Bool, y.length = x.length →
          (gs.foldl step x).length = (gs.foldl step y).length := by
        intro y hy; rw [hyl y hy, hwl]
      have hdidx : (gs.foldl step x).length = (gs.foldl dstep (init x.length marked)).length := by
        rw [hwl, hdl]
      rcases hg with hand | hor
      · rw [hand] at hi
        have hin : ∀ j ∈ g.inputs, (gs.foldl step x).getD j false = true := by
          simpa [GateOp.eval, List.all_eq_true] using hi
        have hex : ∀ j ∈ g.inputs, ∃ S : Finset ℕ,
            S.card ≤ (gs.foldl dstep (init x.length marked)).getD j 0 ∧
            ∀ y : List Bool, y.length = x.length →
              (∀ k, x.getD k false = true → (k ∉ marked ∨ k ∈ S) → y.getD k false = true) →
              (gs.foldl step y).getD j false = true :=
          fun j hj => ih' j (hin j hj)
        choose! F hF1 hF2 using hex
        refine ⟨(g.inputs.map F).foldr (fun (a b : Finset ℕ) => a ∪ b) ∅, ?_, ?_⟩
        · rw [hdidx, dstep, getD_snoc_eq]
          unfold Gate.lineDegree
          rw [if_pos hand]
          exact foldr_union_card g.inputs F _ hF1
        · intro y hyl' hcond
          rw [step, hidx y hyl', getD_snoc_eq, hand]
          have hall : ∀ j ∈ g.inputs, (gs.foldl step y).getD j false = true := by
            intro j hj
            exact hF2 j hj y hyl' (fun k hk hk2 =>
              hcond k hk (hk2.imp id (fun h => subset_foldr_union g.inputs F j hj h)))
          simpa [GateOp.eval, List.all_eq_true] using hall
      · have hand' : g.op ≠ GateOp.and := by
          intro h
          rw [hor] at h
          exact GateOp.noConfusion h
        rw [hor] at hi
        have hex : ∃ j ∈ g.inputs, (gs.foldl step x).getD j false = true := by
          simpa [GateOp.eval, List.any_eq_true] using hi
        obtain ⟨j, hj, hjt⟩ := hex
        obtain ⟨S, hS, hy⟩ := ih' j hjt
        refine ⟨S, ?_, ?_⟩
        · rw [hdidx, dstep, getD_snoc_eq]
          unfold Gate.lineDegree
          rw [if_neg hand']
          exact hS.trans (le_foldr_max g.inputs (fun i => (gs.foldl dstep (init x.length marked)).getD i 0) j hj)
        · intro y hyl' hcond
          rw [step, hidx y hyl', getD_snoc_eq, hor]
          have h1 := hy y hyl' hcond
          have h2 : ∃ j ∈ g.inputs, (gs.foldl step y).getD j false = true := ⟨j, hj, h1⟩
          simpa [GateOp.eval, List.any_eq_true] using h2
    · rw [step, getD_big _ _ _ (by simp; omega)] at hi
      exact absurd hi (by decide)

-- the plane of order three as arithmetic
def inc3 (q l : Fin 13) : Bool := decide (((q.val + 13 - l.val) % 13) ∈ [0, 1, 3, 9])

theorem mem_iff (q l : Fin 13) : q ∈ singerLines3 l ↔ inc3 q l = true := by
  simp [singerLines3, inc3]

theorem inc_self (p : Fin 13) : inc3 p p = true := by
  revert p
  decide

def meet (a b : Fin 13) : Fin 13 :=
  ((List.finRange 13).find? (fun p => inc3 p a && inc3 p b)).getD 0

set_option maxRecDepth 100000 in
theorem dec_pencil : ∀ a b l : Fin 13, inc3 (meet a b) l = true ∨
    ∃ q : Fin 13, inc3 q l = true ∧ inc3 q a = false ∧ inc3 q b = false := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem dec_avoid : ∀ a b p : Fin 13, p ≠ a → p ≠ b →
    ∃ l : Fin 13, inc3 p l = true ∧ inc3 a l = false ∧ inc3 b l = false := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem dec_join : ∀ a b : Fin 13, ∃ l : Fin 13, inc3 a l = true ∧ inc3 b l = true := by
  decide +kernel

theorem card_cases (T : Finset (Fin 13)) (h : T.card ≤ 2) : T = ∅ ∨ ∃ a b, T = {a, b} := by
  have : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 := by omega
  rcases this with h0 | h1 | h2
  · exact Or.inl (Finset.card_eq_zero.mp h0)
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    exact Or.inr ⟨a, a, (Finset.insert_eq_of_mem (Finset.mem_singleton_self a)).symm⟩
  · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp h2
    exact Or.inr ⟨a, b, rfl⟩

theorem pencil (T : Finset (Fin 13)) (h : T.card ≤ 2) : ∃ v : Fin 13, ∀ l : Fin 13,
    (∀ q ∈ singerLines3 l, ∃ t ∈ T, q ∈ singerLines3 t) → v ∈ singerLines3 l := by
  rcases card_cases T h with rfl | ⟨a, b, rfl⟩
  · refine ⟨0, fun l hl => ?_⟩
    obtain ⟨t, ht, _⟩ := hl l ((mem_iff l l).mpr (inc_self l))
    simp at ht
  · refine ⟨meet a b, fun l hl => ?_⟩
    rw [mem_iff]
    rcases dec_pencil a b l with h1 | ⟨q, hq, hqa, hqb⟩
    · exact h1
    · exfalso
      obtain ⟨t, ht, hqt⟩ := hl q ((mem_iff q l).mpr hq)
      rw [mem_iff] at hqt
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with e | e
      · rw [e, hqa] at hqt
        exact Bool.false_ne_true hqt
      · rw [e, hqb] at hqt
        exact Bool.false_ne_true hqt

theorem pts (T : Finset (Fin 13)) (h : T.card ≤ 2) :
    (∀ p ∉ T, ∃ l : Fin 13, p ∈ singerLines3 l ∧ ∀ t ∈ T, t ∉ singerLines3 l) ∧
      ∃ l : Fin 13, ∀ t ∈ T, t ∈ singerLines3 l := by
  rcases card_cases T h with rfl | ⟨a, b, rfl⟩
  · exact ⟨fun p _ => ⟨p, (mem_iff p p).mpr (inc_self p), by simp⟩, ⟨0, by simp⟩⟩
  · refine ⟨fun p hp => ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
      obtain ⟨l, h1, h2, h3⟩ := dec_avoid a b p hp.1 hp.2
      refine ⟨l, (mem_iff _ _).mpr h1, ?_⟩
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rw [mem_iff]
      rcases ht with e | e
      · rw [e, h2]; decide
      · rw [e, h3]; decide
    · obtain ⟨l, h1, h2⟩ := dec_join a b
      refine ⟨l, ?_⟩
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rw [mem_iff]
      rcases ht with e | e
      · rw [e]; exact h1
      · rw [e]; exact h2

theorem len_inc (X Y : Finset (Fin 13)) : (incidenceInput X Y).length = 26 := by
  simp [incidenceInput]

theorem gd_pt (X Y : Finset (Fin 13)) (p : Fin 13) :
    (incidenceInput X Y).getD p.val false = decide (p ∈ X) := by
  unfold incidenceInput
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp), List.getElem?_ofFn]
  simp [p.isLt]

theorem gd_ln (X Y : Finset (Fin 13)) (l : Fin 13) :
    (incidenceInput X Y).getD (13 + l.val) false = decide (l ∈ Y) := by
  unfold incidenceInput
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.length_ofFn,
    Nat.add_sub_cancel_left, List.getElem?_ofFn]
  simp [l.isLt]

theorem gd_big (X Y : Finset (Fin 13)) (j : ℕ) (h : 26 ≤ j) :
    (incidenceInput X Y).getD j false = false :=
  getD_big _ _ _ (by rw [len_inc]; exact h)

theorem idx_cases (j : ℕ) :
    (∃ p : Fin 13, j = p.val) ∨ (∃ l : Fin 13, j = 13 + l.val) ∨ 26 ≤ j := by
  by_cases h1 : j < 13
  · exact Or.inl ⟨⟨j, h1⟩, rfl⟩
  · by_cases h2 : j < 26
    · refine Or.inr (Or.inl ⟨⟨j - 13, by omega⟩, ?_⟩)
      show j = 13 + (j - 13)
      omega
    · exact Or.inr (Or.inr (by omega))

end PEqualNP.Outside.L_meta_8895
open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.HeptadCover PEqualNP.Outside.L_meta_8895 in
theorem PEqualNP.Outside.L_meta_8895 : have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Finset (Fin (13 : ℕ))), (∀ x3 ∉ x2, ∃ x5 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2, x3 ∈ PEqualNP.HeptadCover.singerLines3 x5) → ¬PEqualNP.GenericRejection.InNoLine PEqualNP.HeptadCover.singerLines3 x2 ∨ ¬PEqualNP.GenericRejection.InNoPencil PEqualNP.HeptadCover.singerLines3 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2) → x1.eval (PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2)) = Bool.false; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x2 → x1 x2 → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (2 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (2 : ℕ) → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x2 := by
  dsimp only
  intro C hM hR hF hD
  have hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h := (hM g hg).1
    simpa using h
  have hsupp : ∀ (marked : Finset ℕ) (x : List Bool), C.eval x = true →
      ∃ S : Finset ℕ, S.card ≤ (C.lineDegrees x.length marked).getD C.output 0 ∧
        ∀ y : List Bool, y.length = x.length →
          (∀ j, x.getD j false = true → (j ∉ marked ∨ j ∈ S) → y.getD j false = true) →
          C.eval y = true := by
    intro marked x hx
    exact support marked x C.gates hAO C.output hx
  unfold ComputesIncidence
  intro X Y
  unfold incidenceFun
  by_cases hinc : ∃ p ∈ X, ∃ l ∈ Y, p ∈ singerLines3 l
  · rw [decide_eq_true hinc]
    obtain ⟨p, hp, l, hl, hpl⟩ := hinc
    have h1 := hR l p hpl
    obtain ⟨S, -, hy⟩ := hsupp ∅ _ h1
    apply hy _ ((len_inc _ _).trans (len_inc _ _).symm)
    intro j hj _
    rcases idx_cases j with ⟨q, rfl⟩ | ⟨m, rfl⟩ | hbig
    · rw [gd_pt] at hj ⊢
      simp only [decide_eq_true_eq, Finset.mem_singleton] at hj ⊢
      rw [hj]; exact hp
    · rw [gd_ln] at hj ⊢
      simp only [decide_eq_true_eq, Finset.mem_singleton] at hj ⊢
      rw [hj]; exact hl
    · rw [gd_big _ _ _ hbig] at hj
      exact absurd hj (by decide)
  · rw [decide_eq_false hinc]
    by_contra hne
    have htrue : C.eval (incidenceInput X Y) = true := by simpa using hne
    rcases hD with hL | hP
    · obtain ⟨S, hS, hy⟩ := hsupp (Finset.Ico 13 26) _ htrue
      have hS2 : S.card ≤ 2 := by
        have h2 : (C.lineDegrees (incidenceInput X Y).length (Finset.Ico 13 26)).getD C.output 0 ≤ 2 := by
          rw [len_inc]; exact hL
        omega
      have hY'2 : (Y.filter (fun l => 13 + l.val ∈ S)).card ≤ 2 := by
        refine le_trans (Finset.card_le_card_of_injOn (fun l : Fin 13 => 13 + l.val) ?_ ?_) hS2
        · intro l hl
          exact (Finset.mem_filter.mp hl).2
        · intro a _ b _ h
          exact Fin.ext (by simpa using h)
      obtain ⟨v, hv⟩ := pencil _ hY'2
      have hmiss : ∀ l ∈ Y.filter (fun l => 13 + l.val ∈ S), l ∈ missLines singerLines3
          (Finset.univ.filter (fun p : Fin 13 => ∀ l ∈ Y.filter (fun l => 13 + l.val ∈ S), p ∉ singerLines3 l)) := by
        intro l hl
        simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Finset.disjoint_left]
        intro a ha haZ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at haZ
        exact haZ l (Finset.mem_filter.mp hl) ha
      have hfalse := hF (Finset.univ.filter (fun p : Fin 13 => ∀ l ∈ Y.filter (fun l => 13 + l.val ∈ S), p ∉ singerLines3 l)) (by
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hq
        obtain ⟨l, hl, hql⟩ := hq
        exact ⟨l, hmiss l (Finset.mem_filter.mpr hl), hql⟩) (by
        right
        intro hnp
        apply hnp v
        intro l hl
        apply hv l
        intro q hq
        simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and] at hl
        have hqZ := Finset.disjoint_left.mp hl hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hqZ
        obtain ⟨t, ht, hqt⟩ := hqZ
        exact ⟨t, Finset.mem_filter.mpr ht, hqt⟩)
      have htrue2 : C.eval (incidenceInput (Finset.univ.filter (fun p : Fin 13 => ∀ l ∈ Y.filter (fun l => 13 + l.val ∈ S), p ∉ singerLines3 l)) (missLines singerLines3 (Finset.univ.filter (fun p : Fin 13 => ∀ l ∈ Y.filter (fun l => 13 + l.val ∈ S), p ∉ singerLines3 l)))) = true := hy _ ((len_inc _ _).trans (len_inc _ _).symm) (by
        intro j hj hjS
        rcases idx_cases j with ⟨q, rfl⟩ | ⟨m, rfl⟩ | hbig
        · rw [gd_pt] at hj ⊢
          simp only [decide_eq_true_eq] at hj ⊢
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro l hl hql
          exact hinc ⟨q, hj, l, hl.1, hql⟩
        · rw [gd_ln] at hj ⊢
          simp only [decide_eq_true_eq] at hj ⊢
          apply hmiss
          rw [Finset.mem_filter]
          refine ⟨hj, ?_⟩
          rcases hjS with h | h
          · exfalso
            apply h
            have := m.isLt
            rw [Finset.mem_Ico]
            omega
          · exact h
        · rw [gd_big _ _ _ hbig] at hj
          exact absurd hj (by decide))
      rw [hfalse] at htrue2
      exact absurd htrue2 (by decide)
    · obtain ⟨S, hS, hy⟩ := hsupp (Finset.range 13) _ htrue
      have hS2 : S.card ≤ 2 := by
        have h2 : (C.lineDegrees (incidenceInput X Y).length (Finset.range 13)).getD C.output 0 ≤ 2 := by
          rw [len_inc]; exact hP
        omega
      have hX'2 : (X.filter (fun p => p.val ∈ S)).card ≤ 2 := by
        refine le_trans (Finset.card_le_card_of_injOn (fun p : Fin 13 => p.val) ?_ ?_) hS2
        · intro p hp
          exact (Finset.mem_filter.mp hp).2
        · intro a _ b _ h
          exact Fin.ext h
      obtain ⟨hmaxT, hlineT⟩ := pts _ hX'2
      have hfalse := hF (X.filter (fun p => p.val ∈ S)) (by
        intro q hq
        obtain ⟨l, hql, hl⟩ := hmaxT q hq
        refine ⟨l, ?_, hql⟩
        simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Finset.disjoint_left]
        intro a ha haX
        exact hl a haX ha) (by
        left
        obtain ⟨l, hl⟩ := hlineT
        intro hnl
        exact hnl l (fun t ht => hl t ht))
      have htrue2 : C.eval (incidenceInput (X.filter (fun p => p.val ∈ S)) (missLines singerLines3 (X.filter (fun p => p.val ∈ S)))) = true := hy _ ((len_inc _ _).trans (len_inc _ _).symm) (by
        intro j hj hjS
        rcases idx_cases j with ⟨q, rfl⟩ | ⟨m, rfl⟩ | hbig
        · rw [gd_pt] at hj ⊢
          simp only [decide_eq_true_eq] at hj ⊢
          rw [Finset.mem_filter]
          refine ⟨hj, ?_⟩
          rcases hjS with h | h
          · exact absurd (Finset.mem_range.mpr q.isLt) h
          · exact h
        · rw [gd_ln] at hj ⊢
          simp only [decide_eq_true_eq] at hj ⊢
          simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [Finset.disjoint_left]
          intro a ha haX
          exact hinc ⟨a, (Finset.mem_filter.mp haX).1, m, hj, ha⟩
        · rw [gd_big _ _ _ hbig] at hj
          exact absurd hj (by decide))
      rw [hfalse] at htrue2
      exact absurd htrue2 (by decide)
