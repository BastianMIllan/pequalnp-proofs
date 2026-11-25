import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6917

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Generic evaluation of two-input gates over values of type a.
def gw {α : Type} (z : α) (ev : GateOp → α → α → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [ev g.op (w.getD (g.inputs.getD 0 0) z) (w.getD (g.inputs.getD 1 0) z)])
    init

theorem gw_snoc {α : Type} (z : α) (ev : GateOp → α → α → α) (gs : List Gate) (g : Gate)
    (init : List α) :
    gw z ev (gs ++ [g]) init = gw z ev gs init ++
      [ev g.op ((gw z ev gs init).getD (g.inputs.getD 0 0) z)
        ((gw z ev gs init).getD (g.inputs.getD 1 0) z)] := by
  simp only [gw, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem gw_length {α : Type} (z : α) (ev : GateOp → α → α → α) (gs : List Gate) (init : List α) :
    (gw z ev gs init).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [gw]
  | append_singleton gs g ih =>
    rw [gw_snoc]
    simp only [List.length_append, List.length_singleton]
    omega

-- The same evaluation, with the wire number v forced to z.
def gwv {α : Type} (z : α) (ev : GateOp → α → α → α) (v : ℕ) (gs : List Gate) (init : List α) :
    List α :=
  gs.foldl (fun w g => w ++ [if w.length = v then z else
    ev g.op (w.getD (g.inputs.getD 0 0) z) (w.getD (g.inputs.getD 1 0) z)]) init

theorem gwv_snoc {α : Type} (z : α) (ev : GateOp → α → α → α) (v : ℕ) (gs : List Gate) (g : Gate)
    (init : List α) :
    gwv z ev v (gs ++ [g]) init = gwv z ev v gs init ++
      [if (gwv z ev v gs init).length = v then z else
        ev g.op ((gwv z ev v gs init).getD (g.inputs.getD 0 0) z)
          ((gwv z ev v gs init).getD (g.inputs.getD 1 0) z)] := by
  unfold gwv
  rw [List.foldl_append]
  rfl

theorem gwv_length {α : Type} (z : α) (ev : GateOp → α → α → α) (v : ℕ) (gs : List Gate)
    (init : List α) : (gwv z ev v gs init).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [gwv]
  | append_singleton gs g ih =>
    rw [gwv_snoc]
    simp only [List.length_append, List.length_singleton]
    omega

theorem getD_snoc {α : Type} (l : List α) (x d : α) (i : ℕ) :
    (l ++ [x]).getD i d = if i < l.length then l.getD i d else if i = l.length then x else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem getD_ge {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) : l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; simp

-- Constant propagation of the forced wire v.
def initMap (n : ℕ) : List (Option ℕ) := (List.range n).map some

def pstep (n : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) : List Gate × List (Option ℕ) :=
  match g.op, s.2.getD (g.inputs.getD 0 0) none, s.2.getD (g.inputs.getD 1 0) none with
  | GateOp.and, some a, some b => (s.1 ++ [⟨g.op, [a, b]⟩], s.2 ++ [some (n + s.1.length)])
  | GateOp.and, _, _ => (s.1, s.2 ++ [none])
  | _, some a, some b => (s.1 ++ [⟨g.op, [a, b]⟩], s.2 ++ [some (n + s.1.length)])
  | _, some a, none => (s.1, s.2 ++ [some a])
  | _, none, some b => (s.1, s.2 ++ [some b])
  | _, none, none => (s.1, s.2 ++ [none])

def pstep' (n v : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) : List Gate × List (Option ℕ) :=
  if s.2.length = v then (s.1, s.2 ++ [none]) else pstep n s g

def proc' (n v : ℕ) (gs : List Gate) : List Gate × List (Option ℕ) :=
  gs.foldl (pstep' n v) ([], initMap n)

theorem proc_snoc' (n v : ℕ) (gs : List Gate) (g : Gate) :
    proc' n v (gs ++ [g]) = pstep' n v (proc' n v gs) g := by
  simp only [proc', List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem initMap_getD (n i : ℕ) :
    (initMap n).getD i none = if i < n then some i else none := by
  unfold initMap
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · simp [h]
  · rw [List.getElem?_eq_none (by simp; omega)]; simp [h]

theorem pstep_cases (n : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) :
    (∃ a b, s.2.getD (g.inputs.getD 0 0) none = some a ∧ s.2.getD (g.inputs.getD 1 0) none = some b ∧
      pstep n s g = (s.1 ++ [⟨g.op, [a, b]⟩], s.2 ++ [some (n + s.1.length)])) ∨
    (pstep n s g = (s.1, s.2 ++ [none]) ∧
      (s.2.getD (g.inputs.getD 0 0) none = none ∨ s.2.getD (g.inputs.getD 1 0) none = none) ∧
      (g.op ≠ GateOp.and → s.2.getD (g.inputs.getD 0 0) none = none ∧
        s.2.getD (g.inputs.getD 1 0) none = none)) ∨
    (∃ a, g.op ≠ GateOp.and ∧ s.2.getD (g.inputs.getD 0 0) none = some a ∧
      s.2.getD (g.inputs.getD 1 0) none = none ∧ pstep n s g = (s.1, s.2 ++ [some a])) ∨
    (∃ b, g.op ≠ GateOp.and ∧ s.2.getD (g.inputs.getD 0 0) none = none ∧
      s.2.getD (g.inputs.getD 1 0) none = some b ∧ pstep n s g = (s.1, s.2 ++ [some b])) := by
  unfold pstep
  generalize s.2.getD (g.inputs.getD 0 0) none = ma
  generalize s.2.getD (g.inputs.getD 1 0) none = mb
  rcases g with ⟨op, ins⟩
  cases op <;> cases ma <;> cases mb <;> simp

theorem proc_struct' (n v : ℕ) (gs : List Gate) :
    (proc' n v gs).2.length = n + gs.length ∧
    (∀ i j, (proc' n v gs).2.getD i none = some j → j < n + (proc' n v gs).1.length) ∧
    (∀ k < (proc' n v gs).1.length, ∀ i ∈ ((proc' n v gs).1.getD k ⟨GateOp.or, []⟩).inputs,
      i < n + k) ∧
    (∀ g ∈ (proc' n v gs).1, (∃ g0 ∈ gs, g.op = g0.op) ∧ g.inputs.length = 2) ∧
    (proc' n v gs).1.length ≤ gs.length ∧
    (n ≤ v → v < n + gs.length → (proc' n v gs).1.length < gs.length) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [proc', initMap], ?_, by simp [proc'], by simp [proc'], by simp [proc'], ?_⟩
    · intro i j h
      simp only [proc', List.foldl_nil, initMap_getD] at h
      split_ifs at h with h1
      · simp at h; simp [proc']; omega
      all_goals simp at h
    · intro h1 h2
      exfalso
      simp at h2
      omega
  | append_singleton gs g ih =>
    obtain ⟨h1, h2, h3, h4, h6, h7⟩ := ih
    rw [proc_snoc']
    set s := proc' n v gs with hs
    by_cases hl : s.2.length = v
    · have he : pstep' n v s g = (s.1, s.2 ++ [none]) := by simp [pstep', hl]
      rw [he]
      refine ⟨by simp only [List.length_append, List.length_singleton]; omega, ?_, h3, ?_,
        by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      · intro i j hij
        rw [getD_snoc] at hij
        split_ifs at hij with c1 c2
        · exact h2 i j hij
        all_goals simp at hij
      · intro g' hg'
        obtain ⟨⟨g0, hg0, hop⟩, hlen⟩ := h4 g' hg'
        exact ⟨⟨g0, by simp [hg0], hop⟩, hlen⟩
      · intro _ _
        simp only [List.length_append, List.length_singleton]
        omega
    · have he0 : pstep' n v s g = pstep n s g := by simp [pstep', hl]
      rw [he0]
      rcases pstep_cases n s g with ⟨a, b, ha, hb, he⟩ | ⟨he, hn, _⟩ | ⟨a, _, ha, hb, he⟩ |
        ⟨b, _, ha, hb, he⟩ <;> rw [he] <;> simp only
      · refine ⟨by simp only [List.length_append, List.length_singleton]; omega, ?_, ?_, ?_,
          by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
        · intro i j hij
          rw [getD_snoc] at hij
          split_ifs at hij with c1 c2
          · have := h2 i j hij; simp; omega
          · simp at hij; simp; omega
        · intro k hk i hi
          simp only [List.length_append, List.length_singleton] at hk
          rw [getD_snoc] at hi
          split_ifs at hi with c1 c2
          · exact h3 k c1 i hi
          · subst c2
            simp at hi
            rcases hi with rfl | rfl
            · have := h2 _ _ ha; omega
            · have := h2 _ _ hb; omega
          · omega
        · intro g' hg'
          simp only [List.mem_append, List.mem_singleton] at hg'
          rcases hg' with hg' | rfl
          · obtain ⟨⟨g0, hg0, hop⟩, hlen⟩ := h4 g' hg'
            exact ⟨⟨g0, by simp [hg0], hop⟩, hlen⟩
          · exact ⟨⟨g, by simp, rfl⟩, by simp⟩
        · intro hnv hvlt
          simp only [List.length_append, List.length_singleton] at hvlt
          have := h7 hnv (by omega)
          simp only [List.length_append, List.length_singleton]
          omega
      all_goals
        refine ⟨by simp only [List.length_append, List.length_singleton]; omega, ?_, h3, ?_,
          by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
        · intro i j hij
          rw [getD_snoc] at hij
          split_ifs at hij with c1 c2
          all_goals first
            | exact h2 i j hij
            | (simp at hij; done)
            | (simp at hij; subst hij; exact h2 _ _ ha)
            | (simp at hij; subst hij; exact h2 _ _ hb)
        · intro g' hg'
          obtain ⟨⟨g0, hg0, hop⟩, hlen⟩ := h4 g' hg'
          exact ⟨⟨g0, by simp [hg0], hop⟩, hlen⟩
        · intro _ _
          simp only [List.length_append, List.length_singleton]
          omega

-- Every forced-evaluation wire is z or is copied by a new wire.
theorem proc_sem' {α : Type} (z : α) (ev : GateOp → α → α → α)
    (hA1 : ∀ y, ev GateOp.and z y = z) (hA2 : ∀ y, ev GateOp.and y z = z)
    (hO1 : ∀ op, op ≠ GateOp.and → ∀ y, ev op z y = y)
    (hO2 : ∀ op, op ≠ GateOp.and → ∀ y, ev op y z = y)
    (n v : ℕ) (init : List α) (hO : init.length = n) (gs : List Gate) :
    ∀ i, ((proc' n v gs).2.getD i none = none → (gwv z ev v gs init).getD i z = z) ∧
      (∀ j, (proc' n v gs).2.getD i none = some j →
        (gw z ev (proc' n v gs).1 init).getD j z = (gwv z ev v gs init).getD i z) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    simp only [proc', List.foldl_nil, initMap_getD]
    constructor
    · intro h
      split_ifs at h with c
      all_goals first
        | (simp at h; done)
        | (simp only [gwv, List.foldl_nil]; exact getD_ge _ _ _ (by omega))
    · intro j h
      split_ifs at h with c
      all_goals first
        | (simp at h; done)
        | (simp at h; subst h; simp [gw, gwv])
  | append_singleton gs g ih =>
    obtain ⟨h1, h2, -, -, -, -⟩ := proc_struct' n v gs
    rw [proc_snoc', gwv_snoc]
    set s := proc' n v gs with hs
    have hlo : (gwv z ev v gs init).length = s.2.length := by rw [gwv_length, h1, hO]
    have hln : (gw z ev s.1 init).length = n + s.1.length := by rw [gw_length, hO]
    have old : ∀ (e : Option ℕ) (ng : List Gate) (val : α), (∀ j, (∃ i, s.2.getD i none = some j) →
        (gw z ev ng init).getD j z = (gw z ev s.1 init).getD j z) →
        (e = none → val = z) →
        (∀ j, e = some j → (gw z ev ng init).getD j z = val) →
        ∀ i, ((s.2 ++ [e]).getD i none = none → (gwv z ev v gs init ++ [val]).getD i z = z) ∧
          (∀ j, (s.2 ++ [e]).getD i none = some j →
            (gw z ev ng init).getD j z = (gwv z ev v gs init ++ [val]).getD i z) := by
      intro e ng val hkeep hnone hsome i
      rw [getD_snoc, getD_snoc, hlo]
      split_ifs with c1 c2
      · exact ⟨(ih i).1, fun j hj => (hkeep j ⟨i, hj⟩).trans ((ih i).2 j hj)⟩
      · exact ⟨hnone, hsome⟩
      · exact ⟨fun _ => rfl, fun j hj => by simp at hj⟩
    have va := ih (g.inputs.getD 0 0)
    have vb := ih (g.inputs.getD 1 0)
    by_cases hl : s.2.length = v
    · have he : pstep' n v s g = (s.1, s.2 ++ [none]) := by simp [pstep', hl]
      rw [he, if_pos (hlo.trans hl)]
      exact old none s.1 z (fun j _ => rfl) (fun _ => rfl) (fun j hj => by simp at hj)
    · have he0 : pstep' n v s g = pstep n s g := by simp [pstep', hl]
      rw [he0, if_neg (by rw [hlo]; exact hl)]
      rcases pstep_cases n s g with ⟨a, b, ha, hb, he⟩ | ⟨he, hn, hn2⟩ | ⟨a, hop, ha, hb, he⟩ |
        ⟨b, hop, ha, hb, he⟩ <;> rw [he] <;> simp only
      · apply old
        · rintro j ⟨i, hi⟩
          rw [gw_snoc, getD_snoc, hln, if_pos (h2 i j hi)]
        · intro h; simp at h
        · intro j hj
          simp at hj; subst hj
          rw [gw_snoc, getD_snoc, hln, if_neg (by omega), if_pos rfl]
          simp only [List.getD_cons_zero, List.getD_cons_succ]
          rw [va.2 a ha, vb.2 b hb]
      · apply old
        · intro j _; rfl
        · intro _
          by_cases hop : g.op = GateOp.and
          · rcases hn with h | h
            · rw [va.1 h, hop, hA1]
            · rw [vb.1 h, hop, hA2]
          · obtain ⟨h, h'⟩ := hn2 hop
            rw [va.1 h, vb.1 h', hO1 _ hop]
        · intro j hj; simp at hj
      · apply old
        · intro j _; rfl
        · intro h; simp at h
        · intro j hj
          simp at hj; subst hj
          rw [vb.1 hb, hO2 _ hop, va.2 a ha]
      · apply old
        · intro j _; rfl
        · intro h; simp at h
        · intro j hj
          simp at hj; subst hj
          rw [va.1 ha, hO1 _ hop, vb.2 b hb]

def evB : GateOp → Bool → Bool → Bool
  | GateOp.and, a, b => a && b
  | _, a, b => a || b

theorem wires_eq (C : Circuit)
    (h : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x : List Bool) : C.wires x = gw false evB C.gates x := by
  unfold Circuit.wires gw
  generalize C.gates = gs at h
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]
    congr 1
    obtain ⟨hop, hl⟩ := h g (by simp)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
    rcases hop with hop | hop <;> simp [hop, hab, evB, GateOp.eval]

theorem wires_set (gs : List Gate)
    (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (n j : ℕ) (x : List Bool) (hx : x.length = n) :
    List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
      (gs.set j ⟨GateOp.or, []⟩) = gwv false evB (n + j) gs x := by
  induction gs using List.reverseRecOn with
  | nil => simp [gwv]
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => h g' (by simp [hg']))
    obtain ⟨hop, hl2⟩ := h g (by simp)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl2
    have hgl : (gwv false evB (n + j) gs x).length = n + gs.length := by rw [gwv_length, hx]
    rw [List.set_append, gwv_snoc, hgl]
    by_cases c1 : j < gs.length
    · rw [if_pos c1, List.foldl_append, ih', if_neg (show ¬ (n + gs.length = n + j) by omega)]
      rcases hop with hop | hop <;> simp [hop, hab, evB, GateOp.eval]
    · have hs : gs.set j ⟨GateOp.or, []⟩ = gs := List.set_eq_of_length_le (by omega)
      rw [hs] at ih'
      rw [if_neg c1, List.foldl_append, ih']
      by_cases c2 : j = gs.length
      · rw [if_pos (show n + gs.length = n + j by omega), show j - gs.length = 0 by omega]
        simp [GateOp.eval]
      · rw [if_neg (show ¬ (n + gs.length = n + j) by omega)]
        obtain ⟨k, hk⟩ : ∃ k, j - gs.length = k + 1 := ⟨j - gs.length - 1, by omega⟩
        rw [hk]
        rcases hop with hop | hop <;> simp [hop, hab, evB, GateOp.eval]

theorem eval5 (C : Circuit)
    (h : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (n j : ℕ) (x : List Bool) (hx : x.length = n) :
    Circuit.eval ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ x =
      (gwv false evB (n + j) C.gates x).getD C.output false := by
  unfold Circuit.eval
  rw [← wires_set C.gates h n j x hx]
  rfl

theorem evB_l1 (y : Bool) : evB GateOp.and false y = false := by simp [evB]
theorem evB_l2 (y : Bool) : evB GateOp.and y false = false := by simp [evB]
theorem evB_l3 (op : GateOp) (hop : op ≠ GateOp.and) (y : Bool) : evB op false y = y := by
  cases op <;> simp_all [evB]
theorem evB_l4 (op : GateOp) (hop : op ≠ GateOp.and) (y : Bool) : evB op y false = y := by
  cases op <;> simp_all [evB]
theorem evB_mono (op : GateOp) (a b a' b' : Bool) (e1 : a = true → a' = true)
    (e2 : b = true → b' = true) : evB op a b = true → evB op a' b' = true := by
  cases op <;> cases a <;> cases b <;> cases a' <;> cases b' <;> simp_all [evB]

theorem gwv_le (v : ℕ) (gs : List Gate) (init : List Bool) :
    ∀ i, (gwv false evB v gs init).getD i false = true →
      (gw false evB gs init).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; simpa [gw, gwv] using hi
  | append_singleton gs g ih =>
    intro i hi
    rw [gwv_snoc, getD_snoc, gwv_length] at hi
    rw [gw_snoc, getD_snoc, gw_length]
    split_ifs at hi ⊢ with c1 c2 c3
    all_goals first
      | exact ih i hi
      | (simp at hi; done)
      | exact evB_mono _ _ _ _ _ (ih _) (ih _) hi

end PEqualNP.Outside.L_meta_6917

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_6917 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x2.size),   PEqualNP.TopForm.IsAO2 x1 x2 →     have x5 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2.gates.set ↑x3 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit };     ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x6 ∧ x6.size < x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.circuitFun x1 x5 ∧ ∀ (x7 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x6 x7 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x7 = Bool.true := by
  intro n C j hAO
  dsimp only
  obtain ⟨hand, hrb, hlen⟩ := hAO
  have hgs : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hand g hg, hlen g hg⟩
  have hjl : (j : ℕ) < C.gates.length := j.isLt
  obtain ⟨h1, h2, h3, h4, h6, h7⟩ := L_meta_6917.proc_struct' n (n + j) C.gates
  have hng : ∀ g ∈ (L_meta_6917.proc' n (n + j) C.gates).1,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    obtain ⟨⟨g0, hg0, hop⟩, hl⟩ := h4 g hg
    exact ⟨hop ▸ (hgs g0 hg0).1, hl⟩
  let ng := (L_meta_6917.proc' n (n + j) C.gates).1
  let out' : ℕ := match (L_meta_6917.proc' n (n + j) C.gates).2.getD C.output none with
    | some o => o
    | none => n + ng.length
  let C' : Circuit := ⟨ng, out'⟩
  have key : ∀ (init : List Bool), init.length = n →
      (L_meta_6917.gw false L_meta_6917.evB ng init).getD out' false =
        (L_meta_6917.gwv false L_meta_6917.evB (n + j) C.gates init).getD C.output false := by
    intro init hO
    have hs := L_meta_6917.proc_sem' false L_meta_6917.evB L_meta_6917.evB_l1 L_meta_6917.evB_l2
      L_meta_6917.evB_l3 L_meta_6917.evB_l4 n (n + j) init hO C.gates C.output
    simp only [out']
    cases hm : (L_meta_6917.proc' n (n + j) C.gates).2.getD C.output none with
    | none =>
      rw [hs.1 hm]
      exact L_meta_6917.getD_ge _ _ _ (by rw [L_meta_6917.gw_length, hO])
    | some o => exact hs.2 o hm
  have hval : ∀ X : Fin n → Bool, circuitFun n C' X =
      circuitFun n ⟨C.gates.set (j : ℕ) ⟨GateOp.or, []⟩, C.output⟩ X := by
    intro X
    unfold circuitFun
    rw [L_meta_6917.eval5 C hgs n j (List.ofFn X) (by simp)]
    unfold Circuit.eval
    rw [L_meta_6917.wires_eq C' hng]
    exact key _ (by simp)
  refine ⟨C', ⟨fun g hg => (hng g hg).1, fun k hk i hi => h3 k hk i hi,
    fun g hg => (hng g hg).2⟩, h7 (by omega) (by omega), funext hval, ?_⟩
  intro X hx
  rw [hval] at hx
  unfold circuitFun at hx ⊢
  rw [L_meta_6917.eval5 C hgs n j (List.ofFn X) (by simp)] at hx
  unfold Circuit.eval
  rw [L_meta_6917.wires_eq C hgs]
  exact L_meta_6917.gwv_le _ _ _ _ hx
