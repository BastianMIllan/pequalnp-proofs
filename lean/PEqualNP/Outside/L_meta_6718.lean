import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6718
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem coneSuffix (n : Nat) (gs : List Gate) (cs : List (List Nat)) :
    ∃ t, gs.foldl (coneStep n) cs=cs++t ∧ t.length=gs.length := by
  induction gs generalizing cs with
  | nil => exact ⟨[],by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t,ht,hl⟩ := ih (coneStep n cs g)
    rw [List.foldl_cons,ht]
    unfold coneStep
    exact ⟨_,List.append_assoc _ _ _,by simp [hl]⟩

theorem inheritCone (C : Circuit) (n j a k : Nat) (hj : j<C.gates.length) (ha : a<j)
    (reads : n+a ∈ (gateAt C j).inputs) (whereK : k=a ∨ InCone n C k a) : InCone n C k j := by
  let cs := (C.gates.take j).foldl (coneStep n) []
  obtain ⟨t,ht,hl⟩ := coneSuffix n (C.gates.take j) []
  have len : cs.length=j := by simp [cs,ht,hl,List.length_take,Nat.min_eq_left hj.le]
  let g := gateAt C j
  let anc := (g.inputs.filter (fun w => decide (n≤w ∧ w<n+cs.length))).flatMap (fun w => (w-n)::cs.getD (w-n) [])
  have list : C.gates=(C.gates.take j++[g])++C.gates.drop (j+1) := by
    calc C.gates = C.gates.take (j+1)++C.gates.drop (j+1) := (List.take_append_drop _ _).symm
         _ = _ := by rw [List.take_succ_eq_append_getElem hj,show g=C.gates[j] from List.getD_eq_getElem _ _ hj]
  obtain ⟨rest,hr,_⟩ := coneSuffix n (C.gates.drop (j+1)) (coneStep n cs g)
  have shape : cones n C=(cs++[anc])++rest := by
    unfold cones
    conv_lhs => rw [list,List.foldl_append,List.foldl_append]
    exact hr
  have hk : k=a ∨ k∈cs.getD a [] := by
    rcases whereK with h|h
    · exact Or.inl h
    · right;unfold InCone at h
      rw [shape,List.getD_append _ _ _ _ (by simp [len];omega),List.getD_append _ _ _ _ (by omega)] at h
      exact h
  have member : k∈anc := by
    apply List.mem_flatMap.mpr
    refine ⟨n+a,List.mem_filter.mpr ⟨reads,by simp [len,ha]⟩,?_⟩
    simpa using hk
  unfold InCone
  rw [shape,List.getD_append _ _ _ _ (by simp [len])]
  simpa [←len] using member

variable {n : Nat}

def bit (C : Circuit) (w : Nat) (u v : Fin n) := val C (pairInput u v) w
def mixed (C : Circuit) (w : Nat) (p q : Fin n) := bit C w p q=true ∧ bit C w p p=false ∧ bit C w q q=false
def cross (C : Circuit) (j : Nat) (p q : Fin n) := (gateAt C j).op=.and ∧
  ∃ b : Fin 2, bit C (opnd C j b) p p=true ∧ bit C (opnd C j (1-b)) q q=true

theorem arity (C : Circuit) (ao : IsAO2 n C) (j : Nat) (hj : j<C.gates.length) :
    ∃ a b, (gateAt C j).inputs=[a,b] := by
  have mem : gateAt C j∈C.gates := by rw [gateAt,List.getD_eq_getElem _ _ hj];exact List.getElem_mem _
  have ar := ao.2.2 _ mem
  rcases e : (gateAt C j).inputs with _|⟨a,_|⟨b,t⟩⟩ <;> simp_all

theorem stepValue (C : Circuit) (ao : IsAO2 n C) (j a b : Nat) (hj : j<C.gates.length)
    (ins : (gateAt C j).inputs=[a,b]) (u v : Fin n) :
    bit C (n+j) u v=(gateAt C j).op.eval [bit C a u v,bit C b u v] := by
  have slot : C.gates[j]?=some (gateAt C j) := by rw [gateAt,List.getD_eq_getElem _ _ hj,List.getElem?_eq_getElem hj]
  have la := ao.2.1 j hj a (by simp [ins])
  have lb := ao.2.1 j hj b (by simp [ins])
  unfold bit;rw [val_gate C _ slot,ins];simp [operand,la,lb]

theorem flags : ∀ a b c d : Bool, (a && b)=false → (c && d)=false →
    ¬(a=false ∧ c=false) → ¬(b=false ∧ d=false) → (a=true ∧ d=true) ∨ (b=true ∧ c=true) := by decide

theorem findCross (C : Circuit) (ao : IsAO2 n C) (p q : Fin n) (w : Nat) (m : mixed C w p q) :
    ∃ j, w=n+j ∧ ∃ k, (k=j ∨ InCone n C k j) ∧ cross C k p q := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    obtain ⟨on,leftOff,rightOff⟩ := m
    by_cases raw : w<n
    · let i : Fin n := ⟨w,raw⟩
      have get (u v : Fin n) : bit C w u v=pairInput u v i := val_input C _ i
      rw [get] at on leftOff rightOff
      simp_all [pairInput]
    have valid : w-n<C.gates.length := by
      by_contra! big
      exact Bool.noConfusion ((val_beyond C (pairInput p q) (by omega : n+C.gates.length≤w)).symm.trans on)
    let j := w-n
    have hj : j<C.gates.length := valid
    have index : w=n+j := by dsimp [j];omega
    obtain ⟨a,b,ins⟩ := arity C ao j hj
    let g := gateAt C j
    have mem : g∈C.gates := by change C.gates.getD j _ ∈ _;rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
    have step (u v : Fin n) : bit C w u v=g.op.eval [bit C a u v,bit C b u v] := index ▸ stepValue C ao j a b hj ins u v
    have lower (r : Nat) (hr : r∈g.inputs) : r<w := index ▸ ao.2.1 j hj r hr
    have pass (r : Nat) (hr : r∈g.inputs) (good : mixed C r p q) : ∃ k, (k=j ∨ InCone n C k j) ∧ cross C k p q := by
      have earlier := lower r hr
      obtain ⟨i,ei,k,hk,hcross⟩ := ih r earlier good
      exact ⟨k,Or.inr (inheritCone C n j i k hj (by omega) (ei ▸ hr) hk),hcross⟩
    refine ⟨j,index,?_⟩
    have ha : a∈g.inputs := by change a∈(gateAt C j).inputs;simp [ins]
    have hb : b∈g.inputs := by change b∈(gateAt C j).inputs;simp [ins]
    rcases ao.1 g mem with kind|kind
    · have AND (u v : Fin n) : bit C w u v=(bit C a u v && bit C b u v) := by rw [step,kind];simp [GateOp.eval]
      rw [AND,Bool.and_eq_true] at on
      by_cases leftM : mixed C a p q
      · exact pass a ha leftM
      by_cases rightM : mixed C b p q
      · exact pass b hb rightM
      have signs := flags _ _ _ _ ((AND p p).symm.trans leftOff) ((AND q q).symm.trans rightOff)
        (fun h => leftM ⟨on.1,h⟩) (fun h => rightM ⟨on.2,h⟩)
      refine ⟨j,Or.inl rfl,kind,?_⟩
      rcases signs with s|s
      · exact ⟨0,by simpa [opnd,ins] using s⟩
      · exact ⟨1,by simpa [opnd,ins] using s⟩
    · have OR (u v : Fin n) : bit C w u v=(bit C a u v || bit C b u v) := by rw [step,kind];simp [GateOp.eval]
      rw [OR,Bool.or_eq_true] at on
      rw [OR,Bool.or_eq_false_iff] at leftOff rightOff
      rcases on with h|h
      · exact pass a ha ⟨h,leftOff.1,rightOff.1⟩
      · exact pass b hb ⟨h,leftOff.2,rightOff.2⟩

theorem andLive (C : Circuit) (k : Nat) (h : (gateAt C k).op = .and) : k < C.gates.length := by
  by_contra! hk
  change (C.gates.getD k _).op=.and at h
  rw [List.getD_eq_default _ _ hk] at h
  contradiction

end PEqualNP.Outside.L_meta_6718

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_6718

theorem PEqualNP.Outside.L_meta_6718 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → ∀ (x4 x5 : Fin x1), ∀ x6 < x2.gates.length, PEqualNP.EdgeOwnership.gateVal x1 x2 x6 (PEqualNP.EdgeOwnership.pairInput x4 x5) = Bool.true → PEqualNP.EdgeOwnership.gateVal x1 x2 x6 (PEqualNP.EdgeOwnership.pairInput x4 x4) = Bool.false → PEqualNP.EdgeOwnership.gateVal x1 x2 x6 (PEqualNP.EdgeOwnership.pairInput x5 x5) = Bool.false → ∃ x11 < x2.gates.length, PEqualNP.SplitCount.InConeOrSelf x1 x2 x11 x6 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x12 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal x1 x2 (PEqualNP.TopForm.opnd x2 x11 x12) (PEqualNP.EdgeOwnership.pairInput x4 x4) = Bool.true ∧ PEqualNP.CleanedNonEdge.wireVal x1 x2 (PEqualNP.TopForm.opnd x2 x11 ((1 : Fin (2 : ℕ)) - x12)) (PEqualNP.EdgeOwnership.pairInput x5 x5) = Bool.true := by
  intro n C ao p q j _ on offP offQ
  obtain ⟨j', idx, k, hk, kind, b, hb1, hb2⟩ :=
    findCross C ao p q (n+j) ⟨on, offP, offQ⟩
  have hjj : j' = j := by omega
  subst hjj
  exact ⟨k, andLive C k kind, hk, kind, b, hb1, hb2⟩
