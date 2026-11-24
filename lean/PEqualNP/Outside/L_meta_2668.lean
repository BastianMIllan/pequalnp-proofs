import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2668

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CircuitMoves

theorem getD_app_lt {α : Type} (l l' : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_len {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

theorem foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp only [stepW]
    exact getD_app_lt _ _ _ _ hi

-- the simulation relation: b at most a, and a at most b or hv
def R (hv a b : Bool) : Prop := (b = true → a = true) ∧ (a = true → b = true ∨ hv = true)

theorem R_refl (hv a : Bool) : R hv a a := ⟨id, fun h => Or.inl h⟩

theorem R_ff (hv : Bool) : R hv false false := R_refl hv false

theorem R_and (hv a b c d : Bool) (h1 : R hv a c) (h2 : R hv b d) : R hv (a && b) (c && d) := by
  unfold R at *
  cases a <;> cases b <;> cases c <;> cases d <;> cases hv <;> simp_all

theorem R_or (hv a b c d : Bool) (h1 : R hv a c) (h2 : R hv b d) : R hv (a || b) (c || d) := by
  unfold R at *
  cases a <;> cases b <;> cases c <;> cases d <;> cases hv <;> simp_all

theorem R_gate (hv : Bool) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (u v : ℕ → Bool) (huv : ∀ i, R hv (u i) (v i)) (ins : List ℕ) :
    R hv (op.eval (ins.map u)) (op.eval (ins.map v)) := by
  rcases hop with rfl | rfl
  · induction ins with
    | nil => exact R_refl _ _
    | cons j js ih =>
      simp only [GateOp.eval, List.map_cons, List.all_cons, id] at ih ⊢
      exact R_and _ _ _ _ _ (huv j) ih
  · induction ins with
    | nil => exact R_refl _ _
    | cons j js ih =>
      simp only [GateOp.eval, List.map_cons, List.any_cons, id] at ih ⊢
      exact R_or _ _ _ _ _ (huv j) ih

def ren (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩

-- simulation of the erased circuit, the redirect pointing past every wire
theorem sim2 (hv : Bool) (n m p : ℕ) (B : List Gate)
    (hB : ∀ g ∈ B, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ U U' : List Bool, U.length = U'.length + 1 → n + m < U.length →
    U'.length + B.length ≤ p →
    (∀ i, R hv (U.getD i false) (U'.getD (eraseRedirect n m p i) false)) →
    ∀ i, R hv ((B.foldl stepW U).getD i false)
      (((B.map (ren n m p)).foldl stepW U').getD (eraseRedirect n m p i) false) := by
  induction B with
  | nil => intro U U' _ _ _ h; simpa using h
  | cons g B ih =>
    intro U U' hlen hnm hp hinv
    simp only [List.map_cons, List.foldl_cons]
    simp only [List.length_cons] at hp
    have hg := hB g (List.mem_cons_self ..)
    have hB' : ∀ g ∈ B, g.op = GateOp.and ∨ g.op = GateOp.or :=
      fun g' hg' => hB g' (List.mem_cons_of_mem _ hg')
    apply ih hB' (stepW U g) (stepW U' (ren n m p g))
    · simp [stepW]; omega
    · simp [stepW]; omega
    · simp [stepW]; omega
    · intro i
      have hgate : R hv (g.op.eval (g.inputs.map fun i => U.getD i false))
          ((ren n m p g).op.eval ((ren n m p g).inputs.map fun i => U'.getD i false)) := by
        simp only [ren, List.map_map]
        exact R_gate hv g.op hg _ _ hinv g.inputs
      rcases lt_trichotomy i U.length with hi | hi | hi
      · by_cases hin : i = n + m
        · have hf : eraseRedirect n m p i = p := by
            unfold eraseRedirect; simp [hin]
          have h0 := hinv i
          rw [hf, getD_ge U' false p (by omega)] at h0
          simp only [stepW]
          rw [getD_app_lt _ _ _ _ hi, hf,
            getD_ge (U' ++ [(ren n m p g).op.eval ((ren n m p g).inputs.map fun i => U'.getD i false)])
              false p (by simp; omega)]
          exact h0
        · have hf : eraseRedirect n m p i < U'.length := by
            unfold eraseRedirect; split_ifs <;> omega
          simp only [stepW]
          rw [getD_app_lt _ _ _ _ hi, getD_app_lt _ _ _ _ hf]
          exact hinv i
      · have hf : eraseRedirect n m p i = U'.length := by
          unfold eraseRedirect; split_ifs <;> omega
        simp only [stepW]
        rw [hf, hi, getD_app_len, getD_app_len]
        exact hgate
      · have hf : U'.length + 1 ≤ eraseRedirect n m p i := by
          unfold eraseRedirect; split_ifs <;> omega
        simp only [stepW]
        rw [getD_ge _ _ _ (by simp; omega), getD_ge _ _ _ (by simp; omega)]
        exact R_ff hv

-- monotone gates are monotone
theorem le_gate (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (u v : ℕ → Bool) (huv : ∀ i, u i = true → v i = true) (ins : List ℕ) :
    op.eval (ins.map u) = true → op.eval (ins.map v) = true := by
  rcases hop with rfl | rfl
  · induction ins with
    | nil => simp [GateOp.eval]
    | cons j js ih =>
      simp only [GateOp.eval, List.map_cons, List.all_cons, id, Bool.and_eq_true] at ih ⊢
      intro h
      exact ⟨huv j h.1, ih h.2⟩
  · induction ins with
    | nil => simp [GateOp.eval]
    | cons j js ih =>
      simp only [GateOp.eval, List.map_cons, List.any_cons, id, Bool.or_eq_true] at ih ⊢
      intro h
      rcases h with h | h
      · exact Or.inl (huv j h)
      · exact Or.inr (ih h)

theorem mono_fold (B : List Gate) (hB : ∀ g ∈ B, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ U V : List Bool, U.length = V.length →
    (∀ i, U.getD i false = true → V.getD i false = true) →
    ∀ i, (B.foldl stepW U).getD i false = true → (B.foldl stepW V).getD i false = true := by
  induction B with
  | nil => intro U V _ h; simpa using h
  | cons g B ih =>
    intro U V hlen hinv
    simp only [List.foldl_cons]
    have hg := hB g (List.mem_cons_self ..)
    have hB' : ∀ g ∈ B, g.op = GateOp.and ∨ g.op = GateOp.or :=
      fun g' hg' => hB g' (List.mem_cons_of_mem _ hg')
    apply ih hB' (stepW U g) (stepW V g)
    · simp [stepW]; omega
    · intro i
      have hgate := le_gate g.op hg (fun i => U.getD i false) (fun i => V.getD i false) hinv
        g.inputs
      rcases lt_trichotomy i U.length with hi | hi | hi
      · simp only [stepW]
        rw [getD_app_lt _ _ _ _ hi, getD_app_lt V _ _ _ (by omega)]
        exact hinv i
      · simp only [stepW]
        rw [hi, getD_app_len, hlen, getD_app_len]
        exact hgate
      · simp only [stepW]
        rw [getD_ge (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)]) false i
          (by simp; omega)]
        intro h
        cases h

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · exact getD_ge _ _ _ (by simp; omega)

theorem fun_mono (n : ℕ) (D : Circuit) (hD : Monotone2 D) (x y : Fin n → Bool)
    (hxy : ∀ k, x k = true → y k = true) :
    circuitFun n D x = true → circuitFun n D y = true := by
  have hB : ∀ g ∈ D.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hD g hg).1
    simpa using this
  have hbase : ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
    intro i
    rw [ofFn_getD, ofFn_getD]
    split_ifs with h
    · exact hxy _
    · exact id
  exact mono_fold D.gates hB (List.ofFn x) (List.ofFn y) (by simp) hbase D.output

theorem erase_mono2 (n : ℕ) (C : Circuit) (m p : ℕ) (hM : Monotone2 C)
    (hm : m < C.gates.length) : Monotone2 (eraseGate n C m p) := by
  have hE : eraseGate n C m p =
      { gates := C.gates.take m ++ (C.gates.drop (m + 1)).map (ren n m p)
        output := eraseRedirect n m p C.output } := by
    simp only [eraseGate, if_pos hm]; rfl
  rw [hE]
  intro g hg
  simp only [List.mem_append, List.mem_map] at hg
  rcases hg with hg | ⟨g0, hg0, rfl⟩
  · exact hM g (List.mem_of_mem_take hg)
  · have := hM g0 (List.mem_of_mem_drop hg0)
    simpa [ren] using this

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hmin : IsMinimalMonoCircuit n C) (hf : circuitFun n C = graphFun G ∅)
    (m : ℕ) (hm : m < C.gates.length) :
    ∃ u v : Fin n, G.Adj u v ∧
      PEqualNP.EdgeOwnership.gateVal n C m (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
      circuitFun n (eraseGate n C m (n + C.gates.length))
        (PEqualNP.EdgeOwnership.pairInput u v) = false := by
  obtain ⟨C', hC'⟩ : ∃ C', C' = eraseGate n C m (n + C.gates.length) := ⟨_, rfl⟩
  rw [← hC']
  have hM := hmin.1
  have hE : C' =
      { gates := C.gates.take m ++ (C.gates.drop (m + 1)).map (ren n m (n + C.gates.length))
        output := eraseRedirect n m (n + C.gates.length) C.output } := by
    rw [hC']; simp only [eraseGate, if_pos hm]; rfl
  have hM' : Monotone2 C' := by
    rw [hC']; exact erase_mono2 n C m _ hM hm
  have hsize : C'.size + 1 = C.size := by
    rw [hE]
    simp only [Circuit.size, List.length_append, List.length_take, List.length_map,
      List.length_drop]
    omega
  have hB : ∀ g ∈ C.gates.drop (m + 1), g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hM g (List.mem_of_mem_drop hg)).1
    simpa using this
  have key : ∀ x : Fin n → Bool,
      R (PEqualNP.EdgeOwnership.gateVal n C m x) (circuitFun n C x) (circuitFun n C' x) := by
    intro x
    obtain ⟨X, hX⟩ : ∃ X, X = List.ofFn x := ⟨_, rfl⟩
    have hXl : X.length = n := by simp [hX]
    obtain ⟨V, hV⟩ : ∃ V, V = (C.gates.take m).foldl stepW X := ⟨_, rfl⟩
    have hVl : V.length = n + m := by
      rw [hV, foldl_len, hXl]; simp; omega
    have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
      conv_lhs => rw [← List.take_append_drop m C.gates]
      rw [List.drop_eq_getElem_cons hm]
    have hW : C.wires X = (C.gates.drop (m + 1)).foldl stepW (stepW V C.gates[m]) := by
      show C.gates.foldl stepW X = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons, hV]
    have hW' : C'.wires X =
        ((C.gates.drop (m + 1)).map (ren n m (n + C.gates.length))).foldl stepW V := by
      rw [hE]
      show (C.gates.take m ++ (C.gates.drop (m + 1)).map (ren n m (n + C.gates.length))).foldl
        stepW X = _
      rw [List.foldl_append, hV]
    obtain ⟨hv, hhv⟩ : ∃ hv, hv = (stepW V C.gates[m]).getD (n + m) false := ⟨_, rfl⟩
    have hgv : PEqualNP.EdgeOwnership.gateVal n C m x = hv := by
      show (C.wires (List.ofFn x)).getD (n + m) false = hv
      rw [← hX, hW, foldl_getD_lt (C.gates.drop (m + 1)) (stepW V C.gates[m]) (n + m)
        (by simp [stepW]; omega), hhv]
    have hinit : ∀ i, R hv ((stepW V C.gates[m]).getD i false)
        (V.getD (eraseRedirect n m (n + C.gates.length) i) false) := by
      intro i
      rcases lt_trichotomy i (n + m) with hi | hi | hi
      · have hf : eraseRedirect n m (n + C.gates.length) i = i := by
          unfold eraseRedirect; split_ifs <;> omega
        rw [hf]; simp only [stepW]
        rw [getD_app_lt _ _ _ _ (by omega)]
        exact R_refl _ _
      · have hf : eraseRedirect n m (n + C.gates.length) i = n + C.gates.length := by
          unfold eraseRedirect; simp [hi]
        rw [hf, getD_ge V false (n + C.gates.length) (by omega), hi, ← hhv]
        unfold R
        exact ⟨fun h => (by cases h), fun h => Or.inr h⟩
      · have hf : eraseRedirect n m (n + C.gates.length) i = i - 1 := by
          unfold eraseRedirect; split_ifs <;> omega
        rw [hf]; simp only [stepW]
        rw [getD_ge _ _ _ (by simp; omega), getD_ge V false (i - 1) (by omega)]
        exact R_ff hv
    have hsim := sim2 hv n m (n + C.gates.length) (C.gates.drop (m + 1)) hB
      (stepW V C.gates[m]) V (by simp [stepW]) (by simp [stepW]; omega)
      (by simp; omega) hinit C.output
    rw [← hW, ← hW'] at hsim
    rw [hgv]
    have e1 : circuitFun n C x = (C.wires X).getD C.output false := by
      rw [hX]; rfl
    have e2 : circuitFun n C' x = (C'.wires X).getD C'.output false := by
      rw [hX]; rfl
    have e3 : C'.output = eraseRedirect n m (n + C.gates.length) C.output := by
      rw [hE]
    rw [e1, e2, e3]
    exact hsim
  have hne : circuitFun n C' ≠ circuitFun n C := by
    intro h
    have := hmin.2 C' hM' h
    omega
  obtain ⟨x, hx⟩ : ∃ x, circuitFun n C' x ≠ circuitFun n C x := by
    by_contra hcon
    push_neg at hcon
    exact hne (funext hcon)
  have hRx : (circuitFun n C' x = true → circuitFun n C x = true) ∧
      (circuitFun n C x = true →
        circuitFun n C' x = true ∨ PEqualNP.EdgeOwnership.gateVal n C m x = true) := key x
  have hCx : circuitFun n C x = true := by
    by_contra hc
    have hc' : circuitFun n C x = false := by simpa using hc
    have h1 : circuitFun n C' x = true := by
      cases h : circuitFun n C' x
      · exact absurd (h.trans hc'.symm) hx
      · rfl
    exact hc (hRx.1 h1)
  have hC'x : circuitFun n C' x = false := by
    cases h : circuitFun n C' x
    · rfl
    · exact absurd (h.trans hCx.symm) hx
  have hg : graphFun G ∅ x = true := by
    rw [← hf]; exact hCx
  obtain ⟨u, v, huv, hxu, hxv⟩ : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    simpa [graphFun] using hg
  have hsub : ∀ k, PEqualNP.EdgeOwnership.pairInput u v k = true → x k = true := by
    intro k hk
    simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hk
    rcases hk with rfl | rfl
    · exact hxu
    · exact hxv
  have hC'y : circuitFun n C' (PEqualNP.EdgeOwnership.pairInput u v) = false := by
    cases h : circuitFun n C' (PEqualNP.EdgeOwnership.pairInput u v)
    · rfl
    · have := fun_mono n C' hM' _ x hsub h
      rw [hC'x] at this
      exact absurd this (by simp)
  have hCy : circuitFun n C (PEqualNP.EdgeOwnership.pairInput u v) = true := by
    rw [hf]
    simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
    right
    exact ⟨u, v, huv, by simp [PEqualNP.EdgeOwnership.pairInput],
      by simp [PEqualNP.EdgeOwnership.pairInput]⟩
  have hRy : (circuitFun n C' (PEqualNP.EdgeOwnership.pairInput u v) = true →
        circuitFun n C (PEqualNP.EdgeOwnership.pairInput u v) = true) ∧
      (circuitFun n C (PEqualNP.EdgeOwnership.pairInput u v) = true →
        circuitFun n C' (PEqualNP.EdgeOwnership.pairInput u v) = true ∨
          PEqualNP.EdgeOwnership.gateVal n C m (PEqualNP.EdgeOwnership.pairInput u v) = true) :=
    key _
  refine ⟨u, v, huv, ?_, hC'y⟩
  rcases hRy.2 hCy with h | h
  · rw [hC'y] at h; exact absurd h (by simp)
  · exact h

end PEqualNP.Outside.L_meta_2668

theorem PEqualNP.Outside.L_meta_2668 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∀ x7 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x7 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.MetaComplexity.circuitFun x1 (PEqualNP.CircuitMoves.eraseGate x1 x4 x7 (x1 + x4.gates.length)) (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.false := by
  intro x1 x2 x3 x4 hmin hf x7 hx7 _
  exact @PEqualNP.Outside.L_meta_2668.main x1 x2 x3 x4 hmin hf x7 hx7
