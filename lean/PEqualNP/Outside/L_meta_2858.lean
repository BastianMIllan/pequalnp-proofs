import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2858

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

-- the simulation relation: b at most a, a at most b or hv
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

theorem fin_bool (a b hv : Bool) (hs : R hv a b) (hb : hv = true → a = true) :
    (b || hv) = a := by
  unfold R at hs
  cases a <;> cases b <;> cases hv <;> simp_all

def ren (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩

theorem sim (hv : Bool) (n m p : ℕ) (hp : p < n + m) (B : List Gate)
    (hB : ∀ g ∈ B, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ U U' : List Bool, U.length = U'.length + 1 → n + m < U.length →
    (∀ i, R hv (U.getD i false) (U'.getD (eraseRedirect n m p i) false)) →
    ∀ i, R hv ((B.foldl stepW U).getD i false)
      (((B.map (ren n m p)).foldl stepW U').getD (eraseRedirect n m p i) false) := by
  induction B with
  | nil => intro U U' _ _ h; simpa using h
  | cons g B ih =>
    intro U U' hlen hnm hinv
    simp only [List.map_cons, List.foldl_cons]
    have hg := hB g (List.mem_cons_self ..)
    have hB' : ∀ g ∈ B, g.op = GateOp.and ∨ g.op = GateOp.or :=
      fun g' hg' => hB g' (List.mem_cons_of_mem _ hg')
    apply ih hB' (stepW U g) (stepW U' (ren n m p g))
    · simp [stepW]; omega
    · simp [stepW]; omega
    · intro i
      have hgate : R hv (g.op.eval (g.inputs.map fun i => U.getD i false))
          ((ren n m p g).op.eval ((ren n m p g).inputs.map fun i => U'.getD i false)) := by
        simp only [ren, List.map_map]
        exact R_gate hv g.op hg _ _ hinv g.inputs
      rcases lt_trichotomy i U.length with hi | hi | hi
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

theorem main (n : ℕ) (C C' : Circuit) (hM : Monotone2 C) (hR : ReadsBack n C)
    (hout : C.output < n + C.gates.length) (hL : Lift n C C') :
    Monotone2 C' ∧ ReadsBack n C' ∧ C'.size = C.size ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  obtain ⟨m, hm, p, hp, h, hh, hnh, hg, hbelow, rfl⟩ := hL
  have hE : eraseGate n C m p =
      { gates := C.gates.take m ++ (C.gates.drop (m + 1)).map (ren n m p)
        output := eraseRedirect n m p C.output } := by
    simp only [eraseGate, if_pos hm]; rfl
  have hgm : ∃ gm : Gate, C.gates[m]? = some gm ∧ gm.op = GateOp.or ∧
      (gm.inputs = [p, h] ∨ gm.inputs = [h, p]) := by
    rcases hg with hg | hg
    · exact ⟨_, hg, rfl, Or.inl rfl⟩
    · exact ⟨_, hg, rfl, Or.inr rfl⟩
  obtain ⟨gm, hgm, hgmop, hgmin⟩ := hgm
  have hlenE : (C.gates.take m ++ (C.gates.drop (m + 1)).map (ren n m p)).length =
      C.gates.length - 1 := by
    simp; omega
  have hfout : eraseRedirect n m p C.output < n + (C.gates.length - 1) := by
    unfold eraseRedirect; split_ifs <;> omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- form
    intro g hgmem
    simp only [liftAt, hE, List.mem_append, List.mem_map, List.mem_singleton] at hgmem
    rcases hgmem with (hgmem | ⟨g0, hg0, rfl⟩) | rfl
    · exact hM g (List.mem_of_mem_take hgmem)
    · have := hM g0 (List.mem_of_mem_drop hg0)
      simpa [ren] using this
    · simp
  · -- reads back
    have key : ∀ j g, (liftAt n C m p h).gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j := by
      intro j g hj i hi
      simp only [liftAt, hE] at hj
      rw [List.getElem?_append] at hj
      split_ifs at hj with h1
      · rw [List.getElem?_append] at hj
        split_ifs at hj with h2
        · simp only [List.length_take] at h2
          rw [List.getElem?_take] at hj
          split_ifs at hj with h3
          · have hjl : j < C.gates.length := by omega
            have hga : gateAt C j = g := by
              rw [gateAt, List.getD_eq_getElem?_getD, hj]; rfl
            have := hR j hjl i (by rw [hga]; exact hi)
            exact this
        · simp only [List.length_take] at h2 h1 hj
          rw [List.getElem?_map, List.getElem?_drop] at hj
          cases hq : C.gates[m + 1 + (j - min m C.gates.length)]? with
          | none => rw [hq] at hj; simp at hj
          | some g0 =>
            rw [hq] at hj
            simp only [Option.map_some, Option.some.injEq] at hj
            subst hj
            simp only [ren, List.mem_map] at hi
            obtain ⟨i0, hi0, rfl⟩ := hi
            have hmin : min m C.gates.length = m := by omega
            rw [hmin] at hq
            have hidx : m + 1 + (j - m) = j + 1 := by omega
            rw [hidx] at hq
            have hjl : j + 1 < C.gates.length := by
              by_contra hc
              rw [List.getElem?_eq_none (by omega)] at hq
              simp at hq
            have hga : gateAt C (j + 1) = g0 := by
              rw [gateAt, List.getD_eq_getElem?_getD, hq]; rfl
            have := hR (j + 1) hjl i0 (by rw [hga]; exact hi0)
            unfold eraseRedirect; split_ifs <;> omega
      · rw [hlenE] at h1
        rw [List.getElem?_singleton] at hj
        split_ifs at hj with h4
        · simp only [Option.some.injEq] at hj
          subst hj
          rw [hlenE] at h4
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · omega
          · omega
    intro j hj i hi
    have hsome : (liftAt n C m p h).gates[j]? = some (gateAt (liftAt n C m p h) j) := by
      rw [gateAt, List.getD_eq_getElem _ _ hj, List.getElem?_eq_getElem hj]
    exact key j _ hsome i hi
  · -- size
    simp only [Circuit.size, liftAt, hE, List.length_append, List.length_singleton,
      List.length_take, List.length_map, List.length_drop]
    omega
  · -- value
    intro x
    set X := List.ofFn x with hX
    have hXl : X.length = n := by simp [hX]
    set V := (C.gates.take m).foldl stepW X with hV
    have hVl : V.length = n + m := by
      rw [hV, foldl_len, hXl]; simp; omega
    have hsplit : C.gates = C.gates.take m ++ gm :: C.gates.drop (m + 1) := by
      have h0 : C.gates[m] = gm := by
        rw [List.getElem?_eq_getElem hm] at hgm; exact Option.some.inj hgm
      conv_lhs => rw [← List.take_append_drop m C.gates]
      rw [List.drop_eq_getElem_cons hm, h0]
    have hW : C.wires X = (C.gates.drop (m + 1)).foldl stepW (stepW V gm) := by
      show C.gates.foldl stepW X = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hW' : (eraseGate n C m p).wires X =
        ((C.gates.drop (m + 1)).map (ren n m p)).foldl stepW V := by
      rw [hE]
      show (C.gates.take m ++ (C.gates.drop (m + 1)).map (ren n m p)).foldl stepW X = _
      rw [List.foldl_append]
    set hv := V.getD h false with hhv
    have hB : ∀ g ∈ C.gates.drop (m + 1), g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      have := (hM g (List.mem_of_mem_drop hg)).1
      simpa using this
    have hinit : ∀ i, R hv ((stepW V gm).getD i false) (V.getD (eraseRedirect n m p i) false) := by
      intro i
      rcases lt_trichotomy i (n + m) with hi | hi | hi
      · have hf : eraseRedirect n m p i = i := by
          unfold eraseRedirect; split_ifs <;> omega
        rw [hf]; simp only [stepW]
        rw [getD_app_lt _ _ _ _ (by omega)]
        exact R_refl _ _
      · have hf : eraseRedirect n m p i = p := by
          unfold eraseRedirect; simp [hi]
        rw [hf]; simp only [stepW]
        rw [hi, ← hVl, getD_app_len, hgmop]
        rcases hgmin with hin | hin <;> rw [hin] <;>
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
            Bool.or_false] <;> rw [← hhv] <;> unfold R <;>
          cases V.getD p false <;> cases hv <;> simp
      · have hf : eraseRedirect n m p i = i - 1 := by
          unfold eraseRedirect; split_ifs <;> omega
        rw [hf]; simp only [stepW]
        rw [getD_ge _ _ _ (by simp; omega), getD_ge _ _ _ (by omega)]
        exact R_ff hv
    have hsim := sim hv n m p hp (C.gates.drop (m + 1)) hB (stepW V gm) V
      (by simp [stepW]) (by simp [stepW]; omega) hinit C.output
    rw [← hW, ← hW'] at hsim
    have hWh : (C.wires X).getD h false = hv := by
      rw [hW, foldl_getD_lt _ _ _ (by simp [stepW]; omega)]
      simp only [stepW]
      rw [getD_app_lt _ _ _ _ (by omega)]
    have hW'h : ((eraseGate n C m p).wires X).getD h false = hv := by
      rw [hW', foldl_getD_lt _ _ _ (by omega)]
    have hEl : ((eraseGate n C m p).wires X).length = n + (eraseGate n C m p).gates.length := by
      show ((eraseGate n C m p).gates.foldl stepW X).length = _
      rw [foldl_len, hXl]
    have hev : (liftAt n C m p h).eval X =
        (((eraseGate n C m p).wires X).getD (eraseRedirect n m p C.output) false || hv) := by
      show ((liftAt n C m p h).gates.foldl stepW X).getD (liftAt n C m p h).output false = _
      simp only [liftAt]
      rw [List.foldl_append]
      show (stepW ((eraseGate n C m p).wires X) _).getD _ false = _
      simp only [stepW]
      rw [← hEl, getD_app_len]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
        Bool.or_false]
      rw [hW'h, hE]
    have hbel := hbelow x
    rw [← hX] at hbel
    rw [hWh] at hbel
    rw [hev]
    change _ = (C.wires X).getD C.output false
    change hv = true → (C.wires X).getD C.output false = true at hbel
    exact fin_bool _ _ _ hsim hbel

end PEqualNP.Outside.L_meta_2858

theorem PEqualNP.Outside.L_meta_2858 : ∀ (n : ℕ) (C C' : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → C.output < n + C.gates.length → PEqualNP.CircuitMoves.Lift n C C' → PEqualNP.MetaComplexity.Monotone2 C' ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C' ∧ C'.size = C.size ∧ ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro n C C' hM hR hout hL
  exact PEqualNP.Outside.L_meta_2858.main n C C' hM hR hout hL
