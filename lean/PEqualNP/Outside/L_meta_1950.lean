import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1950

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem ifp {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

theorem ifn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) {a b : α} :
    (if c then a else b) = b := by simp [h]

theorem difp {α : Type} {c : Prop} [Decidable c] (h : c) {a : c → α} {b : ¬ c → α} :
    dite c a b = a h := by simp [h]

theorem difn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) {a : c → α} {b : ¬ c → α} :
    dite c a b = b h := by simp [h]

def fd {α : Type} (F : Gate → List α → α) (X : List α) (gs : List Gate) : List α :=
  gs.foldl (fun w g => w ++ [F g w]) X

theorem fd_len {α : Type} (F : Gate → List α → α) :
    ∀ (gs : List Gate) (X : List α), (fd F X gs).length = X.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro X; simp [fd]
  | cons g gs ih =>
    intro X
    have := ih (X ++ [F g X])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp
    omega

theorem fd_pre {α : Type} (F : Gate → List α → α) :
    ∀ (gs : List Gate) (X : List α) (i : ℕ), i < X.length → (fd F X gs)[i]? = X[i]? := by
  intro gs
  induction gs with
  | nil => intro X i _; simp [fd]
  | cons g gs ih =>
    intro X i hi
    have := ih (X ++ [F g X]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this, List.getElem?_append_left hi]

theorem fd_app {α : Type} (F : Gate → List α → α) (X : List α) (gs hs : List Gate) :
    fd F X (gs ++ hs) = fd F (fd F X gs) hs := by
  simp [fd, List.foldl_append]

theorem fd_gate' {α : Type} (F : Gate → List α → α) (dflt : α)
    (hF : ∀ (g : Gate) (w w' : List α),
      (∀ i ∈ g.inputs, w.getD i dflt = w'.getD i dflt) → F g w = F g w')
    (as : List Gate) (g : Gate) (bs : List Gate) (X : List α)
    (hrb : ∀ i ∈ g.inputs, i < X.length + as.length) :
    (fd F X (as ++ g :: bs)).getD (X.length + as.length) dflt = F g (fd F X (as ++ g :: bs)) := by
  have e1 : fd F X (as ++ g :: bs) = fd F (fd F X as ++ [F g (fd F X as)]) bs := by
    simp [fd, List.foldl_append]
  have hWl : (fd F X as).length = X.length + as.length := fd_len F as X
  have key : ∀ i, i < (fd F X as).length + 1 →
      (fd F X (as ++ g :: bs))[i]? = (fd F X as ++ [F g (fd F X as)])[i]? := by
    intro i hi
    rw [e1]
    exact fd_pre F bs _ i (by simp; omega)
  rw [List.getD_eq_getElem?_getD, key _ (by omega), ← hWl,
    List.getElem?_append_right (le_refl _)]
  simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  apply hF
  intro i hi
  have hi' := hrb i hi
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, key i (by omega),
    List.getElem?_append_left (by omega)]

theorem fd_gate {α : Type} (F : Gate → List α → α) (dflt : α)
    (hF : ∀ (g : Gate) (w w' : List α),
      (∀ i ∈ g.inputs, w.getD i dflt = w'.getD i dflt) → F g w = F g w')
    (gs : List Gate) (X : List α) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < X.length + j) :
    (fd F X gs).getD (X.length + j) dflt = F (gs.getD j ⟨GateOp.or, []⟩) (fd F X gs) := by
  have h1 : gs.take j ++ gs[j] :: gs.drop (j + 1) = gs := by
    rw [← List.drop_eq_getElem_cons hj]
    exact List.take_append_drop j gs
  have h2 : gs.getD j ⟨GateOp.or, []⟩ = gs[j] := by
    simp [List.getD_eq_getElem?_getD, hj]
  have h3 := fd_gate' F dflt hF (gs.take j) gs[j] (gs.drop (j + 1)) X (by
    rw [List.length_take, min_eq_left hj.le, ← h2]
    exact hrb)
  rw [h1, List.length_take, min_eq_left hj.le] at h3
  rw [h2]
  exact h3

def stpF : Gate → List Bool → Bool :=
  fun g w => g.op.eval (g.inputs.map fun i => w.getD i false)

theorem stpF_congr (g : Gate) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = w'.getD i false) : stpF g w = stpF g w' := by
  unfold stpF
  rw [List.map_congr_left h]

theorem ld_congr (g : Gate) (w w' : List ℕ)
    (h : ∀ i ∈ g.inputs, w.getD i 0 = w'.getD i 0) : g.lineDegree w = g.lineDegree w' := by
  unfold Gate.lineDegree
  rw [List.map_congr_left h]
theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

def V (C : Circuit) (X : List Bool) (w : ℕ) : Bool := (C.wires X).getD w false

def D (K : ℕ) (M : Finset ℕ) (C : Circuit) (w : ℕ) : ℕ := (C.lineDegrees K M).getD w 0

theorem wires_fd (C : Circuit) (X : List Bool) : C.wires X = fd stpF X C.gates := rfl
theorem V_gate (K : ℕ) (C : Circuit) (hrb : ReadsBack K C) (X : List Bool) (hX : X.length = K)
    (j : ℕ) (hj : j < C.gates.length) :
    V C X (K + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (V C X)) := by
  have h := fd_gate stpF false stpF_congr C.gates X j hj (by
    intro i hi
    have := hrb j hj i hi
    rw [hX]
    exact this)
  rw [hX] at h
  exact h

theorem D_len (K : ℕ) (M : Finset ℕ) (C : Circuit) :
    (C.lineDegrees K M).length = K + C.gates.length := by
  have := fd_len Gate.lineDegree C.gates
    ((List.range K).map fun i => if i ∈ M then 1 else 0)
  simpa [fd, Circuit.lineDegrees] using this

theorem D_in (K : ℕ) (M : Finset ℕ) (C : Circuit) (w : ℕ) (hw : w < K) :
    D K M C w = if w ∈ M then 1 else 0 := by
  unfold D Circuit.lineDegrees
  have := fd_pre Gate.lineDegree C.gates
    ((List.range K).map fun i => if i ∈ M then 1 else 0) w
    (by simpa using hw)
  unfold fd at this
  rw [List.getD_eq_getElem?_getD, this]
  simp [hw]

theorem D_out (K : ℕ) (M : Finset ℕ) (C : Circuit) (w : ℕ) (hw : K + C.gates.length ≤ w) :
    D K M C w = 0 := by
  unfold D
  have hl := D_len K M C
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

theorem foldr_max_zero : ∀ (l : List ℕ), l.foldr max 0 = 0 ↔ ∀ a ∈ l, a = 0 := by
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    rw [← ih]
    omega

theorem D_zero_iff (K : ℕ) (M : Finset ℕ) (C : Circuit) (hrb : ReadsBack K C) (j : ℕ)
    (hj : j < C.gates.length) :
    D K M C (K + j) = 0 ↔ ∀ i ∈ (gateAt C j).inputs, D K M C i = 0 := by
  have h := fd_gate Gate.lineDegree 0 ld_congr C.gates
    ((List.range K).map fun i => if i ∈ M then 1 else 0) j hj (by
    intro i hi
    have := hrb j hj i hi
    simpa using this)
  simp only [List.length_map, List.length_range] at h
  have h' : D K M C (K + j) = (gateAt C j).lineDegree (C.lineDegrees K M) := h
  rw [h']
  unfold Gate.lineDegree
  split_ifs
  · rw [List.sum_eq_zero_iff]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rfl
  · rw [foldr_max_zero]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rfl
theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem _

def W (N : ℕ) (C : Circuit) (x y : Fin N → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn (Fin.append x y))).getD w false

def DL (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0

def DP (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.range N)).getD w 0
theorem W_gate (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C) (x y : Fin N → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    W N C x y (N + N + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (W N C x y)) :=
  V_gate (N + N) C hrb _ (by simp) j hj

abbrev gok (N : ℕ) (C : Circuit) (x : Fin N → Bool) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.or ∨
    ∃ i ∈ (gateAt C j).inputs, DL N C i = 0 ∧ W N C x (fun _ => false) i = true

abbrev E (N : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ f : Fin C.gates.length, b = N + N + f.val ∧ a ∈ (C.gates.get f).inputs

abbrev cone (N : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (0 < DP N C (N + N + j) ∧ 0 < DL N C (N + N + j)) ∧
    Relation.ReflTransGen (E N C) (N + N + j) C.output

abbrev step (N : ℕ) (C : Circuit) (x : Fin N → Bool) (j3 j4 : ℕ) : Prop :=
  cone N C j4 ∧ N + N + j3 ∈ (gateAt C j4).inputs ∧ gok N C x j4

abbrev lvx (N : ℕ) (C : Circuit) (x : Fin N → Bool) (j : ℕ) : Prop :=
  cone N C j ∧ gok N C x j ∧ ∃ j6 : ℕ, N + N + j6 = C.output ∧ Relation.ReflTransGen (step N C x) j j6

abbrev slot (N : ℕ) (C : Circuit) (h j : ℕ) : Prop :=
  cone N C j ∧ h ∈ (gateAt C j).inputs ∧ DP N C h = 0

theorem two_cases (l : List ℕ) (hl : l.length = 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : ∀ k ∈ l, k = a ∨ k = b := by
  rcases l with _ | ⟨u, _ | ⟨v, _ | ⟨w, t⟩⟩⟩
  · simp at hl
  · simp at hl
  · intro k hk
    simp at ha hb hk
    omega
  · have h := hl
    rw [List.length_cons, List.length_cons, List.length_cons] at h
    omega

theorem mixed_gate (N : ℕ) (C : Circuit) (w : ℕ) (h1 : 0 < DP N C w) (h2 : 0 < DL N C w) :
    ∃ j < C.gates.length, w = N + N + j := by
  change 0 < D (N + N) (Finset.range N) C w at h1
  change 0 < D (N + N) (Finset.Ico N (N + N)) C w at h2
  by_cases hw : w < N + N
  · exfalso
    by_cases hw2 : w < N
    · have h := D_in (N + N) (Finset.Ico N (N + N)) C w hw
      rw [ifn (by simp only [Finset.mem_Ico]; omega)] at h
      omega
    · have h := D_in (N + N) (Finset.range N) C w hw
      rw [ifn (by simp only [Finset.mem_range]; omega)] at h
      omega
  · by_cases hw2 : w < N + N + C.gates.length
    · exact ⟨w - (N + N), by omega, by omega⟩
    · have h := D_out (N + N) (Finset.range N) C w (by omega)
      omega

theorem fwd (N : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C)
    (hI : ∀ (w : ℕ) (xa xb ya yb : Fin N → Bool),
      (DL N C w = 0 → W N C xa ya w = W N C xa yb w) ∧
      (DP N C w = 0 → W N C xa ya w = W N C xb ya w) ∧
      W N C (fun _ => false) (fun _ => false) w = false)
    (x y : Fin N → Bool) (c : ℕ) (hc : c < C.gates.length) (hg : gok N C x c) (u : ℕ)
    (hu : u ∈ (gateAt C c).inputs) (hDu : 0 < DL N C u) (hW : W N C x y u = true) :
    W N C x y (N + N + c) = true := by
  rw [W_gate N C hrb x y c hc]
  have hgc := hC _ (gateAt_mem C c hc)
  rcases hgc.1 with hop | hop
  · rw [ev_and _ _ hop]
    rcases hg with hor | ⟨i, hi, hDi, hWi⟩
    · rw [hop] at hor
      cases hor
    · have hne : i ≠ u := by
        intro e
        subst e
        omega
      intro k hk
      rcases two_cases _ hgc.2 i u hi hu hne k hk with e | e
      · rw [e, (hI i x x y (fun _ => false)).1 hDi]
        exact hWi
      · rw [e]
        exact hW
  · rw [ev_or _ _ hop]
    exact ⟨u, hu, hW⟩

theorem chain (N : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C)
    (hI : ∀ (w : ℕ) (xa xb ya yb : Fin N → Bool),
      (DL N C w = 0 → W N C xa ya w = W N C xa yb w) ∧
      (DP N C w = 0 → W N C xa ya w = W N C xb ya w) ∧
      W N C (fun _ => false) (fun _ => false) w = false)
    (x y : Fin N → Bool) (j j' : ℕ) (hr : Relation.ReflTransGen (step N C x) j j')
    (hj : cone N C j) (hW : W N C x y (N + N + j) = true) :
    cone N C j' ∧ W N C x y (N + N + j') = true := by
  induction hr with
  | refl => exact ⟨hj, hW⟩
  | tail _ hbc ih =>
    obtain ⟨hcb, hWb⟩ := ih
    obtain ⟨hcc, hin, hg⟩ := hbc
    exact ⟨hcc, fwd N C hC hrb hI x y _ hcc.1 hg _ hin hcb.2.1.2 hWb⟩

theorem part2 (N : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C)
    (hI : ∀ (w : ℕ) (xa xb ya yb : Fin N → Bool),
      (DL N C w = 0 → W N C xa ya w = W N C xa yb w) ∧
      (DP N C w = 0 → W N C xa ya w = W N C xb ya w) ∧
      W N C (fun _ => false) (fun _ => false) w = false)
    (x y : Fin N → Bool) (h j : ℕ) (hs : slot N C h j) (hl : lvx N C x j)
    (hh : W N C (fun _ => false) y h = true) : W N C x y C.output = true := by
  obtain ⟨hcj, hin, hDP⟩ := hs
  obtain ⟨_, hg, j6, hj6, hr⟩ := hl
  have hWh : W N C x y h = true := by
    rw [← (hI h (fun _ => false) x y y).2.1 hDP]
    exact hh
  have hDL : 0 < DL N C h := by
    by_contra hc
    have h0 : DL N C h = 0 := by omega
    have e1 := (hI h x x y (fun _ => false)).1 h0
    have e2 := (hI h x (fun _ => false) (fun _ => false) (fun _ => false)).2.1 hDP
    have e3 := (hI h x x y y).2.2
    rw [e1, e2, e3] at hWh
    cases hWh
  have hWj := fwd N C hC hrb hI x y j hcj.1 hg h hin hDL hWh
  have := (chain N C hC hrb hI x y j j6 hr hcj hWj).2
  rw [hj6] at this
  exact this

theorem back (N : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C)
    (hI : ∀ (w : ℕ) (xa xb ya yb : Fin N → Bool),
      (DL N C w = 0 → W N C xa ya w = W N C xa yb w) ∧
      (DP N C w = 0 → W N C xa ya w = W N C xb ya w) ∧
      W N C (fun _ => false) (fun _ => false) w = false)
    (hand : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, DL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, DP N C h = 0))
    (x y : Fin N → Bool) (jo : ℕ) (hjo : N + N + jo = C.output) :
    ∀ j, cone N C j → Relation.ReflTransGen (step N C x) j jo → W N C x y (N + N + j) = true →
      W N C x (fun _ => false) (N + N + j) = false →
      ∃ h j', slot N C h j' ∧ lvx N C x j' ∧ W N C (fun _ => false) y h = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hc hr hW hW0
  have hj := hc.1
  have hgc := hC _ (gateAt_mem C j hj)
  have key : gok N C x j ∧ ∃ u ∈ (gateAt C j).inputs,
      W N C x y u = true ∧ W N C x (fun _ => false) u = false := by
    rw [W_gate N C hrb x y j hj] at hW
    rw [W_gate N C hrb x _ j hj] at hW0
    rcases hgc.1 with hop | hop
    · rw [ev_and _ _ hop] at hW
      rcases hand j hj hop with ⟨i, hi, hDi⟩ | hall
      · have hWi : W N C x (fun _ => false) i = true := by
          rw [← (hI i x x y (fun _ => false)).1 hDi]
          exact hW i hi
        refine ⟨Or.inr ⟨i, hi, hDi, hWi⟩, ?_⟩
        have hex : ∃ u ∈ (gateAt C j).inputs, W N C x (fun _ => false) u = false := by
          by_contra hne
          push_neg at hne
          have := (ev_and _ (W N C x (fun _ => false)) hop).mpr
            (fun k hk => by simpa using hne k hk)
          rw [hW0] at this
          cases this
        obtain ⟨u, hu, hWu⟩ := hex
        exact ⟨u, hu, hW u hu, hWu⟩
      · exfalso
        have h1 := (D_zero_iff (N + N) (Finset.range N) C hrb j hj).mpr hall
        have h2 := hc.2.1.1
        change 0 < D (N + N) (Finset.range N) C (N + N + j) at h2
        omega
    · rw [ev_or _ _ hop] at hW
      obtain ⟨u, hu, hWu⟩ := hW
      refine ⟨Or.inl hop, u, hu, hWu, ?_⟩
      cases h : W N C x (fun _ => false) u
      · rfl
      · exfalso
        have : (gateAt C j).op.eval ((gateAt C j).inputs.map (W N C x (fun _ => false))) = true := by
          rw [ev_or _ _ hop]
          exact ⟨u, hu, h⟩
        rw [hW0] at this
        cases this
  obtain ⟨hg, u, hu, hWu, hWu0⟩ := key
  by_cases hDP : DP N C u = 0
  · refine ⟨u, j, ⟨hc, hu, hDP⟩, ⟨hc, hg, jo, hjo, hr⟩, ?_⟩
    rw [(hI u (fun _ => false) x y y).2.1 hDP]
    exact hWu
  · by_cases hDL : DL N C u = 0
    · exfalso
      rw [(hI u x x y (fun _ => false)).1 hDL, hWu0] at hWu
      cases hWu
    · obtain ⟨j', hj', rfl⟩ := mixed_gate N C u (by omega) (by omega)
      have hlt : j' < j := by
        have := hrb j hj _ hu
        omega
      have hget : C.gates.get ⟨j, hj⟩ = gateAt C j := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ hj]
        rfl
      have hc' : cone N C j' := by
        refine ⟨hj', ⟨by omega, by omega⟩, ?_⟩
        refine Relation.ReflTransGen.head (b := N + N + j)
          ⟨(by omega : N + N + j' < N + N + j), ⟨j, hj⟩, rfl, ?_⟩ hc.2.2
        rw [hget]
        exact hu
      exact ih j' hlt hc' (Relation.ReflTransGen.head ⟨hc, hu, hg⟩ hr) hWu hWu0

theorem part1 (N : ℕ) (C : Circuit)
    (hI : ∀ (w : ℕ) (xa xb ya yb : Fin N → Bool),
      (DL N C w = 0 → W N C xa ya w = W N C xa yb w) ∧
      (DP N C w = 0 → W N C xa ya w = W N C xb ya w) ∧
      W N C (fun _ => false) (fun _ => false) w = false)
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hedge : ∃ p w : Fin N, I p w)
    (htrue : ∀ p w : Fin N, I p w →
      W N C (fun a => decide (a = p)) (fun a => decide (a = w)) C.output = true)
    (hfalse : ∀ x y : Fin N → Bool, (Finset.univ.filter (fun l => y l = true)).card ≤ 1 →
      (¬ ∃ p w : Fin N, I p w ∧ x p = true ∧ y w = true) → W N C x y C.output = false) :
    ∃ jo, N + N + jo = C.output ∧ cone N C jo := by
  obtain ⟨p, w, hpw⟩ := hedge
  have h1 := htrue p w hpw
  have h2 := hfalse (fun a => decide (a = p)) (fun _ => false) (by simp) (by simp)
  have h3 := hfalse (fun _ => false) (fun a => decide (a = w))
    (Finset.card_le_one.mpr (fun a ha b hb => by
      simp at ha hb
      rw [ha, hb])) (by simp)
  have hDL : 0 < DL N C C.output := by
    by_contra hc
    rw [(hI C.output (fun a => decide (a = p)) (fun a => decide (a = p))
      (fun a => decide (a = w)) (fun _ => false)).1 (by omega), h2] at h1
    cases h1
  have hDP : 0 < DP N C C.output := by
    by_contra hc
    rw [(hI C.output (fun a => decide (a = p)) (fun _ => false)
      (fun a => decide (a = w)) (fun a => decide (a = w))).2.1 (by omega), h3] at h1
    cases h1
  obtain ⟨jo, hjo, he⟩ := mixed_gate N C _ hDP hDL
  refine ⟨jo, he.symm, hjo, ?_, ?_⟩
  · rw [← he]
    exact ⟨hDP, hDL⟩
  · rw [he]
    all_goals exact Relation.ReflTransGen.refl

theorem part4 (N : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C)
    (hI : ∀ (w : ℕ) (xa xb ya yb : Fin N → Bool),
      (DL N C w = 0 → W N C xa ya w = W N C xa yb w) ∧
      (DP N C w = 0 → W N C xa ya w = W N C xb ya w) ∧
      W N C (fun _ => false) (fun _ => false) w = false)
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hfalse : ∀ x y : Fin N → Bool, (Finset.univ.filter (fun l => y l = true)).card ≤ 1 →
      (¬ ∃ p w : Fin N, I p w ∧ x p = true ∧ y w = true) → W N C x y C.output = false)
    (h j : ℕ) (w : Fin N) (hs : slot N C h j)
    (hl : W N C (fun _ => false) (fun a => decide (a = w)) h = true)
    (hv : lvx N C (fun a => decide (¬ I a w)) j) : False := by
  have := part2 N C hC hrb hI _ _ h j hs hv hl
  rw [hfalse _ _ (Finset.card_le_one.mpr (fun a ha b hb => by
      simp at ha hb
      rw [ha, hb])) (by
    rintro ⟨p, w', hpw, hx, hy⟩
    simp at hx hy
    subst hy
    exact hx hpw)] at this
  cases this

theorem part5 (N : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C)
    (hI : ∀ (w : ℕ) (xa xb ya yb : Fin N → Bool),
      (DL N C w = 0 → W N C xa ya w = W N C xa yb w) ∧
      (DP N C w = 0 → W N C xa ya w = W N C xb ya w) ∧
      W N C (fun _ => false) (fun _ => false) w = false)
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hfalse : ∀ x y : Fin N → Bool, (Finset.univ.filter (fun l => y l = true)).card ≤ 1 →
      (¬ ∃ p w : Fin N, I p w ∧ x p = true ∧ y w = true) → W N C x y C.output = false)
    (h : ℕ) (p w : Fin N) (ha : ∃ j, slot N C h j ∧ lvx N C (fun a => decide (a = p)) j)
    (hl : W N C (fun _ => false) (fun a => decide (a = w)) h = true) : I p w := by
  obtain ⟨j, hs, hv⟩ := ha
  have := part2 N C hC hrb hI _ _ h j hs hv hl
  by_contra hn
  rw [hfalse _ _ (Finset.card_le_one.mpr (fun a ha b hb => by
      simp at ha hb
      rw [ha, hb])) (by
    rintro ⟨p', w', hpw, hx, hy⟩
    simp at hx hy
    subst hx
    subst hy
    exact hn hpw)] at this
  cases this

theorem part6 (N : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C)
    (hI : ∀ (w : ℕ) (xa xb ya yb : Fin N → Bool),
      (DL N C w = 0 → W N C xa ya w = W N C xa yb w) ∧
      (DP N C w = 0 → W N C xa ya w = W N C xb ya w) ∧
      W N C (fun _ => false) (fun _ => false) w = false)
    (hand : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, DL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, DP N C h = 0))
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (h4 : ∀ p p' w w' : Fin N, p ≠ p' → w ≠ w' → I p w → I p' w → I p w' → I p' w' → False)
    (htrue : ∀ p w : Fin N, I p w →
      W N C (fun a => decide (a = p)) (fun a => decide (a = w)) C.output = true)
    (hfalse : ∀ x y : Fin N → Bool, (Finset.univ.filter (fun l => y l = true)).card ≤ 1 →
      (¬ ∃ p w : Fin N, I p w ∧ x p = true ∧ y w = true) → W N C x y C.output = false)
    (jo : ℕ) (hjo : N + N + jo = C.output) (hco : cone N C jo) (p w : Fin N) (hpw : I p w) :
    (∃ h : ℕ, (∀ w7 : Fin N, W N C (fun _ => false) (fun a => decide (a = w7)) h = true ↔ w7 = w) ∧
        ∃ j, slot N C h j ∧ lvx N C (fun a => decide (a = p)) j) ∨
      (∃ h : ℕ, ((∃ w8 w9 : Fin N, w8 ≠ w9 ∧
          W N C (fun _ => false) (fun a => decide (a = w8)) h = true ∧
          W N C (fun _ => false) (fun a => decide (a = w9)) h = true) ∧
        ∀ p7 : Fin N, (∃ j, slot N C h j ∧ lvx N C (fun a => decide (a = p7)) j) ↔ p7 = p) ∧
        W N C (fun _ => false) (fun a => decide (a = w)) h = true) := by
  have hT := htrue p w hpw
  have hF0 := hfalse (fun a => decide (a = p)) (fun _ => false) (by simp) (by simp)
  obtain ⟨h, j, hs, hv, hh⟩ := back N C hC hrb hI hand (fun a => decide (a = p))
    (fun a => decide (a = w)) jo hjo jo hco Relation.ReflTransGen.refl
    (by rw [hjo]; exact hT) (by rw [hjo]; exact hF0)
  by_cases hone : ∀ w7 : Fin N, W N C (fun _ => false) (fun a => decide (a = w7)) h = true → w7 = w
  · left
    refine ⟨h, fun w7 => ⟨hone w7, fun e => ?_⟩, j, hs, hv⟩
    subst e
    exact hh
  · right
    push_neg at hone
    obtain ⟨w', hw', hne⟩ := hone
    refine ⟨h, ⟨⟨w', w, hne, hw', hh⟩, fun p7 => ⟨?_, ?_⟩⟩, hh⟩
    · rintro ⟨j7, hs7, hv7⟩
      by_contra hp
      have i1 := part5 N C hC hrb hI I hfalse h p7 w ⟨j7, hs7, hv7⟩ hh
      have i2 := part5 N C hC hrb hI I hfalse h p7 w' ⟨j7, hs7, hv7⟩ hw'
      have i3 := part5 N C hC hrb hI I hfalse h p w ⟨j, hs, hv⟩ hh
      have i4 := part5 N C hC hrb hI I hfalse h p w' ⟨j, hs, hv⟩ hw'
      exact h4 p p7 w w' (Ne.symm hp) (Ne.symm hne) i3 i1 i4 i2
    · rintro rfl
      exact ⟨j, hs, hv⟩

end PEqualNP.Outside.L_meta_1950

theorem PEqualNP.Outside.L_meta_1950 : (∀ (N21 : ℕ) (C21 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g21 ∈ C21.gates, (g21.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g21.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g21.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N21 + N21) C21 → (∀ j21 < C21.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i21 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD i21 0 = 0) ∨ (∀ h21b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21b 0 = 0)) → (∀ (w21 : ℕ) (xa21 xb21 ya21 yb21 : Fin N21 → Bool), ((C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xa21 yb21))).getD w21 false) ∧ ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xb21 ya21))).getD w21 false) ∧ (C21.wires (List.ofFn (Fin.append (fun u21 : Fin N21 => false) (fun u21a : Fin N21 => false)))).getD w21 false = false) ∧ (∀ w21a : ℕ, 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21a 0 → 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21a 0 → ∃ c21 : ℕ → (Fin N21 → Bool) → Bool, (∀ h21 : ℕ, Monotone (c21 h21)) ∧ ∀ x21 y21 : Fin N21 → Bool, ((C21.wires (List.ofFn (Fin.append x21 y21))).getD w21a false = true ↔ ((C21.wires (List.ofFn (Fin.append x21 (fun u21b : Fin N21 => false)))).getD w21a false = true ∨ ∃ h21a : ℕ, ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21a 0 = 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD h21a 0 ∧ ∃ j21a < C21.gates.length, h21a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21a).inputs ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD (N21 + N21 + j21a) 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD (N21 + N21 + j21a) 0) ∧ (C21.wires (List.ofFn (Fin.append (fun u21c : Fin N21 => false) y21))).getD h21a false = true ∧ c21 h21a x21 = true)))) → ∀ (N231 : ℕ) (I231 : Fin N231 → Fin N231 → Prop) [DecidableRel I231] (C231 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g231 ∈ C231.gates, (g231.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g231.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g231.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N231 + N231) C231) → (∀ j231 < C231.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231 0 = 0) ∨ (∀ h231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231 0 = 0)) → (∀ p231 p231x1 w231 w231x1 : Fin N231, p231 ≠ p231x1 → w231 ≠ w231x1 → I231 p231 w231 → I231 p231x1 w231 → I231 p231 w231x1 → I231 p231x1 w231x1 → False) → (∃ p231x2 w231x2 : Fin N231, I231 p231x2 w231x2) → (∀ p231x3 w231x3 : Fin N231, I231 p231x3 w231x3 → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append (fun a231 : Fin N231 => decide (a231 = p231x3)) (fun a231x1 : Fin N231 => decide (a231x1 = w231x3))) = true) → (∀ x231 y231 : Fin N231 → Bool, (Finset.univ.filter (fun l231 : Fin N231 => y231 l231 = true)).card ≤ 1 → (¬ ∃ p231x4 w231x4 : Fin N231, I231 p231x4 w231x4 ∧ x231 p231x4 = true ∧ y231 w231x4 = true) → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231 y231) = false) → ∀ mixed231 : ℕ → Prop, mixed231 = (fun i231x1 : ℕ => 0 < (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD i231x1 0 ∧ 0 < (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x1 0) → ∀ cone231 : ℕ → Prop, cone231 = (fun j231x1 : ℕ => j231x1 < C231.gates.length ∧ mixed231 (N231 + N231 + j231x1) ∧ Relation.ReflTransGen (fun a231x2 b231 : ℕ => a231x2 < b231 ∧ ∃ f231 : Fin C231.gates.length, b231 = N231 + N231 + f231.val ∧ a231x2 ∈ (C231.gates.get f231).inputs) (N231 + N231 + j231x1) C231.output) → ∀ gok231 : (Fin N231 → Bool) → ℕ → Prop, gok231 = (fun (x231x1 : Fin N231 → Bool) (j231x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i231x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x2 0 = 0 ∧ (C231.wires (List.ofFn (Fin.append x231x1 (fun u231 : Fin N231 => false)))).getD i231x2 false = true) → ∀ step231 : (Fin N231 → Bool) → ℕ → ℕ → Prop, step231 = (fun (x231x2 : Fin N231 → Bool) (j231x3 j231x4 : ℕ) => cone231 j231x4 ∧ N231 + N231 + j231x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x4).inputs ∧ gok231 x231x2 j231x4) → ∀ lvx231 : (Fin N231 → Bool) → ℕ → Prop, lvx231 = (fun (x231x3 : Fin N231 → Bool) (j231x5 : ℕ) => cone231 j231x5 ∧ gok231 x231x3 j231x5 ∧ ∃ j231x6 : ℕ, N231 + N231 + j231x6 = C231.output ∧ Relation.ReflTransGen (step231 x231x3) j231x5 j231x6) → ∀ slot231 : ℕ → ℕ → Prop, slot231 = (fun h231x1 j231x7 : ℕ => cone231 j231x7 ∧ h231x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x7).inputs ∧ (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231x1 0 = 0) → ∀ ap231 : ℕ → Fin N231 → Prop, ap231 = (fun (h231x2 : ℕ) (p231x5 : Fin N231) => ∃ j231x8 : ℕ, slot231 h231x2 j231x8 ∧ lvx231 (fun a231x3 : Fin N231 => decide (a231x3 = p231x5)) j231x8) → ∀ lh231 : ℕ → Fin N231 → Prop, lh231 = (fun (h231x3 : ℕ) (w231x5 : Fin N231) => (C231.wires (List.ofFn (Fin.append (fun u231x1 : Fin N231 => false) (fun a231x4 : Fin N231 => decide (a231x4 = w231x5))))).getD h231x3 false = true) → ∀ lpw231 : ℕ → Fin N231 → Prop, lpw231 = (fun (h231x4 : ℕ) (w231x6 : Fin N231) => ∀ w231x7 : Fin N231, lh231 h231x4 w231x7 ↔ w231x7 = w231x6) → ∀ ppw231 : ℕ → Fin N231 → Prop, ppw231 = (fun (h231x5 : ℕ) (p231x6 : Fin N231) => (∃ w231x8 w231x9 : Fin N231, w231x8 ≠ w231x9 ∧ lh231 h231x5 w231x8 ∧ lh231 h231x5 w231x9) ∧ ∀ p231x7 : Fin N231, ap231 h231x5 p231x7 ↔ p231x7 = p231x6) → ∀ lps231 : Fin N231 → Fin N231 → Prop, lps231 = (fun p231x8 w231x10 : Fin N231 => ∃ h231x6 : ℕ, lpw231 h231x6 w231x10 ∧ ap231 h231x6 p231x8) → ∀ pps231 : Fin N231 → Fin N231 → Prop, pps231 = (fun p231x9 w231x11 : Fin N231 => ∃ h231x7 : ℕ, ppw231 h231x7 p231x9 ∧ lh231 h231x7 w231x11) → (∃ j231x9 : ℕ, N231 + N231 + j231x9 = C231.output ∧ cone231 j231x9) ∧ (∀ (x231x4 y231x1 : Fin N231 → Bool) (h231x8 j231x10 : ℕ), slot231 h231x8 j231x10 → lvx231 x231x4 j231x10 → (C231.wires (List.ofFn (Fin.append (fun u231x2 : Fin N231 => false) y231x1))).getD h231x8 false = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x4 y231x1) = true) ∧ (∀ x231x5 y231x2 : Fin N231 → Bool, PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 y231x2) = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 (fun u231x3 : Fin N231 => false)) = false → ∃ h231x9 j231x11 : ℕ, slot231 h231x9 j231x11 ∧ lvx231 x231x5 j231x11 ∧ (C231.wires (List.ofFn (Fin.append (fun u231x4 : Fin N231 => false) y231x2))).getD h231x9 false = true) ∧ (∀ (h231x10 j231x12 : ℕ) (w231x12 : Fin N231), slot231 h231x10 j231x12 → lh231 h231x10 w231x12 → ¬ lvx231 (fun a231x5 : Fin N231 => decide (¬ I231 a231x5 w231x12)) j231x12) ∧ (∀ (h231x11 : ℕ) (p231x10 w231x13 : Fin N231), ap231 h231x11 p231x10 → lh231 h231x11 w231x13 → I231 p231x10 w231x13) ∧ (∀ p231x11 w231x14 : Fin N231, I231 p231x11 w231x14 → lps231 p231x11 w231x14 ∨ pps231 p231x11 w231x14) := by
  intro hF N I instI C hC hand h4 hedge htrue hfalse mixed hmixed cone hcone gok hgok step hstep lvx hlvx slot hslot ap hap lh hlh lpw hlpw ppw hppw lps hlps pps hpps
  subst hmixed hcone hgok hstep hlvx hslot hap hlh hlpw hppw hlps hpps
  have hI := (hF N C hC.1 hC.2 hand).1
  obtain ⟨jo, hjo, hco⟩ := PEqualNP.Outside.L_meta_1950.part1 N C hI I hedge htrue hfalse
  refine ⟨⟨jo, hjo, hco⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y h j hs hv hh
    exact PEqualNP.Outside.L_meta_1950.part2 N C hC.1 hC.2 hI x y h j hs hv hh
  · intro x y h1 h2
    exact PEqualNP.Outside.L_meta_1950.back N C hC.1 hC.2 hI hand x y jo hjo jo hco
      Relation.ReflTransGen.refl (by rw [hjo]; exact h1) (by rw [hjo]; exact h2)
  · intro h j w hs hl hv
    exact PEqualNP.Outside.L_meta_1950.part4 N C hC.1 hC.2 hI I hfalse h j w hs hl hv
  · intro h p w ha hl
    exact PEqualNP.Outside.L_meta_1950.part5 N C hC.1 hC.2 hI I hfalse h p w ha hl
  · intro p w hpw
    exact PEqualNP.Outside.L_meta_1950.part6 N C hC.1 hC.2 hI hand I h4 htrue hfalse jo hjo hco p w hpw
