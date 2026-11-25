import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6037

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wf_append (pre post : List Gate) (w : List Bool) :
    wf (pre ++ post) w = wf post (wf pre w) := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

theorem legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

def sk (N i : ℕ) : ℕ := if i < N then i else i - 1

def rn (N a i : ℕ) : ℕ := if i < N then i else if i = N then a else i - 1

theorem getD_mid (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) :
    (A ++ b :: E).getD N false = b := by
  subst hN
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl A.length),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

theorem getD_sk (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (i : ℕ) (hi : i ≠ N) :
    (A ++ E).getD (sk N i) false = (A ++ b :: E).getD i false := by
  subst hN
  unfold sk
  by_cases h : i < A.length
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [if_neg h]
    have h1 : A.length ≤ i - 1 := by omega
    have h2 : A.length ≤ i := by omega
    have h3 : i - A.length = (i - 1 - A.length) + 1 := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
      List.getElem?_append_right h2]
    rw [h3, List.getElem?_cons_succ]

theorem getD_rn (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (a : ℕ) (ha : a < N)
    (hb : A.getD a false = b) (i : ℕ) :
    (A ++ E).getD (rn N a i) false = (A ++ b :: E).getD i false := by
  by_cases h : i = N
  · have e : rn N a N = a := by
      unfold rn
      rw [if_neg (lt_irrefl _), if_pos rfl]
    have ha' : a < A.length := by omega
    rw [h, getD_mid A E b N hN, e, ← hb]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left ha']
  · have e : rn N a i = sk N i := by
      unfold rn sk
      by_cases h' : i < N
      · rw [if_pos h', if_pos h']
      · rw [if_neg h', if_neg h, if_neg h']
    rw [e]
    exact getD_sk A E b N hN i h

theorem surg (T : Gate → Gate) (A : List Bool) (b : Bool) :
    ∀ (post : List Gate) (E : List Bool),
      (∀ h ∈ post, ∀ E' : List Bool,
        h.op.eval (h.inputs.map fun i => (A ++ b :: E').getD i false)
          = (T h).op.eval ((T h).inputs.map fun i => (A ++ E').getD i false)) →
      ∃ E2 : List Bool, wf post (A ++ b :: E) = A ++ b :: E2 ∧
        wf (post.map T) (A ++ E) = A ++ E2 := by
  intro post
  induction post with
  | nil => intro E _; exact ⟨E, rfl, rfl⟩
  | cons h post ih =>
    intro E hT
    have e := hT h (List.mem_cons.mpr (Or.inl rfl)) E
    obtain ⟨E2, h1, h2⟩ :=
      ih (E ++ [h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)])
        (fun h' hh' E' => hT h' (List.mem_cons.mpr (Or.inr hh')) E')
    refine ⟨E2, ?_, ?_⟩
    · rw [wf_cons, List.append_assoc, List.cons_append]
      exact h1
    · rw [List.map_cons, wf_cons, ← e, List.append_assoc]
      exact h2

theorem ev (pre post : List Gate) (g : Gate) (T : Gate → Gate) (x : List Bool) (b : Bool)
    (hb : g.op.eval (g.inputs.map fun i => (wf pre x).getD i false) = b)
    (hT : ∀ h ∈ post, ∀ E' : List Bool,
        h.op.eval (h.inputs.map fun i => (wf pre x ++ b :: E').getD i false)
          = (T h).op.eval ((T h).inputs.map fun i => (wf pre x ++ E').getD i false)) :
    ∃ E2 : List Bool, wf (pre ++ g :: post) x = wf pre x ++ b :: E2 ∧
      wf (pre ++ post.map T) x = wf pre x ++ E2 := by
  obtain ⟨E2, h1, h2⟩ := surg T (wf pre x) b post [] hT
  rw [List.append_nil] at h2
  refine ⟨E2, ?_, ?_⟩
  · rw [wf_append, wf_cons, hb]
    exact h1
  · rw [wf_append]
    exact h2

def Tc (N a : ℕ) (h : Gate) : Gate := ⟨h.op, h.inputs.map (rn N a)⟩

theorem sound_c (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (a : ℕ) (ha : a < N)
    (hb : A.getD a false = b) (h : Gate) :
    h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)
      = (Tc N a h).op.eval ((Tc N a h).inputs.map fun i => (A ++ E).getD i false) := by
  have e : (h.inputs.map (rn N a)).map (fun i => (A ++ E).getD i false)
      = h.inputs.map fun i => (A ++ b :: E).getD i false := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact getD_rn A E b N hN a ha hb i
  show h.op.eval _ = h.op.eval ((h.inputs.map (rn N a)).map fun i => (A ++ E).getD i false)
  rw [e]

theorem Tc_legal (N a : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tc N a h).op = GateOp.and ∨ (Tc N a h).op = GateOp.or) ∧ (Tc N a h).inputs.length ≤ 2 := by
  refine ⟨hl.1, ?_⟩
  show (h.inputs.map (rn N a)).length ≤ 2
  rw [List.length_map]
  exact hl.2

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (wf gs W1).getD i false = true → (wf gs W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; exact H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [wf_cons, wf_cons]
    apply ih _ _ (by simp [hl]) (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [getD_snoc, hl]
    split_ifs
    · rcases hop g (List.mem_cons.mpr (Or.inl rfl)) with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem wf_ext : ∀ (gs : List Gate) (w : List Bool), ∃ E : List Bool, wf gs w = w ++ E := by
  intro gs
  induction gs with
  | nil => intro w; exact ⟨[], (List.append_nil w).symm⟩
  | cons g gs ih =>
    intro w
    obtain ⟨E, hE⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: E, ?_⟩
    rw [wf_cons, hE, List.append_assoc]
    rfl

theorem old_wires (pre post : List Gate) (g : Gate) (x : List Bool) :
    ∃ E : List Bool, wf (pre ++ g :: post) x
      = wf pre x ++ g.op.eval (g.inputs.map fun i => (wf pre x).getD i false) :: E := by
  obtain ⟨E, hE⟩ := wf_ext post
    (wf pre x ++ [g.op.eval (g.inputs.map fun i => (wf pre x).getD i false)])
  refine ⟨E, ?_⟩
  rw [wf_append, wf_cons, hE, List.append_assoc]
  rfl

theorem getD_left (A L : List Bool) (a : ℕ) (ha : a < A.length) :
    (A ++ L).getD a false = A.getD a false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left ha]

theorem new_eval (pre post : List Gate) (N a o : ℕ) (x : List Bool)
    (hlen : (wf pre x).length = N) (ha : a < N) :
    (wf (pre ++ post.map (Tc N a)) x).getD (rn N a o) false
      = (wf post (wf pre x ++ [(wf pre x).getD a false])).getD o false := by
  obtain ⟨E2, h1, h2⟩ := surg (Tc N a) (wf pre x) ((wf pre x).getD a false) post []
    (fun h _ E' => sound_c (wf pre x) E' _ N hlen a ha rfl h)
  rw [List.append_nil] at h2
  have h1' : wf post (wf pre x ++ [(wf pre x).getD a false])
      = wf pre x ++ (wf pre x).getD a false :: E2 := h1
  rw [wf_append, h2, h1']
  exact getD_rn (wf pre x) E2 _ N hlen a ha rfl o

theorem swap_le (post : List Gate) (hop : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (A : List Bool) (u v : Bool) (huv : u = true → v = true) (o : ℕ)
    (h : (wf post (A ++ [u])).getD o false = true) :
    (wf post (A ++ [v])).getD o false = true := by
  refine mono post (A ++ [u]) (A ++ [v]) (by simp) hop ?_ o h
  intro i
  simp only [getD_snoc]
  split_ifs
  · exact huv
  · exact id

theorem er_eq (n m a : ℕ) : PEqualNP.CircuitMoves.eraseRedirect n m a = rn (n + m) a := by
  funext i
  unfold PEqualNP.CircuitMoves.eraseRedirect rn
  split_ifs <;> omega

theorem bridge (n : ℕ) (C : Circuit) (pre post : List Gate) (gj : Gate)
    (hC : C.gates = pre ++ gj :: post) (a : ℕ) :
    PEqualNP.CircuitMoves.eraseGate n C pre.length a
      = ⟨pre ++ post.map (Tc (n + pre.length) a), rn (n + pre.length) a C.output⟩ := by
  have hk : pre.length < C.gates.length := by rw [hC]; simp
  have h1 : C.gates.take pre.length = pre := by rw [hC]; simp
  have h2 : C.gates.drop (pre.length + 1) = post := by rw [hC]; simp
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [if_pos hk, h1, h2, er_eq]
  rfl

theorem asm (C : Circuit) (pre post : List Gate) (g : Gate)
    (hC : C.gates = pre ++ g :: post) (T : Gate → Gate) (o' : ℕ)
    (hmono : Monotone2 C)
    (hTm : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ((T h).op = GateOp.and ∨ (T h).op = GateOp.or) ∧ (T h).inputs.length ≤ 2) :
    Monotone2 ⟨pre ++ post.map T, o'⟩ ∧
      Circuit.size ⟨pre ++ post.map T, o'⟩ < C.size := by
  have legal := legal_of C hmono
  refine ⟨?_, ?_⟩
  · intro g' hg'
    have hg2 : g' ∈ pre ∨ g' ∈ post.map T := List.mem_append.mp hg'
    rcases hg2 with hp | hp
    · exact hmono g' (by rw [hC]; exact List.mem_append.mpr (Or.inl hp))
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      have hl := hTm h (legal h (by
        rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hh)))))
      refine ⟨?_, hl.2⟩
      rcases hl.1 with e | e
      · exact Or.inl e
      · exact Or.inr e
  · show (pre ++ post.map T).length < C.gates.length
    rw [hC]
    simp

theorem ble (a b : Bool) (h : a = true → b = true) : a ≤ b := by
  revert h; cases a <;> cases b <;> decide

theorem core (n : ℕ) (C : Circuit) (pre post : List Gate) (gj : Gate)
    (hC : C.gates = pre ++ gj :: post) (hmono : Monotone2 C)
    (hop : gj.op = GateOp.or) (a : ℕ) (haN : a < n + pre.length) (ha : a ∈ gj.inputs)
    (C' : Circuit)
    (hC' : C' = ⟨pre ++ post.map (Tc (n + pre.length) a), rn (n + pre.length) a C.output⟩) :
    Monotone2 C' ∧ C'.size < C.size ∧ circuitFun n C' ≤ circuitFun n C := by
  subst hC'
  obtain ⟨m1, m3⟩ := asm C pre post gj hC (Tc (n + pre.length) a)
    (rn (n + pre.length) a C.output) hmono (fun h hl => Tc_legal _ _ h hl)
  refine ⟨m1, m3, ?_⟩
  intro y
  apply ble
  let x : List Bool := List.ofFn y
  have hx : x.length = n := by simp [x]
  show Circuit.eval _ x = true → Circuit.eval C x = true
  have hlen : (wf pre x).length = n + pre.length := by rw [wf_len, hx]
  have hpostop : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or := fun h hh =>
    (legal_of C hmono h (by
      rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hh))))).1
  have hold : C.eval x = (wf post (wf pre x ++
      [gj.op.eval (gj.inputs.map fun i => (wf pre x).getD i false)])).getD C.output false := by
    show (wf C.gates x).getD C.output false = _
    rw [hC, wf_append, wf_cons]
  have hnew :
      Circuit.eval ⟨pre ++ post.map (Tc (n + pre.length) a), rn (n + pre.length) a C.output⟩ x
        = (wf post (wf pre x ++ [(wf pre x).getD a false])).getD C.output false :=
    new_eval pre post _ a C.output x hlen haN
  have hge : (wf pre x).getD a false = true →
      gj.op.eval (gj.inputs.map fun i => (wf pre x).getD i false) = true := by
    intro h
    exact (ev_or gj _ hop).mpr ⟨a, ha, h⟩
  rw [hnew, hold]
  exact fun h => swap_le post hpostop _ _ _ hge C.output h

end PEqualNP.Outside.L_meta_6037

theorem PEqualNP.Outside.L_meta_6037 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     x3 < x2.size →       (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3).op = PEqualNP.CircuitLowerBounds.GateOp.or →         x4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3).inputs →           x4 < x1 + x3 →             have x10 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.CircuitMoves.eraseGate x1 x2 x3 x4;             PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size < x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x10 ≤ PEqualNP.MetaComplexity.circuitFun x1 x2 := by
  intro x1 x2 x3 x4 hmono hk hop ha haN
  have hk' : x3 < x2.gates.length := hk
  obtain ⟨pre, post, gj, hC, hpl, hgj⟩ := PEqualNP.Outside.L_meta_6037.split_gates x2.gates x3 hk'
  have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3 = gj := by
    rw [PEqualNP.Outside.L_meta_6037.gateAt_eq x2 x3 hk']; exact hgj
  rw [hgat] at hop ha
  subst hpl
  exact PEqualNP.Outside.L_meta_6037.core x1 x2 pre post gj hC hmono hop x4 haN ha
    (PEqualNP.CircuitMoves.eraseGate x1 x2 pre.length x4)
    (PEqualNP.Outside.L_meta_6037.bridge x1 x2 pre post gj hC x4)
