import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7449

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

theorem sk_lt (N M i : ℕ) (hN0 : 0 < N) (hM : N ≤ M) (hi : i < M + 1) : sk N i < M := by
  unfold sk
  split_ifs <;> omega

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

theorem Tc_rb (N a : ℕ) (ha : a < N) (h : Gate) (M : ℕ) (hM : N ≤ M)
    (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tc N a h).inputs, i < M := by
  intro i hi'
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
  have := hi j hj
  unfold rn
  split_ifs <;> omega

theorem asm (C : Circuit) (pre post : List Gate) (g : Gate)
    (hC : C.gates = pre ++ g :: post) (T : Gate → Gate) (o' : ℕ)
    (hmono : Monotone2 C) (hrb : ReadsBack 14 C)
    (hTm : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ((T h).op = GateOp.and ∨ (T h).op = GateOp.or) ∧ (T h).inputs.length ≤ 2)
    (hTr : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ∀ M : ℕ, 14 + pre.length ≤ M → (∀ i ∈ h.inputs, i < M + 1) → ∀ i ∈ (T h).inputs, i < M) :
    Monotone2 ⟨pre ++ post.map T, o'⟩ ∧ ReadsBack 14 ⟨pre ++ post.map T, o'⟩ ∧
      Circuit.size ⟨pre ++ post.map T, o'⟩ < C.size := by
  have legal := legal_of C hmono
  refine ⟨?_, ?_, ?_⟩
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
  · intro j hj i hi
    have hj' : j < pre.length + post.length := by simpa using hj
    by_cases hjp : j < pre.length
    · have e : gateAt ⟨pre ++ post.map T, o'⟩ j = gateAt C j := by
        simp only [gateAt, hC, List.getD_eq_getElem?_getD, List.getElem?_append_left hjp]
      rw [e] at hi
      exact hrb j (by rw [hC]; simp only [List.length_append, List.length_cons]; omega) i hi
    · have hjk : j - pre.length < post.length := by omega
      have e1 : gateAt ⟨pre ++ post.map T, o'⟩ j = T (post[j - pre.length]) := by
        simp [gateAt, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_of_not_lt hjp), hjk]
      have e2 : gateAt C (j + 1) = post[j - pre.length] := by
        have h3 : j + 1 - pre.length = (j - pre.length) + 1 := by omega
        simp [gateAt, hC, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (show pre.length ≤ j + 1 by omega), h3, hjk]
      rw [e1] at hi
      have hmem : post[j - pre.length] ∈ C.gates := by
        rw [hC]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.getElem_mem hjk))))
      have hold : ∀ i ∈ (post[j - pre.length]).inputs, i < (14 + j) + 1 := by
        intro i hi2
        have := hrb (j + 1) (by rw [hC]; simp only [List.length_append, List.length_cons]; omega)
          i (by rw [e2]; exact hi2)
        omega
      exact hTr _ (legal _ hmem) (14 + j) (by omega) hold i hi
  · show (pre ++ post.map T).length < C.gates.length
    rw [hC]
    simp

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

theorem er_eq (m a : ℕ) : PEqualNP.CircuitMoves.eraseRedirect 14 m a = rn (14 + m) a := by
  funext i
  unfold PEqualNP.CircuitMoves.eraseRedirect rn
  split_ifs <;> omega

theorem bridge (C : Circuit) (pre post : List Gate) (gj : Gate)
    (hC : C.gates = pre ++ gj :: post) (a : ℕ) :
    PEqualNP.CircuitMoves.eraseGate 14 C pre.length a
      = ⟨pre ++ post.map (Tc (14 + pre.length) a), rn (14 + pre.length) a C.output⟩ := by
  have hk : pre.length < C.gates.length := by rw [hC]; simp
  have h1 : C.gates.take pre.length = pre := by rw [hC]; simp
  have h2 : C.gates.drop (pre.length + 1) = post := by rw [hC]; simp
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [if_pos hk, h1, h2, er_eq]
  rfl

theorem core (C : Circuit) (pre post : List Gate) (gj : Gate)
    (hC : C.gates = pre ++ gj :: post) (hmono : Monotone2 C) (hrb : ReadsBack 14 C)
    (hop : gj.op = GateOp.and) (a : ℕ) (haN : a < 14 + pre.length) (ha : a ∈ gj.inputs)
    (C' : Circuit)
    (hC' : C' = ⟨pre ++ post.map (Tc (14 + pre.length) a), rn (14 + pre.length) a C.output⟩) :
    Monotone2 C' ∧ ReadsBack 14 C' ∧ C'.size < C.size ∧
      ∀ x : List Bool, x.length = 14 →
        (C.eval x = true → C'.eval x = true) ∧
        ((C.wires x).getD (14 + pre.length) false = (C.wires x).getD a false →
          C'.eval x = C.eval x) := by
  subst hC'
  obtain ⟨m1, m2, m3⟩ := asm C pre post gj hC (Tc (14 + pre.length) a)
    (rn (14 + pre.length) a C.output) hmono hrb (fun h hl => Tc_legal _ _ h hl)
    (fun h _ M hM hi => Tc_rb _ _ haN h M hM hi)
  refine ⟨m1, m2, m3, ?_⟩
  intro x hx
  have hlen : (wf pre x).length = 14 + pre.length := by rw [wf_len, hx]
  have hpostop : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or := fun h hh =>
    (legal_of C hmono h (by
      rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hh))))).1
  obtain ⟨E, hE⟩ := old_wires pre post gj x
  have hwa : (C.wires x).getD a false = (wf pre x).getD a false := by
    show (wf C.gates x).getD a false = _
    rw [hC, hE]
    exact getD_left _ _ a (by rw [hlen]; exact haN)
  have hwN : (C.wires x).getD (14 + pre.length) false
      = gj.op.eval (gj.inputs.map fun i => (wf pre x).getD i false) := by
    show (wf C.gates x).getD (14 + pre.length) false = _
    rw [hC, hE]
    exact getD_mid _ _ _ _ hlen
  have hold : C.eval x = (wf post (wf pre x ++
      [gj.op.eval (gj.inputs.map fun i => (wf pre x).getD i false)])).getD C.output false := by
    show (wf C.gates x).getD C.output false = _
    rw [hC, wf_append, wf_cons]
  have hnew :
      Circuit.eval ⟨pre ++ post.map (Tc (14 + pre.length) a), rn (14 + pre.length) a C.output⟩ x
        = (wf post (wf pre x ++ [(wf pre x).getD a false])).getD C.output false :=
    new_eval pre post _ a C.output x hlen haN
  have hge : gj.op.eval (gj.inputs.map fun i => (wf pre x).getD i false) = true →
      (wf pre x).getD a false = true := by
    intro h
    exact (ev_and gj _ hop).mp h a ha
  rw [hnew, hold, hwa, hwN]
  refine ⟨fun h => swap_le post hpostop _ _ _ hge C.output h, fun h => ?_⟩
  rw [h]


theorem gate_val (C : Circuit) (pre post : List Gate) (gj : Gate)
    (hC : C.gates = pre ++ gj :: post) (x : List Bool) (hx : x.length = 14)
    (hin : ∀ i ∈ gj.inputs, i < 14 + pre.length) :
    (C.wires x).getD (14 + pre.length) false
      = gj.op.eval (gj.inputs.map fun i => (C.wires x).getD i false) := by
  have hlen : (wf pre x).length = 14 + pre.length := by rw [wf_len, hx]
  obtain ⟨E, hE⟩ := old_wires pre post gj x
  have hw : ∀ i, i < 14 + pre.length → (C.wires x).getD i false = (wf pre x).getD i false := by
    intro i hi
    show (wf C.gates x).getD i false = _
    rw [hC, hE]
    exact getD_left _ _ i (by rw [hlen]; exact hi)
  have hwN : (C.wires x).getD (14 + pre.length) false
      = gj.op.eval (gj.inputs.map fun i => (wf pre x).getD i false) := by
    show (wf C.gates x).getD (14 + pre.length) false = _
    rw [hC, hE]
    exact getD_mid _ _ _ _ hlen
  rw [hwN]
  congr 1
  exact List.map_congr_left (fun i hi => (hw i (hin i hi)).symm)

theorem exists_maxterm (f : (Fin 14 → Bool) → Bool) (x : Fin 14 → Bool) (hx : f x = false) :
    ∃ m : Fin 14 → Bool, x ≤ m ∧ f m = false ∧ ∀ y : Fin 14 → Bool, m ≤ y → f y = false → y = m := by
  classical
  let S : Finset (Fin 14 → Bool) := Finset.univ.filter (fun y => x ≤ y ∧ f y = false)
  have hS : S.Nonempty := ⟨x, by simp [S, hx]⟩
  obtain ⟨m, hmS, hmax⟩ :=
    S.exists_max_image (fun y => (Finset.univ.filter (fun i => y i = true)).card) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmS
  refine ⟨m, hmS.1, hmS.2, fun y hmy hy => ?_⟩
  by_contra hne
  have hyS : y ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_trans hmS.1 hmy, hy⟩
  have h1 := hmax y hyS
  have hsub : Finset.univ.filter (fun i => m i = true) ⊂ Finset.univ.filter (fun i => y i = true) := by
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have := hmy i
      rw [hi] at this
      revert this
      cases y i <;> simp
    · intro heq
      apply hne
      funext i
      have := Finset.ext_iff.mp heq i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact Bool.eq_iff_iff.mpr this.symm
  have := Finset.card_lt_card hsub
  omega

theorem ofFn_le (x m : Fin 14 → Bool) (h : x ≤ m) :
    ∀ i, (List.ofFn x).getD i false = true → (List.ofFn m).getD i false = true := by
  intro i hi
  by_cases hlt : i < 14
  · have hl : i < (List.ofFn x).length := by simp; omega
    have hl' : i < (List.ofFn m).length := by simp; omega
    rw [List.getD_eq_getElem _ _ hl, List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ hl', List.getElem_ofFn]
    have := h ⟨i, hlt⟩
    revert this hi
    cases x ⟨i, hlt⟩ <;> cases m ⟨i, hlt⟩ <;> simp
  · simp [List.getD_eq_getElem?_getD, hlt] at hi

theorem main (C : Circuit) (j : ℕ) (b : Fin 2) (f : (Fin 14 → Bool) → Bool)
    (hAO : PEqualNP.TopForm.IsAO2 14 C) (hf : circuitFun 14 C = f) (hj : j < C.size)
    (hop : (gateAt C j).op = GateOp.and)
    (hmax : ∀ x : Fin 14 → Bool,
      (f x = false ∧ ∀ y : Fin 14 → Bool, x ≤ y → f y = false → y = x) →
       PEqualNP.CleanedNonEdge.wireVal 14 C (PEqualNP.TopForm.opnd C j b) x = true →
       PEqualNP.CleanedNonEdge.wireVal 14 C (PEqualNP.TopForm.opnd C j (1 - b)) x = true) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 14 C' ∧ circuitFun 14 C' = f ∧ C'.size < C.size := by
  obtain ⟨hAOnly, hrb, hl2⟩ := hAO
  have hmono : Monotone2 C := fun g hg =>
    ⟨by rcases hAOnly g hg with h | h <;> simp [h], by rw [hl2 g hg]⟩
  have hk : j < C.gates.length := hj
  obtain ⟨pre, post, gj, hC, hpl, hgj⟩ := split_gates C.gates j hk
  have hgat : gateAt C j = gj := by rw [gateAt_eq C j hk]; exact hgj
  have hgmem : gj ∈ C.gates := by rw [hC]; simp
  have hlen2 : gj.inputs.length = 2 := hl2 gj hgmem
  obtain ⟨p, q, hpq⟩ : ∃ p q, gj.inputs = [p, q] := by
    rcases hI : gj.inputs with _ | ⟨p, _ | ⟨q, _ | ⟨r, t⟩⟩⟩
    all_goals rw [hI] at hlen2
    all_goals first | exact ⟨_, _, rfl⟩ | (simp at hlen2; try omega)
  subst hpl
  rw [hgat] at hop
  have hp0 : ∀ c : Fin 2, (c : ℕ) = 0 → PEqualNP.TopForm.opnd C pre.length c = p := by
    intro c hc
    unfold PEqualNP.TopForm.opnd
    rw [hgat, hpq, hc]
    rfl
  have hq1 : ∀ c : Fin 2, (c : ℕ) = 1 → PEqualNP.TopForm.opnd C pre.length c = q := by
    intro c hc
    unfold PEqualNP.TopForm.opnd
    rw [hgat, hpq, hc]
    rfl
  have hmem : PEqualNP.TopForm.opnd C pre.length b ∈ gj.inputs := by
    rw [hpq]
    rcases b with ⟨_ | _ | k, hb⟩
    · rw [hp0 ⟨0, hb⟩ rfl]; simp
    · rw [hq1 ⟨0 + 1, hb⟩ rfl]; simp
    · omega
  have hrb' : ∀ i ∈ gj.inputs, i < 14 + pre.length := fun i hi =>
    hrb pre.length hk i (by rw [hgat]; exact hi)
  have haN := hrb' _ hmem
  obtain ⟨m1, m2, m3, hev⟩ :=
    core C pre post gj hC hmono hrb hop (PEqualNP.TopForm.opnd C pre.length b) haN hmem _ rfl
  refine ⟨_, m1, m2, ?_, m3⟩
  funext x
  have hfx : C.eval (List.ofFn x) = f x := congrFun hf x
  show Circuit.eval _ (List.ofFn x) = f x
  cases hfv : f x with
  | true => exact (hev (List.ofFn x) (by simp)).1 (hfx.trans hfv)
  | false =>
    obtain ⟨m, hxm, hfm, hmx⟩ := exists_maxterm f x hfv
    have hCm : C.eval (List.ofFn m) = false := (congrFun hf m).trans hfm
    have hg := gate_val C pre post gj hC (List.ofFn m) (by simp) hrb'
    rw [hpq, hop] at hg
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id, Bool.and_true] at hg
    have hm := hmax m ⟨hfm, hmx⟩
    unfold PEqualNP.CleanedNonEdge.wireVal at hm
    have heq : (C.wires (List.ofFn m)).getD (14 + pre.length) false
        = (C.wires (List.ofFn m)).getD (PEqualNP.TopForm.opnd C pre.length b) false := by
      rw [hg]
      rcases b with ⟨_ | _ | k, hb⟩
      · have e1 : (1 : Fin 2) - ⟨0, hb⟩ = ⟨1, by omega⟩ := Fin.ext rfl
        rw [e1, hp0 ⟨0, hb⟩ rfl, hq1 ⟨1, by omega⟩ rfl] at hm
        rw [hp0 ⟨0, hb⟩ rfl]
        generalize (C.wires (List.ofFn m)).getD p false = P at *
        generalize (C.wires (List.ofFn m)).getD q false = Q at *
        cases P <;> cases Q <;> simp_all
      · have e1 : (1 : Fin 2) - ⟨0 + 1, hb⟩ = ⟨0, by omega⟩ := Fin.ext rfl
        rw [e1, hp0 ⟨0, by omega⟩ rfl, hq1 ⟨0 + 1, hb⟩ rfl] at hm
        rw [hq1 ⟨0 + 1, hb⟩ rfl]
        generalize (C.wires (List.ofFn m)).getD p false = P at *
        generalize (C.wires (List.ofFn m)).getD q false = Q at *
        cases P <;> cases Q <;> simp_all
      · omega
    have hC'm := (hev (List.ofFn m) (by simp)).2 heq
    rw [hCm] at hC'm
    cases hv : Circuit.eval ⟨pre ++ post.map (Tc (14 + pre.length)
        (PEqualNP.TopForm.opnd C pre.length b)), rn (14 + pre.length)
        (PEqualNP.TopForm.opnd C pre.length b) C.output⟩ (List.ofFn x) with
    | false => rfl
    | true =>
      exfalso
      have hops : ∀ g ∈ pre ++ post.map (Tc (14 + pre.length)
          (PEqualNP.TopForm.opnd C pre.length b)), g.op = GateOp.and ∨ g.op = GateOp.or :=
        fun g hg => by
          have := (m1 g hg).1
          simpa using this
      have := mono _ (List.ofFn x) (List.ofFn m) (by simp) hops (ofFn_le x m hxm) _ hv
      exact Bool.false_ne_true (hC'm.symm.trans this)

end PEqualNP.Outside.L_meta_7449

theorem PEqualNP.Outside.L_meta_7449 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Fin (2 : ℕ)),   have x4 : (Fin (14 : ℕ) → Bool) → Bool := fun (x4 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true);   have x5 : (Fin (14 : ℕ) → Bool) → Prop := fun (x5 : Fin (14 : ℕ) → Bool) => x4 x5 = Bool.false ∧ ∀ (x6 : Fin (14 : ℕ) → Bool), x5 ≤ x6 → x4 x6 = Bool.false → x6 = x5;   have x6 : ℕ → Fin (2 : ℕ) → (Fin (14 : ℕ) → Bool) → Bool := fun (x6 : ℕ) (x7 : Fin (2 : ℕ)) (x8 : Fin (14 : ℕ) → Bool) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x6 x7) x8;   PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = x4 → x2 < x1.size → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ (x11 : Fin (14 : ℕ) → Bool), x5 x11 → x6 x2 x3 x11 = Bool.true → x6 x2 ((1 : Fin (2 : ℕ)) - x3) x11 = Bool.true) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x12 ∧ PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x12 = x4 ∧ x12.size < x1.size := by
  intro x1 x2 x3
  dsimp only
  intro hAO hf hj hop hmax
  exact PEqualNP.Outside.L_meta_7449.main x1 x2 x3 _ hAO hf hj hop hmax
