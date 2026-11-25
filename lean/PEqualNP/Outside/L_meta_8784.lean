import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8784
open PEqualNP.CircuitLowerBounds

theorem ifp {c : Prop} [Decidable c] {α : Type} {t e : α} (h : c) : (if c then t else e) = t := by simp [h]
theorem ifn {c : Prop} [Decidable c] {α : Type} {t e : α} (h : ¬c) : (if c then t else e) = e := by simp [h]
theorem difp {c : Prop} [Decidable c] {α : Type} {t : c → α} {e : ¬c → α} (h : c) : dite c t e = t h := by simp [h]
theorem difn {c : Prop} [Decidable c] {α : Type} {t : c → α} {e : ¬c → α} (h : ¬c) : dite c t e = e h := by simp [h]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val (gs : List Gate) (w : List Bool) (i : ℕ) : Bool :=
  (gs.foldl step w).getD i false

lemma eval_eq (gs : List Gate) (out : ℕ) (w : List Bool) :
    (⟨gs, out⟩ : Circuit).eval w = val gs w out := rfl

lemma eval_eq' (C : Circuit) (w : List Bool) : C.eval w = val C.gates w C.output := rfl

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_snoc (gs : List Gate) (g : Gate) (w : List Bool) (i : ℕ) :
    val (gs ++ [g]) w i =
      if i = w.length + gs.length then g.op.eval (g.inputs.map fun j => val gs w j)
      else val gs w i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step w).length = w.length + gs.length := fold_length gs w
  rcases lt_trichotomy i (w.length + gs.length) with h | h | h
  · rw [ifn (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ifp h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ifn (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    val gs w i = false := by
  unfold val
  have hl : (gs.foldl step w).length = w.length + gs.length := fold_length gs w
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    val gs w i = w.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [val_snoc, ifn (by omega)]
    exact ih

lemma val_prefix (gs hs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length + gs.length) :
    val (gs ++ hs) w i = val gs w i := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs h ih =>
    rw [← List.append_assoc, val_snoc, ifn (by rw [List.length_append]; omega), ih]

lemma val_flat (L : List Bool) : ∀ (gs : List Gate), (∀ g ∈ gs, ∀ i ∈ g.inputs, i < L.length) →
    ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
      val gs L (L.length + j) = g.op.eval (g.inputs.map fun i => L.getD i false) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _ j g h; simp at h
  | append_singleton gs g0 ih =>
    intro hin j g hj
    rw [val_snoc]
    rcases lt_trichotomy j gs.length with h | h | h
    · rw [ifn (by omega)]
      rw [List.getElem?_append_left h] at hj
      exact ih (fun g' hg' => hin g' (List.mem_append_left _ hg')) j g hj
    · subst h
      rw [ifp rfl]
      rw [List.getElem?_append_right (le_refl _), Nat.sub_self] at hj
      simp at hj
      subst hj
      congr 1
      apply List.map_congr_left
      intro i hi
      exact val_lt gs L i (hin _ (List.mem_append_right _ (List.mem_singleton_self _)) i hi)
    · rw [List.getElem?_eq_none (by simp; omega)] at hj
      cases hj

-- well-formed gate lists: AND/OR, two inputs, each input earlier.
def WF (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < m + j

lemma wf_append (m : ℕ) (gs hs : List Gate) (h1 : WF m gs) (h2 : WF (m + gs.length) hs) :
    WF m (gs ++ hs) := by
  intro j g hj
  rcases lt_or_ge j gs.length with h | h
  · rw [List.getElem?_append_left h] at hj
    exact h1 j g hj
  · rw [List.getElem?_append_right h] at hj
    obtain ⟨hop, hlen, hlt⟩ := h2 (j - gs.length) g hj
    exact ⟨hop, hlen, fun i hi => by have := hlt i hi; omega⟩

lemma isAO2_of_wf (m : ℕ) (gs : List Gate) (out : ℕ) (hwf : WF m gs) :
    PEqualNP.TopForm.IsAO2 m (⟨gs, out⟩ : Circuit) := by
  unfold PEqualNP.TopForm.IsAO2
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hg
    exact (hwf j g hj).1
  · intro j hj i hi
    have hj' : j < gs.length := hj
    have hi' : i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs := hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] at hi'
    exact (hwf j _ (List.getElem?_eq_getElem hj')).2.2 i hi'
  · intro g hg
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hg
    exact (hwf j g hj).2.1

def phi (a b : ℕ) (w : ℕ) : ℕ :=
  if w < a then w else if w < a + a then w + b else w - (a + a) + (a + b + (a + b))

def rho (a b : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (phi a b)⟩

lemma reidx (a b : ℕ) (L L5 : List Bool) (P : List Gate)
    (hL : L.length + P.length = a + b + (a + b) + b) (h5 : L5.length = a + a + b)
    (hbase : ∀ w, val P L (phi a b w) = L5.getD w false) :
    ∀ (gs : List Gate) (w : ℕ), val (P ++ gs.map (rho a b)) L (phi a b w) = val gs L5 w := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    rw [List.map_nil, List.append_nil, hbase]
    rfl
  | append_singleton gs g ih =>
    intro w
    rw [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc, val_snoc, val_snoc]
    have key : phi a b w = L.length + (P ++ gs.map (rho a b)).length ↔
        w = L5.length + gs.length := by
      rw [List.length_append, List.length_map, h5]
      unfold phi
      split_ifs <;> omega
    by_cases hw : w = L5.length + gs.length
    · rw [ifp (key.2 hw), ifp hw]
      show g.op.eval (List.map (fun j => val (P ++ gs.map (rho a b)) L j)
        (g.inputs.map (phi a b))) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact ih j
    · rw [ifn (fun h => hw (key.1 h)), ifn hw]
      exact ih w

lemma wf_map (a b : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (a + a + b) C) :
    WF (a + b + (a + b) + b) (C.gates.map (rho a b)) := by
  obtain ⟨hC1, hC2, hC3⟩ := hC
  intro j g hj
  rw [List.getElem?_map] at hj
  cases h : C.gates[j]? with
  | none =>
    rw [h] at hj
    simp at hj
  | some g0 =>
    rw [h] at hj
    simp at hj
    subst hj
    have hmem : g0 ∈ C.gates := List.mem_of_getElem? h
    have hjl : j < C.gates.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at h
      cases h
    refine ⟨hC1 g0 hmem, ?_, ?_⟩
    · show (g0.inputs.map (phi a b)).length = 2
      rw [List.length_map]
      exact hC3 g0 hmem
    · intro i hi
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hi
      have hwl : w < a + a + b + j := hC2 j hjl w (by
        show w ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs
        rw [List.getD_eq_getElem?_getD, h]
        exact hw)
      unfold phi
      split_ifs <;> omega

lemma val_three (gs : List Gate) (L : List Bool) (N p q r out : ℕ) (hL : L.length = N)
    (hp : p < N + gs.length) (hq : q < N + gs.length) (hr : r < N + gs.length)
    (ho : out < N + gs.length) :
    val (gs ++ [⟨GateOp.or, [p, q]⟩, ⟨GateOp.and, [r, N + gs.length]⟩,
      ⟨GateOp.or, [out, N + gs.length + 1]⟩]) L (N + gs.length + 2)
      = (val gs L out || (val gs L r && (val gs L p || val gs L q))) := by
  have happ : gs ++ [(⟨GateOp.or, [p, q]⟩ : Gate), ⟨GateOp.and, [r, N + gs.length]⟩,
      ⟨GateOp.or, [out, N + gs.length + 1]⟩]
      = ((gs ++ [⟨GateOp.or, [p, q]⟩]) ++ [⟨GateOp.and, [r, N + gs.length]⟩]) ++
        [⟨GateOp.or, [out, N + gs.length + 1]⟩] := by simp
  have h1 : val (gs ++ [⟨GateOp.or, [p, q]⟩]) L (N + gs.length) =
      (val gs L p || val gs L q) := by
    rw [val_snoc, ifp (by omega)]
    simp [GateOp.eval]
  have h2 : val ((gs ++ [⟨GateOp.or, [p, q]⟩]) ++ [⟨GateOp.and, [r, N + gs.length]⟩]) L
      (N + gs.length + 1) = (val gs L r && (val gs L p || val gs L q)) := by
    rw [val_snoc, ifp (by simp; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true]
    rw [h1, val_prefix gs _ L r (by omega)]
  rw [happ, val_snoc, ifp (by simp; omega)]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
    Bool.or_false]
  rw [h2, val_prefix (gs ++ [(⟨GateOp.or, [p, q]⟩ : Gate)]) _ L out (by simp; omega),
    val_prefix gs _ L out (by omega)]

def ext (a b N : ℕ) : List (Fin b) → List Gate → ℕ → List Gate × ℕ
  | [], gs, out => (gs, out)
  | k :: E, gs, out =>
    ext a b N E (gs ++ [⟨GateOp.or, [N + k.val, a + b + a + k.val]⟩,
      ⟨GateOp.and, [a + k.val, N + gs.length]⟩, ⟨GateOp.or, [out, N + gs.length + 1]⟩])
      (N + gs.length + 2)

lemma ext_cons (a b N : ℕ) (k : Fin b) (E : List (Fin b)) (gs : List Gate) (out : ℕ) :
    ext a b N (k :: E) gs out =
      ext a b N E (gs ++ [⟨GateOp.or, [N + k.val, a + b + a + k.val]⟩,
        ⟨GateOp.and, [a + k.val, N + gs.length]⟩, ⟨GateOp.or, [out, N + gs.length + 1]⟩])
        (N + gs.length + 2) := rfl

lemma ext_struct (a b N : ℕ) (hN : N = a + b + (a + b)) :
    ∀ (E : List (Fin b)) (gs : List Gate) (out : ℕ),
    out < N + gs.length → b ≤ gs.length → WF N gs →
    (ext a b N E gs out).1.length = gs.length + 3 * E.length ∧
    (ext a b N E gs out).2 < N + (ext a b N E gs out).1.length ∧
    WF N (ext a b N E gs out).1 := by
  intro E
  induction E with
  | nil =>
    intro gs out hout _ hwf
    exact ⟨by simp [ext], hout, hwf⟩
  | cons k E ih =>
    intro gs out hout hb hwf
    have hk := k.isLt
    rw [ext_cons]
    have hl3 : (gs ++ [(⟨GateOp.or, [N + k.val, a + b + a + k.val]⟩ : Gate),
        ⟨GateOp.and, [a + k.val, N + gs.length]⟩,
        ⟨GateOp.or, [out, N + gs.length + 1]⟩]).length = gs.length + 3 := by simp
    have hwf3 : WF N (gs ++ [(⟨GateOp.or, [N + k.val, a + b + a + k.val]⟩ : Gate),
        ⟨GateOp.and, [a + k.val, N + gs.length]⟩,
        ⟨GateOp.or, [out, N + gs.length + 1]⟩]) := by
      apply wf_append N gs _ hwf
      intro j g hj
      match j, hj with
      | 0, hj =>
        simp at hj
        subst hj
        exact ⟨Or.inr rfl, rfl, by intro i hi; simp at hi; omega⟩
      | 1, hj =>
        simp at hj
        subst hj
        exact ⟨Or.inl rfl, rfl, by intro i hi; simp at hi; omega⟩
      | 2, hj =>
        simp at hj
        subst hj
        exact ⟨Or.inr rfl, rfl, by intro i hi; simp at hi; omega⟩
      | j + 3, hj => simp at hj
    obtain ⟨h1, h2, h3⟩ := ih _ (N + gs.length + 2) (by rw [hl3]; omega)
      (by rw [hl3]; omega) hwf3
    refine ⟨?_, h2, h3⟩
    rw [h1, hl3, List.length_cons]
    ring

lemma ext_val (a b N : ℕ) (L : List Bool) (c : Fin b → Bool) (hL : L.length = N)
    (hN : N = a + b + (a + b)) :
    ∀ (E : List (Fin b)) (gs : List Gate) (out : ℕ),
    out < N + gs.length → b ≤ gs.length → (∀ k : Fin b, val gs L (N + k.val) = c k) →
    val (ext a b N E gs out).1 L (ext a b N E gs out).2 =
      (val gs L out || E.any (fun k => L.getD (a + k.val) false &&
        (c k || L.getD (a + b + a + k.val) false))) := by
  intro E
  induction E with
  | nil =>
    intro gs out _ _ _
    simp [ext]
  | cons k E ih =>
    intro gs out hout hb hc
    have hk := k.isLt
    rw [ext_cons]
    have hl3 : (gs ++ [(⟨GateOp.or, [N + k.val, a + b + a + k.val]⟩ : Gate),
        ⟨GateOp.and, [a + k.val, N + gs.length]⟩,
        ⟨GateOp.or, [out, N + gs.length + 1]⟩]).length = gs.length + 3 := by simp
    rw [ih _ (N + gs.length + 2) (by rw [hl3]; omega) (by rw [hl3]; omega)
      (fun k' => by
        have := k'.isLt
        rw [val_prefix gs _ L _ (by omega)]
        exact hc k')]
    rw [val_three gs L N (N + k.val) (a + b + a + k.val) (a + k.val) out hL (by omega)
      (by omega) (by omega) hout]
    rw [val_lt gs L (a + k.val) (by omega), val_lt gs L (a + b + a + k.val) (by omega), hc k]
    simp only [List.any_cons, Bool.or_assoc]

lemma gdA (l : List Bool) {m : ℕ} (g : Fin m → Bool) (i : ℕ) :
    (l ++ List.ofFn g).getD i false =
      if i < l.length then l.getD i false
      else if h2 : i - l.length < m then g ⟨i - l.length, h2⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < l.length
  · rw [ifp h, List.getElem?_append_left h, List.getD_eq_getElem?_getD]
  · rw [ifn h, List.getElem?_append_right (by omega)]
    by_cases h2 : i - l.length < m
    · rw [difp h2]
      simp [h2]
    · rw [difn h2]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl

lemma gdO {n : ℕ} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  have := gdA [] f i
  simpa using this

theorem main (a b : ℕ) (x3 x4 : Fin b → Fin a) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 (a + a + b) C) (hout : C.output < a + a + b + C.size) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (a + b + (a + b)) D ∧ D.size ≤ C.size + 4 * b ∧
      ∀ (x9 x10 : Fin (a + b) → Bool), D.eval (List.ofFn x9 ++ List.ofFn x10) =
        (C.eval (((List.ofFn fun i : Fin a => x9 (Fin.castAdd b i)) ++
          List.ofFn fun i : Fin a => x10 (Fin.castAdd b i)) ++
          List.ofFn fun k : Fin b => x10 (Fin.castAdd b (x3 k)) || x10 (Fin.castAdd b (x4 k))) ||
        (List.finRange b).any fun k : Fin b => x9 (Fin.natAdd a k) &&
          (x10 (Fin.castAdd b (x3 k)) || x10 (Fin.castAdd b (x4 k)) || x10 (Fin.natAdd a k))) := by
  obtain ⟨G1, hG1len, hG1wf, hG1in, hG1get⟩ : ∃ G1 : List Gate, G1.length = b ∧
      WF (a + b + (a + b)) G1 ∧ (∀ g ∈ G1, ∀ i ∈ g.inputs, i < a + b + (a + b)) ∧
      ∀ k : Fin b, G1[k.val]? = some ⟨GateOp.or, [a + b + (x3 k).val, a + b + (x4 k).val]⟩ := by
    have hin : ∀ g ∈ List.ofFn (fun k : Fin b =>
        (⟨GateOp.or, [a + b + (x3 k).val, a + b + (x4 k).val]⟩ : Gate)),
        g.op = GateOp.or ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < a + b + (a + b) := by
      intro g hg
      simp only [List.mem_ofFn] at hg
      obtain ⟨k, rfl⟩ := hg
      have h3 := (x3 k).isLt
      have h4 := (x4 k).isLt
      refine ⟨rfl, rfl, ?_⟩
      intro i hi
      simp at hi
      omega
    refine ⟨List.ofFn (fun k : Fin b =>
      (⟨GateOp.or, [a + b + (x3 k).val, a + b + (x4 k).val]⟩ : Gate)), by simp, ?_,
      fun g hg => (hin g hg).2.2, ?_⟩
    · intro j g hj
      have hg := hin g (List.mem_of_getElem? hj)
      exact ⟨Or.inr hg.1, hg.2.1, fun i hi => by have := hg.2.2 i hi; omega⟩
    · intro k
      rw [List.getElem?_eq_getElem (by simp)]
      simp
  have hPlen : (G1 ++ C.gates.map (rho a b)).length = b + C.size := by
    simp [hG1len, Circuit.size]
  have hPwf : WF (a + b + (a + b)) (G1 ++ C.gates.map (rho a b)) :=
    wf_append _ _ _ hG1wf (by rw [hG1len]; exact wf_map a b C hC)
  have hpo : phi a b C.output < a + b + (a + b) + (G1 ++ C.gates.map (rho a b)).length := by
    rw [hPlen]
    unfold phi
    split_ifs <;> omega
  obtain ⟨hl, -, hwf⟩ := ext_struct a b (a + b + (a + b)) rfl (List.finRange b)
    (G1 ++ C.gates.map (rho a b)) (phi a b C.output) hpo (by omega) hPwf
  refine ⟨⟨(ext a b (a + b + (a + b)) (List.finRange b) (G1 ++ C.gates.map (rho a b))
    (phi a b C.output)).1, (ext a b (a + b + (a + b)) (List.finRange b)
    (G1 ++ C.gates.map (rho a b)) (phi a b C.output)).2⟩, isAO2_of_wf _ _ _ hwf, ?_, ?_⟩
  · show (ext a b (a + b + (a + b)) (List.finRange b) (G1 ++ C.gates.map (rho a b))
      (phi a b C.output)).1.length ≤ _
    rw [hl, hPlen, List.length_finRange]
    omega
  · intro x9 x10
    have hLlen : (List.ofFn x9 ++ List.ofFn x10).length = a + b + (a + b) := by simp
    have hL1 : ∀ (i : ℕ) (h : i < a), (List.ofFn x9 ++ List.ofFn x10).getD i false =
        x9 (Fin.castAdd b ⟨i, h⟩) := by
      intro i h
      rw [gdA, ifp (by simp only [List.length_append, List.length_ofFn]; omega), gdO, difp (by omega)]
      rfl
    have hL2 : ∀ k : Fin b, (List.ofFn x9 ++ List.ofFn x10).getD (a + k.val) false =
        x9 (Fin.natAdd a k) := by
      intro k
      have := k.isLt
      rw [gdA, ifp (by simp only [List.length_append, List.length_ofFn]; omega), gdO, difp (by omega)]
      rfl
    have hL3 : ∀ (i : ℕ) (h : i < a), (List.ofFn x9 ++ List.ofFn x10).getD (a + b + i) false =
        x10 (Fin.castAdd b ⟨i, h⟩) := by
      intro i h
      rw [gdA, ifn (by simp only [List.length_ofFn]; omega), List.length_ofFn, difp (by omega)]
      congr 1
      ext
      simp
    have hL4 : ∀ k : Fin b, (List.ofFn x9 ++ List.ofFn x10).getD (a + b + a + k.val) false =
        x10 (Fin.natAdd a k) := by
      intro k
      have := k.isLt
      rw [gdA, ifn (by simp only [List.length_ofFn]; omega), List.length_ofFn, difp (by omega)]
      congr 1
      ext
      simp
      omega
    have hc : ∀ k : Fin b, val (G1 ++ C.gates.map (rho a b)) (List.ofFn x9 ++ List.ofFn x10)
        (a + b + (a + b) + k.val) =
        ((List.ofFn x9 ++ List.ofFn x10).getD (a + b + (x3 k).val) false ||
          (List.ofFn x9 ++ List.ofFn x10).getD (a + b + (x4 k).val) false) := by
      intro k
      have := k.isLt
      rw [val_prefix G1 _ _ _ (by rw [hLlen, hG1len]; omega)]
      rw [show a + b + (a + b) + k.val = (List.ofFn x9 ++ List.ofFn x10).length + k.val by
        rw [hLlen]]
      rw [val_flat _ G1 (by intro g hg i hi; rw [hLlen]; exact hG1in g hg i hi) k.val _
        (hG1get k)]
      simp [GateOp.eval]
    have hbase : ∀ w, val G1 (List.ofFn x9 ++ List.ofFn x10) (phi a b w) =
        (((List.ofFn fun i : Fin a => x9 (Fin.castAdd b i)) ++
          List.ofFn fun i : Fin a => x10 (Fin.castAdd b i)) ++
          List.ofFn fun k : Fin b => x10 (Fin.castAdd b (x3 k)) ||
            x10 (Fin.castAdd b (x4 k))).getD w false := by
      intro w
      unfold phi
      split_ifs with h1 h2
      · rw [val_lt G1 _ w (by rw [hLlen]; omega), hL1 w h1]
        rw [gdA, ifp (by simp only [List.length_append, List.length_ofFn]; omega), gdA, ifp (by simp only [List.length_append, List.length_ofFn]; omega), gdO, difp h1]
      · rw [val_lt G1 _ (w + b) (by rw [hLlen]; omega)]
        have := hL3 (w - a) (by omega)
        rw [show a + b + (w - a) = w + b by omega] at this
        rw [this]
        rw [gdA, ifp (by simp only [List.length_append, List.length_ofFn]; omega), gdA, ifn (by simp only [List.length_append, List.length_ofFn]; omega), List.length_ofFn,
          difp (by omega)]
      · by_cases h3 : w < a + a + b
        · have hk : w - (a + a) < b := by omega
          rw [show w - (a + a) + (a + b + (a + b)) =
            (List.ofFn x9 ++ List.ofFn x10).length + (w - (a + a)) by rw [hLlen]; omega]
          rw [val_flat _ G1 (by intro g hg i hi; rw [hLlen]; exact hG1in g hg i hi)
            (w - (a + a)) _ (hG1get ⟨w - (a + a), hk⟩)]
          rw [gdA, ifn (by simp only [List.length_append, List.length_ofFn]; omega), difp (by simp only [List.length_append, List.length_ofFn]; omega)]
          have h3' := (x3 ⟨w - (a + a), hk⟩).isLt
          have h4' := (x4 ⟨w - (a + a), hk⟩).isLt
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false]
          rw [hL3 _ h3', hL3 _ h4']
          simp only [List.length_append, List.length_ofFn]
        · rw [val_ge G1 _ _ (by rw [hLlen, hG1len]; omega)]
          rw [gdA, ifn (by simp only [List.length_append, List.length_ofFn]; omega), difn (by simp only [List.length_append, List.length_ofFn]; omega)]
    rw [eval_eq, ext_val a b (a + b + (a + b)) (List.ofFn x9 ++ List.ofFn x10)
      (fun k => (List.ofFn x9 ++ List.ofFn x10).getD (a + b + (x3 k).val) false ||
          (List.ofFn x9 ++ List.ofFn x10).getD (a + b + (x4 k).val) false) hLlen rfl
      (List.finRange b) _ _ hpo (by omega) hc]
    rw [reidx a b _ _ G1 (by rw [hLlen, hG1len]) (by simp only [List.length_append, List.length_ofFn]) hbase C.gates C.output, ← eval_eq']
    simp only [hL2, hL4, hL3, Fin.is_lt, Fin.eta]

end PEqualNP.Outside.L_meta_8784

theorem PEqualNP.Outside.L_meta_8784 : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x2 → Fin x1) (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x1 + x2) x5 → x5.output < x1 + x1 + x2 + x5.size → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2 + (x1 + x2)) x8 ∧ x8.size ≤ x5.size + (4 : ℕ) * x2 ∧ ∀ (x9 x10 : Fin (x1 + x2) → Bool), x8.eval (List.ofFn x9 ++ List.ofFn x10) = (x5.eval (((List.ofFn fun (x11 : Fin x1) => x9 (Fin.castAdd x2 x11)) ++ List.ofFn fun (x11 : Fin x1) => x10 (Fin.castAdd x2 x11)) ++ List.ofFn fun (x11 : Fin x2) => x10 (Fin.castAdd x2 (x3 x11)) || x10 (Fin.castAdd x2 (x4 x11))) || (List.finRange x2).any fun (x11 : Fin x2) => x9 (Fin.natAdd x1 x11) && (x10 (Fin.castAdd x2 (x3 x11)) || x10 (Fin.castAdd x2 (x4 x11)) || x10 (Fin.natAdd x1 x11))) := by
  intro x1 x2 x3 x4 x5 h1 h2
  exact PEqualNP.Outside.L_meta_8784.main x1 x2 x3 x4 x5 h1 h2
