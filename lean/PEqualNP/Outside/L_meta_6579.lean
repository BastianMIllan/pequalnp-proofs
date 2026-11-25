import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6579

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadK PEqualNP.TopForm

def s2230_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2230_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2230_stepWire x := rfl

lemma s2230_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2230_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2230_stepWire]
    omega

lemma s2230_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2230_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2230_stepWire w g).length := by simp [s2230_stepWire]; omega
    rw [ih (s2230_stepWire w g) hlt]
    simp [s2230_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2230_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2230_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [s2230_wires_eq_foldl, s2230_foldl_stepWire_length, List.length_ofFn]

lemma s2230_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def s2230_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma s2230_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma s2230_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    s2230_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then s2230_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2230_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [s2230_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl s2230_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, s2230_foldl_stepWire_length, hpre_len]
  have hCj : s2230_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [s2230_W]
    rw [s2230_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [s2230_foldl_stepWire_getD_lt post (s2230_stepWire w0 gj) (n + k) (by simp [s2230_stepWire]; omega)]
    simp [s2230_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [s2230_W]
    rw [s2230_wires_eq_foldl, hgs, List.foldl_append]
    exact (s2230_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact s2230_getD_ge_length w0 i (by omega)

lemma s2230_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    s2230_W n C x u = x ⟨u, hu⟩ := by
  simp only [s2230_W]
  rw [s2230_wires_eq_foldl, s2230_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]


def s2230_FR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def s2230_stepR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
  R ++ [s2230_FR S k R g]

lemma s2230_readVectors_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl (s2230_stepR S k) ((List.range n).map (leafVectors S k)) := by
  first
    | rfl
    | (unfold readVectors; congr 1; funext R g; rcases g with ⟨op, ins⟩; cases op <;> rfl)

lemma s2230_FR_or (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) (h : g.op = GateOp.or) :
    s2230_FR S k R g =
      (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) [] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.or := h
  subst h2
  rfl

lemma s2230_FR_and (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate)
    (h : g.op = GateOp.and) :
    s2230_FR S k R g = (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.and := h
  subst h2
  rfl

lemma s2230_foldR_length (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) :
    (gs.foldl (s2230_stepR S k) R).length = R.length + gs.length := by
  induction gs generalizing R with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2230_stepR]
    omega

lemma s2230_foldR_getD_lt (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) (i : ℕ)
    (hi : i < R.length) : (gs.foldl (s2230_stepR S k) R).getD i [] = R.getD i [] := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2230_stepR S k R g).length := by simp [s2230_stepR]; omega
    rw [ih (s2230_stepR S k R g) hlt]
    simp [s2230_stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def s2230_RV (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD w []

lemma s2230_RV_input (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) (hw : w < n) :
    s2230_RV C n S k w = leafVectors S k w := by
  simp only [s2230_RV]
  rw [s2230_readVectors_eq, s2230_foldR_getD_lt S k C.gates ((List.range n).map (leafVectors S k)) w
    (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma s2230_RV_gate (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (j : ℕ) (hj : j < C.gates.length) :
    ∃ Rp : List (List (List ℕ)),
      (∀ i, i < n + j → Rp.getD i [] = s2230_RV C n S k i) ∧
      s2230_RV C n S k (n + j) = s2230_FR S k Rp (gateAt C j) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2230_split_gates C.gates j hj
  have hga : gateAt C j = gj := by rw [s2230_gateAt_eq C j hj]; exact hgj
  rw [hga]
  obtain ⟨Rp, hRp⟩ : ∃ Rp, Rp = pre.foldl (s2230_stepR S k) ((List.range n).map (leafVectors S k)) :=
    ⟨_, rfl⟩
  have hlen : Rp.length = n + j := by
    rw [hRp, s2230_foldR_length]
    simp only [List.length_map, List.length_range, hpre_len]
  have hall : readVectors C n S k = post.foldl (s2230_stepR S k) (s2230_stepR S k Rp gj) := by
    rw [s2230_readVectors_eq, hgs, List.foldl_append, List.foldl_cons, hRp]
  have hlen1 : (s2230_stepR S k Rp gj).length = n + j + 1 := by
    simp [s2230_stepR, hlen]
  refine ⟨Rp, ?_, ?_⟩
  · intro i hi
    simp only [s2230_RV]
    rw [hall, s2230_foldR_getD_lt S k post (s2230_stepR S k Rp gj) i (by omega)]
    simp [s2230_stepR, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show i < Rp.length by omega)]
  · simp only [s2230_RV]
    rw [hall, s2230_foldR_getD_lt S k post (s2230_stepR S k Rp gj) (n + j) (by omega)]
    simp [s2230_stepR, List.getD_eq_getElem?_getD, hlen]

lemma s2230_mem_foldl_insertNew (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ L.foldl insertNew acc) : v ∈ acc ∨ v ∈ L := by
  induction L generalizing acc with
  | nil => exact Or.inl h
  | cons x L ih =>
    rw [List.foldl_cons] at h
    rcases ih _ h with h1 | h1
    · unfold insertNew at h1
      split_ifs at h1
      · exact Or.inl h1
      · rcases List.mem_append.1 h1 with h2 | h2
        · exact Or.inl h2
        · have h3 : v = x := by simpa using h2
          exact Or.inr (by simp [h3])
    · exact Or.inr (List.mem_cons_of_mem _ h1)

lemma s2230_mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) (h : v ∈ andStep k A B) :
    ∃ u ∈ A, ∃ u2 ∈ B, v = capAdd k u u2 := by
  unfold andStep at h
  rcases s2230_mem_foldl_insertNew _ _ _ h with h1 | h1
  · simp at h1
  · simp only [List.mem_flatMap, List.mem_map] at h1
    obtain ⟨u, hu, u2, hu2, rfl⟩ := h1
    exact ⟨u, hu, u2, hu2, rfl⟩

lemma s2230_capAdd_pair (k x1 y1 x2 y2 : ℕ) :
    capAdd k [x1, y1] [x2, y2] = [min (x1 + x2) (k + 1), min (y1 + y2) (k + 1)] := by
  first
    | rfl
    | simp [capAdd]

lemma s2230_leaf_eq (a b w : ℕ) :
    leafVectors [a, b] 1 w =
      if w ∈ [a, b] then [[if a = w then 1 else 0, if b = w then 1 else 0]] else [] := by
  first
    | rfl
    | (unfold leafVectors; simp)


lemma mem_foldl_insertNew_of_acc (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ acc) : v ∈ L.foldl insertNew acc := by
  induction L generalizing acc with
  | nil => exact h
  | cons x L ih =>
    rw [List.foldl_cons]
    apply ih
    unfold insertNew
    split_ifs
    · exact h
    · exact List.mem_append_left _ h

lemma mem_foldl_insertNew_of_mem (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ L) : v ∈ L.foldl insertNew acc := by
  induction L generalizing acc with
  | nil => simp at h
  | cons x L ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with h1 | h1
    · apply mem_foldl_insertNew_of_acc
      subst h1
      unfold insertNew
      split_ifs with h2
      · exact h2
      · simp
    · exact ih _ h1

lemma mem_andStep_of (k : ℕ) (A B : List (List ℕ)) (u u2 : List ℕ) (hu : u ∈ A) (hu2 : u2 ∈ B) :
    capAdd k u u2 ∈ andStep k A B := by
  unfold andStep
  apply mem_foldl_insertNew_of_mem
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨u, hu, u2, hu2, rfl⟩

lemma mem_orFold (As : List (List (List ℕ))) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ acc ∨ ∃ A ∈ As, v ∈ A) :
    v ∈ As.foldl (fun acc A => A.foldl insertNew acc) acc := by
  induction As generalizing acc with
  | nil =>
    rcases h with h | ⟨A, hA, _⟩
    · exact h
    · simp at hA
  | cons A0 As ih =>
    rw [List.foldl_cons]
    apply ih
    rcases h with h | ⟨A, hA, hv⟩
    · exact Or.inl (mem_foldl_insertNew_of_acc _ _ _ h)
    · rcases List.mem_cons.1 hA with h1 | h1
      · subst h1
        exact Or.inl (mem_foldl_insertNew_of_mem _ _ _ hv)
      · exact Or.inr ⟨A, h1, hv⟩

lemma capAdd_map (L : List ℕ) (f g : ℕ → ℕ) (k : ℕ) :
    capAdd k (L.map f) (L.map g) = L.map (fun j => min (f j + g j) (k + 1)) := by
  unfold capAdd
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.zipWith_cons_cons, ih]

def uv (L : List ℕ) (i : ℕ) : List ℕ := L.map fun j => if j = i then min 1 (1 + 1) else 0

lemma mem_setList {n : ℕ} (S : Finset (Fin n)) (w : ℕ) (hw : w < n) (h : (⟨w, hw⟩ : Fin n) ∈ S) :
    w ∈ setList S := by
  unfold setList
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  exact ⟨⟨w, hw⟩, h, rfl⟩

theorem inv (x1 x2 : ℕ) (C : Circuit) (x4 : Bool → Finset ℕ) (hC : IsAO2 (x1 + x2) C)
    (hx4 : ∀ (b : Bool), ∀ w ∈ x4 b, (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
      ∃ j < C.size, w = x1 + x2 + j ∧ (gateAt C j).op = GateOp.or ∧
        ∀ i ∈ (gateAt C j).inputs, i ∈ x4 b)
    (hand : ∀ j < C.size, (gateAt C j).op = GateOp.and →
      ∃ (a : ℕ) (c : ℕ), (gateAt C j).inputs = [a, c] ∧ a ∈ x4 false ∧ c ∈ x4 true)
    (S : Finset (Fin (x1 + x2))) :
    ∀ w, s2230_W (x1 + x2) C (setInput S) w = true →
      (∃ v ∈ s2230_RV C (x1 + x2) (setList S) 1 w, ∀ a ∈ v, a ≤ 1) ∧
      (∀ b, w ∈ x4 b → ∃ i, decide (x1 ≤ i) = b ∧
        uv (setList S) i ∈ s2230_RV C (x1 + x2) (setList S) 1 w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  obtain ⟨hAO, hRB, _⟩ := hC
  by_cases hwn : w < x1 + x2
  · have hS : (⟨w, hwn⟩ : Fin (x1 + x2)) ∈ S := by
      rw [s2230_W_input (x1 + x2) C _ w hwn] at hw
      simpa [setInput] using hw
    have hmem : w ∈ setList S := mem_setList S w hwn hS
    have hRV : s2230_RV C (x1 + x2) (setList S) 1 w = [uv (setList S) w] := by
      rw [s2230_RV_input C (x1 + x2) (setList S) 1 w hwn]
      unfold leafVectors uv
      rw [if_pos hmem]
    refine ⟨⟨uv (setList S) w, by rw [hRV]; exact List.mem_singleton_self _, ?_⟩, ?_⟩
    · intro a ha
      unfold uv at ha
      simp only [List.mem_map] at ha
      obtain ⟨j, _, rfl⟩ := ha
      split_ifs <;> omega
    · intro b hb
      refine ⟨w, ?_, by rw [hRV]; exact List.mem_singleton_self _⟩
      rcases hx4 b w hb with ⟨_, hside⟩ | ⟨j, _, hj, _⟩
      · exact hside
      · omega
  · by_cases hwl : w < x1 + x2 + C.gates.length
    swap
    · exfalso
      have hf : s2230_W (x1 + x2) C (setInput S) w = false := by
        unfold s2230_W
        exact s2230_getD_ge_length _ _ (by rw [s2230_wires_length]; omega)
      rw [hf] at hw
      exact Bool.false_ne_true hw
    obtain ⟨j, rfl⟩ : ∃ j, w = x1 + x2 + j := ⟨w - (x1 + x2), by omega⟩
    have hj : j < C.gates.length := by omega
    have hgW := s2230_W_gate (x1 + x2) C (setInput S) j hj
    obtain ⟨Rp, hRp, hRVj⟩ := s2230_RV_gate C (x1 + x2) (setList S) 1 j hj
    have hRB' : ∀ i ∈ (gateAt C j).inputs, i < x1 + x2 + j := hRB j hj
    have hmapW : ((gateAt C j).inputs.map fun i =>
        if i < x1 + x2 + j then s2230_W (x1 + x2) C (setInput S) i else false) =
        (gateAt C j).inputs.map fun i => s2230_W (x1 + x2) C (setInput S) i := by
      refine List.map_congr_left fun i hi => ?_
      rw [if_pos (hRB' i hi)]
    have hmapR : ((gateAt C j).inputs.map fun i => Rp.getD i []) =
        (gateAt C j).inputs.map fun i => s2230_RV C (x1 + x2) (setList S) 1 i := by
      refine List.map_congr_left fun i hi => ?_
      exact hRp i (hRB' i hi)
    have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or :=
      hAO (gateAt C j) (by rw [s2230_gateAt_eq C j hj]; exact List.getElem_mem hj)
    have hor_true : (gateAt C j).op = GateOp.or →
        ∃ i ∈ (gateAt C j).inputs, s2230_W (x1 + x2) C (setInput S) i = true := by
      intro ho
      have hw' := hw
      rw [hgW, hmapW, ho] at hw'
      simpa [GateOp.eval] using hw'
    have hor_mem : (gateAt C j).op = GateOp.or → ∀ i ∈ (gateAt C j).inputs,
        ∀ v ∈ s2230_RV C (x1 + x2) (setList S) 1 i,
          v ∈ s2230_RV C (x1 + x2) (setList S) 1 (x1 + x2 + j) := by
      intro ho i hi v hv
      rw [hRVj, s2230_FR_or _ _ _ _ ho, hmapR]
      apply mem_orFold
      exact Or.inr ⟨_, List.mem_map.2 ⟨i, hi, rfl⟩, hv⟩
    refine ⟨?_, ?_⟩
    · rcases hop with ho | ho
      · obtain ⟨a, c, hac, ha, hc⟩ := hand j hj ho
        have hw' := hw
        rw [hgW, hmapW, ho, hac] at hw'
        have hwa : s2230_W (x1 + x2) C (setInput S) a = true ∧
            s2230_W (x1 + x2) C (setInput S) c = true := by
          simpa [GateOp.eval] using hw'
        have hRBa : a < x1 + x2 + j := hRB' a (by rw [hac]; simp)
        have hRBc : c < x1 + x2 + j := hRB' c (by rw [hac]; simp)
        obtain ⟨ia, hia, hA⟩ := (ih a hRBa hwa.1).2 false ha
        obtain ⟨ic, hic, hCc⟩ := (ih c hRBc hwa.2).2 true hc
        have hne : ia ≠ ic := by
          rintro rfl
          rw [hia] at hic
          exact Bool.false_ne_true hic
        refine ⟨capAdd 1 (capAdd 1 ((setList S).map fun _ => 0) (uv (setList S) ia))
          (uv (setList S) ic), ?_, ?_⟩
        · rw [hRVj, s2230_FR_and _ _ _ _ ho, hmapR, hac]
          simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
          exact mem_andStep_of _ _ _ _ _
            (mem_andStep_of _ _ _ _ _ (List.mem_singleton_self _) hA) hCc
        · intro e he
          unfold uv at he
          rw [capAdd_map, capAdd_map] at he
          simp only [List.mem_map] at he
          obtain ⟨t, _, rfl⟩ := he
          split_ifs <;> omega
      · obtain ⟨i, hi, hwi⟩ := hor_true ho
        obtain ⟨v, hv, hle⟩ := (ih i (hRB' i hi) hwi).1
        exact ⟨v, hor_mem ho i hi v hv, hle⟩
    · intro b hb
      rcases hx4 b _ hb with ⟨hlt, _⟩ | ⟨j', _, hjj, ho, hins⟩
      · omega
      · have hjj' : j' = j := by omega
        subst hjj'
        obtain ⟨i, hi, hwi⟩ := hor_true ho
        obtain ⟨ia, hia, hA⟩ := (ih i (hRB' i hi) hwi).2 b (hins i hi)
        exact ⟨ia, hia, hor_mem ho i hi _ hA⟩

end PEqualNP.Outside.L_meta_6579

theorem PEqualNP.Outside.L_meta_6579 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Bool → Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x3 → (∀ (x6 : Bool), ∀ x7 ∈ x4 x6, x7 < x1 + x2 ∧ Decidable.decide (x1 ≤ x7) = x6 ∨ ∃ x9 < x3.size, x7 = x1 + x2 + x9 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).inputs, x10 ∈ x4 x6) → (∀ x7 < x3.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : ℕ) (x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).inputs = [x10, x11] ∧ x10 ∈ x4 Bool.false ∧ x11 ∈ x4 Bool.true) → PEqualNP.ReadK.IsReadK (x1 + x2) x3 (1 : ℕ) := by
  intro x1 x2 C x4 hC hx4 hand S hS
  have hout : PEqualNP.Outside.L_meta_6579.s2230_W (x1 + x2) C (PEqualNP.ReadK.setInput S)
      C.output = true := hS.1
  obtain ⟨⟨v, hv, hle⟩, _⟩ :=
    PEqualNP.Outside.L_meta_6579.inv x1 x2 C x4 hC hx4 hand S C.output hout
  unfold PEqualNP.ReadK.readsAtMost
  apply List.any_eq_true.2
  refine ⟨v, hv, ?_⟩
  apply List.all_eq_true.2
  intro a ha
  exact decide_eq_true (hle a ha)
