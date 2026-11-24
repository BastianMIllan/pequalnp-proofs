import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2854

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def runWires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl stepWire x

lemma runWires_append (gs1 gs2 : List Gate) (x : List Bool) :
    runWires (gs1 ++ gs2) x = runWires gs2 (runWires gs1 x) := by
  simp [runWires, List.foldl_append]

lemma runWires_singleton (g : Gate) (x : List Bool) :
    runWires [g] x = stepWire x g := rfl

lemma runWires_length (gs : List Gate) (x : List Bool) :
    (runWires gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [runWires]
  | cons g gs ih =>
    change (runWires gs (stepWire x g)).length = x.length + (gs.length + 1)
    rw [ih]
    simp [stepWire]
    omega

lemma getD_append_left_lt (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_singleton_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_of_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rfl

lemma runWires_getD_prefix (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (runWires gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (runWires gs (stepWire x g)).getD i false = x.getD i false
    have hlt : i < (stepWire x g).length := by
      simp [stepWire]
      omega
    rw [ih (stepWire x g) hlt]
    exact getD_append_left_lt x _ i hi

lemma wires_eq_runWires (C : Circuit) (x : List Bool) :
    C.wires x = runWires C.gates x := rfl

lemma wires_getD_gate (C : Circuit) (x : List Bool) (k : ℕ) (hk : k < C.gates.length) :
    (C.wires x).getD (x.length + k) false =
      (C.gates[k]).op.eval
        ((C.gates[k]).inputs.map fun a =>
          if a < x.length + k then (C.wires x).getD a false else false) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simpa [List.append_assoc] using h1.symm
  let pref := runWires (C.gates.take k) x
  have hpref_len : pref.length = x.length + k := by
    change (runWires (C.gates.take k) x).length = x.length + k
    rw [runWires_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hwires : C.wires x = runWires (C.gates.drop (k + 1)) (stepWire pref C.gates[k]) := by
    rw [wires_eq_runWires]
    conv_lhs => rw [hsplit]
    rw [runWires_append, runWires_append, runWires_singleton]
  have hstep_len : x.length + k < (stepWire pref C.gates[k]).length := by
    simp [stepWire, hpref_len]
  rw [hwires, runWires_getD_prefix _ _ _ hstep_len]
  have hstep_eq : (stepWire pref C.gates[k]).getD (x.length + k) false =
      (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun a => pref.getD a false) := by
    rw [← hpref_len]
    exact getD_append_singleton_eq pref _
  rw [hstep_eq]
  congr 1
  apply List.map_congr_left
  intro a _
  by_cases ha : a < x.length + k
  · rw [if_pos ha]
    have ha' : a < (stepWire pref C.gates[k]).length := by omega
    rw [runWires_getD_prefix _ _ _ ha']
    have ha'' : a < pref.length := by omega
    exact (getD_append_left_lt pref _ a ha'').symm
  · rw [if_neg ha]
    exact getD_of_le pref a (by omega)

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

lemma wire_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hR : ReadsBack n C)
    (k : ℕ) (hk : k < C.gates.length) :
    (C.wires (List.ofFn x)).getD (n + k) false =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun a =>
        (C.wires (List.ofFn x)).getD a false) := by
  have h := wires_getD_gate C (List.ofFn x) k hk
  rw [List.length_ofFn] at h
  rw [h, gateAt_eq C k hk]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hlt := hR k hk a (by rw [gateAt_eq C k hk]; exact ha)
  rw [if_pos hlt]

lemma wire_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = (List.ofFn x).getD i false := by
  rw [wires_eq_runWires, runWires_getD_prefix _ _ _ (by simpa using hi)]

lemma eval_mono (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
    intro hf i hi
    exact h i hi (hf i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    rintro ⟨i, hi, hf⟩
    exact ⟨i, hi, h i hi hf⟩

end PEqualNP.Outside.L_meta_2854

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_2854 : ∀ (n : ℕ) (C C' : PEqualNP.CircuitLowerBounds.Circuit) (σ : ℕ → ℕ) (m : ℕ) (x : Fin n → Bool), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C' → (∀ i < n, σ i = i) → (∀ j < C.gates.length, n ≤ σ (n + j) ∧ σ (n + j) < n + C'.gates.length) → (∀ j < C.gates.length, j ≠ m → (PEqualNP.MetaComplexity.NestedCover.gateAt C' (σ (n + j) - n)).op = (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C' (σ (n + j) - n)).inputs = (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map σ) → (((C'.wires (List.ofFn x)).getD (σ (n + m)) false = true → (C.wires (List.ofFn x)).getD (n + m) false = true) → ∀ j < C.gates.length, (C'.wires (List.ofFn x)).getD (σ (n + j)) false = true → (C.wires (List.ofFn x)).getD (n + j) false = true) ∧ ((C'.wires (List.ofFn x)).getD (σ (n + m)) false = (C.wires (List.ofFn x)).getD (n + m) false → ∀ j < C.gates.length, (C'.wires (List.ofFn x)).getD (σ (n + j)) false = (C.wires (List.ofFn x)).getD (n + j) false) := by
  intro n C C' σ m x hM hR hR' hσin hσrange hcopy
  have hcopyval : ∀ j < C.gates.length, j ≠ m →
      (C'.wires (List.ofFn x)).getD (σ (n + j)) false =
        (gateAt C j).op.eval ((gateAt C j).inputs.map fun a =>
          (C'.wires (List.ofFn x)).getD (σ a) false) := by
    intro j hj hjm
    obtain ⟨h1, h2⟩ := hσrange j hj
    obtain ⟨hop, hin⟩ := hcopy j hj hjm
    have hk : σ (n + j) - n < C'.gates.length := by omega
    have hw := PEqualNP.Outside.L_meta_2854.wire_gate n C' x hR' (σ (n + j) - n) hk
    rw [show n + (σ (n + j) - n) = σ (n + j) by omega] at hw
    rw [hw, hop, hin, List.map_map]
    rfl
  have hinput : ∀ i < n, (C'.wires (List.ofFn x)).getD (σ i) false =
      (C.wires (List.ofFn x)).getD i false := by
    intro i hi
    rw [hσin i hi, PEqualNP.Outside.L_meta_2854.wire_input n C' x i hi,
      PEqualNP.Outside.L_meta_2854.wire_input n C x i hi]
  have hopmem : ∀ j < C.gates.length,
      (gateAt C j).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by
    intro j hj
    rw [PEqualNP.Outside.L_meta_2854.gateAt_eq C j hj]
    exact (hM _ (List.getElem_mem hj)).1
  refine ⟨?_, ?_⟩
  · intro hm j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases hjm : j = m
      · subst hjm; exact hm
      · rw [hcopyval j hj hjm, PEqualNP.Outside.L_meta_2854.wire_gate n C x hR j hj]
        apply PEqualNP.Outside.L_meta_2854.eval_mono _ (hopmem j hj)
        intro a ha
        have hlt := hR j hj a ha
        by_cases han : a < n
        · rw [hinput a han]; exact id
        · have hih := ih (a - n) (by omega) (by omega)
          rw [show n + (a - n) = a by omega] at hih
          exact hih
  · intro hm j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases hjm : j = m
      · subst hjm; exact hm
      · rw [hcopyval j hj hjm, PEqualNP.Outside.L_meta_2854.wire_gate n C x hR j hj]
        congr 1
        apply List.map_congr_left
        intro a ha
        have hlt := hR j hj a ha
        by_cases han : a < n
        · exact hinput a han
        · have hih := ih (a - n) (by omega) (by omega)
          rw [show n + (a - n) = a by omega] at hih
          exact hih
