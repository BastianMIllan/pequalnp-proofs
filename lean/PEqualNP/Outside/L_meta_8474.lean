import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8474

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma mono {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true)
    (hN : ∀ k, ∀ hk : k < C.gates.length,
      ¬ (C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or) →
      value C x (n + k) = true → value C y (n + k) = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      by_cases hop : C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or
      · exact gate_mono C (w - n) hk hop x y fun r _ hlt => ih r (by omega)
      · exact hN (w - n) hk hop
    · simp [missing_value C x w (by unfold Circuit.size; omega)]


lemma andOr_mono {n : ℕ} (C : Circuit) (hC : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  apply mono C x y hxy
  intro k hk hn
  exact (hn (hC _ (List.getElem_mem hk))).elim



end PEqualNP.Outside.L_meta_8474

theorem PEqualNP.Outside.L_meta_8474 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Bool) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x1) x3 → (∀ (x5 x6 : Fin x1), x2 x5 x6 = Bool.true → PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd x1 x5) (Fin.natAdd x1 x6)) = Bool.true) → (∀ (x6 : Finset (Fin x1)), (PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 fun (x7 : Fin (x1 + x1)) => Fin.addCases (fun (x8 : Fin x1) => Decidable.decide (x8 ∈ x6)) (fun (x8 : Fin x1) => Decidable.decide (∀ x9 ∈ x6, x2 x9 x8 = Bool.false)) x7) = Bool.false) → ∀ (x7 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), x2 x8 x9 = Bool.true ∧ x7 (Fin.castAdd x1 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true) := by
  intro N R C hAO hpos hneg x
  have hmono : ∀ y z : Fin (N + N) → Bool, (∀ i, y i = true → z i = true) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C y = true →
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true :=
    fun y z h => PEqualNP.Outside.L_meta_8474.andOr_mono C hAO.1 y z h C.output
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · intro hx
    by_contra hne
    push_neg at hne
    let S : Finset (Fin N) := Finset.univ.filter (fun a => x (Fin.castAdd N a) = true)
    have h2 := hmono x (fun (x7 : Fin (N + N)) => Fin.addCases
      (fun (x8 : Fin N) => decide (x8 ∈ S))
      (fun (x8 : Fin N) => decide (∀ x9 ∈ S, R x9 x8 = false)) x7) ?_ hx
    · rw [hneg S] at h2
      exact absurd h2 (by simp)
    · intro i
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i
      · intro ha
        simp [S, ha]
      · intro hb
        simp only [Fin.addCases_right, decide_eq_true_eq]
        intro a ha
        have ha' : x (Fin.castAdd N a) = true := by simpa [S] using ha
        by_contra hR
        have hR' : R a b = true := by simpa using hR
        exact hne a b hR' ha' hb
  · rintro ⟨a, b, hR, ha, hb⟩
    apply hmono (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd N a) (Fin.natAdd N b)) x _ (hpos a b hR)
    intro i hi
    simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
