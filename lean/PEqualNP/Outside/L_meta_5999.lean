import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5999

open PEqualNP.CircuitLowerBounds

-- Renaming the 26 inputs: every reference to an input wire k below 26 is replaced by s k.
-- Gate wires keep their numbers, so the gates stay in place and still read earlier wires.

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

def ren (s : Fin 26 → Fin 26) (k : ℕ) : ℕ := if h : k < 26 then (s ⟨k, h⟩ : ℕ) else k

def reGate (s : Fin 26 → Fin 26) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren s)⟩

lemma getD_ren (s : Fin 26 → Fin 26) (x : Fin 26 → Bool) (t : List Bool) (k : ℕ) :
    (List.ofFn (x ∘ s) ++ t).getD k false = (List.ofFn x ++ t).getD (ren s k) false := by
  unfold ren
  by_cases h : k < 26
  · simp only [h, ↓reduceDIte]
    have h1 : k < (List.ofFn (x ∘ s)).length := by rw [List.length_ofFn]; exact h
    have h2 : (s ⟨k, h⟩ : ℕ) < (List.ofFn x).length := by
      rw [List.length_ofFn]; exact (s ⟨k, h⟩).isLt
    rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2]
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
    rw [List.getElem_ofFn, List.getElem_ofFn]
    rfl
  · simp only [h, ↓reduceDIte]
    have h1 : (List.ofFn (x ∘ s)).length ≤ k := by rw [List.length_ofFn]; omega
    have h2 : (List.ofFn x).length ≤ k := by rw [List.length_ofFn]; omega
    rw [List.getD_append_right _ _ _ _ h1, List.getD_append_right _ _ _ _ h2]
    simp

lemma step_ren (s : Fin 26 → Fin 26) (x : Fin 26 → Bool) (t : List Bool) (g : Gate) :
    stepW (List.ofFn x ++ t) (reGate s g) =
      List.ofFn x ++ (t ++ [g.op.eval (g.inputs.map fun i =>
        (List.ofFn (x ∘ s) ++ t).getD i false)]) := by
  have hm : ((g.inputs.map (ren s)).map fun i => (List.ofFn x ++ t).getD i false)
      = g.inputs.map fun i => (List.ofFn (x ∘ s) ++ t).getD i false := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => (getD_ren s x t i).symm)
  show (List.ofFn x ++ t) ++
    [g.op.eval ((g.inputs.map (ren s)).map fun i => (List.ofFn x ++ t).getD i false)] = _
  rw [hm, List.append_assoc]

lemma step_orig (s : Fin 26 → Fin 26) (x : Fin 26 → Bool) (t : List Bool) (g : Gate) :
    stepW (List.ofFn (x ∘ s) ++ t) g =
      List.ofFn (x ∘ s) ++ (t ++ [g.op.eval (g.inputs.map fun i =>
        (List.ofFn (x ∘ s) ++ t).getD i false)]) := by
  show (List.ofFn (x ∘ s) ++ t) ++
    [g.op.eval (g.inputs.map fun i => (List.ofFn (x ∘ s) ++ t).getD i false)] = _
  rw [List.append_assoc]

lemma fold_ren (s : Fin 26 → Fin 26) (x : Fin 26 → Bool) (gs : List Gate) :
    ∀ t : List Bool, ∃ t' : List Bool,
      (gs.map (reGate s)).foldl stepW (List.ofFn x ++ t) = List.ofFn x ++ t' ∧
      gs.foldl stepW (List.ofFn (x ∘ s) ++ t) = List.ofFn (x ∘ s) ++ t' := by
  induction gs with
  | nil => intro t; exact ⟨t, rfl, rfl⟩
  | cons g gs ih =>
    intro t
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, step_ren, step_orig]
    exact ih _

lemma ren_lt (s : Fin 26 → Fin 26) (i m : ℕ) (hi : i < 26 + m) : ren s i < 26 + m := by
  unfold ren
  by_cases h : i < 26
  · simp only [h, ↓reduceDIte]
    have := (s ⟨i, h⟩).isLt
    omega
  · simp only [h, ↓reduceDIte]
    exact hi

lemma gateAt_map (s : Fin 26 → Fin 26) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt ⟨C.gates.map (reGate s), ren s C.output⟩ j
      = reGate s (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  have hj2 : j < (C.gates.map (reGate s)).length := by rw [List.length_map]; exact hj
  show (C.gates.map (reGate s)).getD j _ = reGate s (C.gates.getD j _)
  rw [List.getD_eq_getElem _ _ hj2, List.getD_eq_getElem _ _ hj, List.getElem_map]

lemma main (s : Fin 26 → Fin 26) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 26 C) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 26 D ∧ D.size = C.size ∧
      ∀ (x : Fin 26 → Bool), D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ s)) := by
  obtain ⟨hAO, hRB, hLen⟩ := hC
  refine ⟨⟨C.gates.map (reGate s), ren s C.output⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact hAO g' hg'
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa using hj
    rw [gateAt_map s C j hj'] at hi
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
    exact ren_lt s i' j (hRB j hj' i' hi')
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    show (g'.inputs.map (ren s)).length = 2
    rw [List.length_map]
    exact hLen g' hg'
  · simp [Circuit.size]
  · intro x
    obtain ⟨t', h1, h2⟩ := fold_ren s x C.gates []
    simp only [List.append_nil] at h1 h2
    unfold Circuit.eval
    rw [wires_eq, wires_eq]
    show ((C.gates.map (reGate s)).foldl stepW (List.ofFn x)).getD (ren s C.output) false
      = (C.gates.foldl stepW (List.ofFn (x ∘ s))).getD C.output false
    rw [h1, h2]
    exact (getD_ren s x t' C.output).symm

end PEqualNP.Outside.L_meta_5999

theorem PEqualNP.Outside.L_meta_5999 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ) → Fin (26 : ℕ)), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧ x4.size = x1.size ∧ ∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x5) = x1.eval (List.ofFn fun (x6 : Fin (26 : ℕ)) => x5 (x2 x6)) := by
  intro C s hC
  exact PEqualNP.Outside.L_meta_5999.main s C hC
