import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7370

open PEqualNP.CircuitLowerBounds

def fm (i : ℕ) : ℕ := if i < 9 then i else if i < 12 then i + 1 else i + 2

def tg (g : Gate) : Gate := ⟨g.op, g.inputs.map fm⟩

def tc (C : Circuit) : Circuit := ⟨C.gates.map tg, C.output⟩

theorem fm_lt (i n : ℕ) (hn : 12 ≤ n) (hi : i < n) : fm i < n + 2 := by
  unfold fm; split_ifs <;> omega

theorem fm_eq (n : ℕ) (hn : 12 ≤ n) : fm n = n + 2 := by
  unfold fm; split_ifs <;> omega

theorem fm_gt (i n : ℕ) (hn : 12 ≤ n) (hi : n < i) : n + 2 < fm i := by
  unfold fm; split_ifs <;> omega

theorem fold_inv (gs : List Gate) : ∀ (w w' : List Bool), 12 ≤ w.length → w'.length = w.length + 2 →
    (∀ i, w'.getD (fm i) false = w.getD i false) →
    ∀ i, ((gs.map tg).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD (fm i) false
      = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false := by
  induction gs with
  | nil => intro w w' _ _ h i; exact h i
  | cons g gs ih =>
    intro w w' hl hl' h
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp only [List.length_append, List.length_singleton]; omega
    · simp only [List.length_append, List.length_singleton]; omega
    · intro i
      have hv : (tg g).op.eval ((tg g).inputs.map fun i => w'.getD i false)
          = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp only [tg, List.map_map]
        congr 1
        apply List.map_congr_left
        intro j _
        exact h j
      rw [hv]
      rcases lt_trichotomy i w.length with hi | hi | hi
      · have h2 : fm i < w'.length := by rw [hl']; exact fm_lt i _ hl hi
        rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ h2]
        exact h i
      · subst hi
        rw [fm_eq _ hl, ← hl']
        simp [List.getD_append_right]
      · have h3 := fm_gt i _ hl hi
        rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega),
          List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega)]

end PEqualNP.Outside.L_meta_7370

theorem PEqualNP.Outside.L_meta_7370 : have x1 : ℕ → ℕ := fun (x1 : ℕ) => if x1 < (9 : ℕ) then x1 else if x1 < (12 : ℕ) then x1 + (1 : ℕ) else x1 + (2 : ℕ); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     x2.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } →       ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.Monotone2 x5 ∧           x5.size = x2.size ∧             x5.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧               ∀ (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ),                 have x8 : Fin (24 : ℕ) → Bool := fun (x8 : Fin (24 : ℕ)) => x6 (Fin.ofNat (26 : ℕ) (x1 ↑x8));                 (x5.wires (List.ofFn x6)).getD (x1 x7) Bool.false = (x2.wires (List.ofFn x8)).getD x7 Bool.false := by
  intro x1 C hM hh
  refine ⟨PEqualNP.Outside.L_meta_7370.tc C, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_7370.tc, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨h1, h2⟩ := hM g0 hg0
    exact ⟨h1, by simpa [PEqualNP.Outside.L_meta_7370.tg] using h2⟩
  · simp [PEqualNP.Outside.L_meta_7370.tc, PEqualNP.CircuitLowerBounds.Circuit.size]
  · cases hgs : C.gates with
    | nil => rw [hgs] at hh; simp at hh
    | cons g gs =>
      rw [hgs] at hh
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      simp [PEqualNP.Outside.L_meta_7370.tc, PEqualNP.Outside.L_meta_7370.tg, hgs,
        PEqualNP.Outside.L_meta_7370.fm]
  · intro x6 x7
    show ((PEqualNP.Outside.L_meta_7370.tc C).wires (List.ofFn x6)).getD (PEqualNP.Outside.L_meta_7370.fm x7) false
      = (C.wires (List.ofFn fun x8 : Fin 24 => x6 (Fin.ofNat 26 (PEqualNP.Outside.L_meta_7370.fm x8.val)))).getD x7 false
    apply PEqualNP.Outside.L_meta_7370.fold_inv
    · simp
    · simp
    · intro i
      by_cases hi : i < 24
      · have hf : PEqualNP.Outside.L_meta_7370.fm i < 26 := by
          unfold PEqualNP.Outside.L_meta_7370.fm; split_ifs <;> omega
        rw [List.getD_eq_getElem _ _ (by simpa using hf), List.getD_eq_getElem _ _ (by simpa using hi)]
        simp only [List.getElem_ofFn]
        congr 1
        ext
        simp [Fin.ofNat, Nat.mod_eq_of_lt hf]
      · have hf : 26 ≤ PEqualNP.Outside.L_meta_7370.fm i := by
          unfold PEqualNP.Outside.L_meta_7370.fm; split_ifs <;> omega
        rw [List.getD_eq_default _ _ (by simpa using hf), List.getD_eq_default _ _ (by simp; omega)]
