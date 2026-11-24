import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2430

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def reGate (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

def rho (n2 m : ℕ) (r : Fin n2 → Fin m) (i : ℕ) : ℕ :=
  if h : i < n2 then (r ⟨i, h⟩).val else i - n2 + m

def comb (n1 n2 : ℕ) (C3 C4 : Circuit) (r : Fin n2 → Fin (n1 + C3.size)) : Circuit :=
  ⟨C3.gates ++ C4.gates.map (reGate (rho n2 (n1 + C3.size) r)) ++
    [⟨GateOp.or, [C3.output, rho n2 (n1 + C3.size) r C4.output]⟩],
    n1 + C3.size + C4.size⟩

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma getD_snoc_len (l : List Bool) (b : Bool) (n : ℕ) (h : n = l.length) :
    (l ++ [b]).getD n false = b := by
  subst h; simp

lemma fold_shape (gs : List Gate) :
    ∀ w : List Bool, ∃ u : List Bool, u.length = gs.length ∧ gs.foldl stepW w = w ++ u := by
  induction gs with
  | nil => intro w; exact ⟨[], rfl, by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨u, hu, he⟩ := ih (stepW w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ u, ?_, ?_⟩
    · simp [hu]
    · rw [List.foldl_cons, he]
      simp [stepW]

lemma fold_pair (P Q : List Bool) (ρ : ℕ → ℕ)
    (hρ : ∀ (v : List Bool) (i : ℕ), (P ++ v).getD (ρ i) false = (Q ++ v).getD i false)
    (gs : List Gate) :
    ∀ v : List Bool, ∃ v' : List Bool, v'.length = v.length + gs.length ∧
      gs.foldl stepW (Q ++ v) = Q ++ v' ∧
      (gs.map (reGate ρ)).foldl stepW (P ++ v) = P ++ v' := by
  induction gs with
  | nil => intro v; exact ⟨v, by simp, rfl, rfl⟩
  | cons g gs ih =>
    intro v
    obtain ⟨v', hl, h1, h2⟩ :=
      ih (v ++ [g.op.eval (g.inputs.map fun i => (Q ++ v).getD i false)])
    have hm : (g.inputs.map ρ).map (fun i => (P ++ v).getD i false)
        = g.inputs.map (fun i => (Q ++ v).getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => hρ v i)
    refine ⟨v', ?_, ?_, ?_⟩
    · simp at hl ⊢; omega
    · rw [List.foldl_cons, ← h1]
      simp [stepW]
    · rw [List.map_cons, List.foldl_cons, ← h2]
      have hs : stepW (P ++ v) (reGate ρ g)
          = P ++ (v ++ [g.op.eval (g.inputs.map fun i => (Q ++ v).getD i false)]) := by
        show (P ++ v) ++ [g.op.eval ((g.inputs.map ρ).map fun i => (P ++ v).getD i false)] = _
        rw [hm, List.append_assoc]
      rw [hs]

lemma rho_spec (n2 m : ℕ) (r : Fin n2 → Fin m) (P : List Bool) (hP : P.length = m)
    (v : List Bool) (i : ℕ) :
    (P ++ v).getD (rho n2 m r i) false
      = (List.ofFn (fun k => P.getD (r k).val false) ++ v).getD i false := by
  unfold rho
  by_cases h : i < n2
  · rw [dif_pos h]
    have h2 : (r ⟨i, h⟩).val < m := (r ⟨i, h⟩).isLt
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by simpa using h)]
    conv_rhs => rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · rw [dif_neg h]
    rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
    congr 1
    simp only [List.length_ofFn, hP]
    omega

lemma main (n1 n2 : ℕ) (C3 C4 : Circuit) (r : Fin n2 → Fin (n1 + C3.size))
    (ho : C3.output < n1 + C3.size) (x : Fin n1 → Bool) :
    (comb n1 n2 C3 C4 r).eval (List.ofFn x)
      = (C3.eval (List.ofFn x) ||
          C4.eval (List.ofFn fun k => (C3.wires (List.ofFn x)).getD (r k).val false)) := by
  obtain ⟨u, hu, hW3⟩ := fold_shape C3.gates (List.ofFn x)
  have hPlen : (C3.wires (List.ofFn x)).length = n1 + C3.size := by
    rw [wires_eq, hW3, List.length_append, hu, List.length_ofFn]
    rfl
  obtain ⟨v', hl, h1, h2⟩ := fold_pair (C3.wires (List.ofFn x))
    (List.ofFn fun k => (C3.wires (List.ofFn x)).getD (r k).val false)
    (rho n2 (n1 + C3.size) r)
    (rho_spec n2 (n1 + C3.size) r (C3.wires (List.ofFn x)) hPlen) C4.gates []
  simp only [List.append_nil, List.length_nil, Nat.zero_add] at h1 h2 hl
  have e4 : C4.wires (List.ofFn fun k => (C3.wires (List.ofFn x)).getD (r k).val false)
      = (List.ofFn fun k => (C3.wires (List.ofFn x)).getD (r k).val false) ++ v' := h1
  have e10 : (comb n1 n2 C3 C4 r).wires (List.ofFn x) = (C3.wires (List.ofFn x) ++ v') ++
      [GateOp.or.eval ([C3.output, rho n2 (n1 + C3.size) r C4.output].map
          fun i => (C3.wires (List.ofFn x) ++ v').getD i false)] := by
    rw [wires_eq]
    unfold comb
    simp only
    rw [List.foldl_append, List.foldl_append, ← wires_eq C3 (List.ofFn x), h2]
    rfl
  unfold Circuit.eval
  rw [e10]
  have hout : (comb n1 n2 C3 C4 r).output = n1 + C3.size + C4.gates.length := rfl
  rw [hout, getD_snoc_len _ _ _ (by rw [List.length_append, hPlen, hl])]
  show GateOp.or.eval [(C3.wires (List.ofFn x) ++ v').getD C3.output false,
    (C3.wires (List.ofFn x) ++ v').getD (rho n2 (n1 + C3.size) r C4.output) false] = _
  rw [rho_spec n2 (n1 + C3.size) r (C3.wires (List.ofFn x)) hPlen, ← e4,
    List.getD_append _ _ _ _ (by omega)]
  simp [GateOp.eval]

lemma mono (n1 n2 : ℕ) (C3 C4 : Circuit) (r : Fin n2 → Fin (n1 + C3.size))
    (h3 : PEqualNP.MetaComplexity.Monotone2 C3) (h4 : PEqualNP.MetaComplexity.Monotone2 C4) :
    PEqualNP.MetaComplexity.Monotone2 (comb n1 n2 C3 C4 r) := by
  intro g hg
  unfold comb at hg
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
  rcases hg with (hg | ⟨g', hg', rfl⟩) | rfl
  · exact h3 g hg
  · have := h4 g' hg'
    simpa [reGate] using this
  · simp

end PEqualNP.Outside.L_meta_2430

theorem PEqualNP.Outside.L_meta_2430 : ∀ (x1 x2 : ℕ) (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin x2 → Fin (x1 + x3.size)), x3.output < x1 + x3.size → PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.Monotone2 x4 → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 ∧ x9.size ≤ x3.size + x4.size + (1 : ℕ) ∧ ∀ (x10 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x9 x10 = (PEqualNP.MetaComplexity.circuitFun x1 x3 x10 || PEqualNP.MetaComplexity.circuitFun x2 x4 fun (x11 : Fin x2) => (x3.wires (List.ofFn x10)).getD (↑(x5 x11)) Bool.false) := by
  intro n1 n2 C3 C4 r ho h3 h4
  refine ⟨PEqualNP.Outside.L_meta_2430.comb n1 n2 C3 C4 r,
    PEqualNP.Outside.L_meta_2430.mono n1 n2 C3 C4 r h3 h4, ?_, ?_⟩
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.Outside.L_meta_2430.comb,
      List.length_append, List.length_map, List.length_singleton]
    omega
  · intro x
    exact PEqualNP.Outside.L_meta_2430.main n1 n2 C3 C4 r ho x
