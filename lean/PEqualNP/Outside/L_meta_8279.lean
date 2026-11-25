import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8279

open PEqualNP.CircuitLowerBounds

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def lo (g : Gate) : Fin 89 :=
  ⟨min (min (g.inputs.getD 0 0) (g.inputs.getD 1 0)) 88, by omega⟩

def hi (g : Gate) : Fin 89 :=
  ⟨min (max (g.inputs.getD 0 0) (g.inputs.getD 1 0)) 88, by omega⟩

def T (g : Gate) : Bool × Fin 89 × Fin 89 := (isAnd g.op, lo g, hi g)

def stepT (w : List Bool) (t : Bool × Fin 89 × Fin 89) : List Bool :=
  w ++ [bif t.1 then w.getD (↑t.2.1) false && w.getD (↑t.2.2) false
    else w.getD (↑t.2.1) false || w.getD (↑t.2.2) false]

theorem bounds (g : Gate) (m : ℕ) (hl : g.inputs.length = 2) (hb : ∀ k ∈ g.inputs, k < m) :
    (lo g).val < m ∧ (hi g).val < m ∧ lo g ≤ hi g := by
  obtain ⟨op, ins⟩ := g
  match ins, hl with
  | [a, b], _ =>
    have h1 := hb a (by simp)
    have h2 := hb b (by simp)
    simp only [lo, hi, Fin.mk_le_mk, List.getD_cons_zero, List.getD_cons_succ]
    simp only [Nat.min_def, Nat.max_def]
    split_ifs <;> omega

theorem step_eq (g : Gate) (w : List Bool) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hl : g.inputs.length = 2) (hb : ∀ i ∈ g.inputs, i ≤ 88) :
    stepT w (T g) = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  obtain ⟨op, ins⟩ := g
  match ins, hl with
  | [a, b], _ =>
    have ha : a ≤ 88 := hb a (by simp)
    have hb' : b ≤ 88 := hb b (by simp)
    have e1 : min (min a b) 88 = min a b := Nat.min_eq_left (le_trans (Nat.min_le_left _ _) ha)
    have e2 : min (max a b) 88 = max a b := Nat.min_eq_left (max_le ha hb')
    simp only at hop
    rcases hop with h | h <;> subst h <;>
      simp only [stepT, T, lo, hi, isAnd, GateOp.eval, List.getD_cons_zero,
        List.getD_cons_succ, e1, e2, List.map_cons, List.map_nil, Bool.cond_true, Bool.cond_false,
        List.all_cons, List.all_nil, List.any_cons, List.any_nil, id, Bool.and_true,
        Bool.or_false] <;>
      rcases le_total a b with hab | hab <;>
      simp [Nat.min_eq_left hab, Nat.max_eq_right hab, Nat.min_eq_right hab,
        Nat.max_eq_left hab, Bool.and_comm, Bool.or_comm]

end PEqualNP.Outside.L_meta_8279

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_8279 in
theorem PEqualNP.Outside.L_meta_8279 : have x1 : (Fin (63 : ℕ) → Bool) → (Fin (63 : ℕ) → Fin (89 : ℕ)) → (Fin (63 : ℕ) → Fin (89 : ℕ)) → (Fin (26 : ℕ) → Bool) → Bool := fun (x1 : Fin (63 : ℕ) → Bool) (x2 x3 : Fin (63 : ℕ) → Fin (89 : ℕ)) (x4 : Fin (26 : ℕ) → Bool) => (List.foldl (fun (x5 : List Bool) (x6 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) => x5 ++ [bif x6.1 then x5.getD (↑x6.2.1) Bool.false && x5.getD (↑x6.2.2) Bool.false else x5.getD (↑x6.2.1) Bool.false || x5.getD (↑x6.2.2) Bool.false]) (List.ofFn x4) (List.ofFn fun (x5 : Fin (63 : ℕ)) => (x1 x5, x2 x5, x3 x5))).getD (88 : ℕ) Bool.false; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → x2.size = (63 : ℕ) → x2.output = (88 : ℕ) → ∃ (x6 : Fin (63 : ℕ) → Bool) (x7 : Fin (63 : ℕ) → Fin (89 : ℕ)) (x8 : Fin (63 : ℕ) → Fin (89 : ℕ)), (∀ (x9 : Fin (63 : ℕ)), ↑(x7 x9) < (26 : ℕ) + ↑x9 ∧ ↑(x8 x9) < (26 : ℕ) + ↑x9 ∧ x7 x9 ≤ x8 x9) ∧ ∀ (x9 : Fin (26 : ℕ) → Bool), x1 x6 x7 x8 x9 = PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x9 := by
  intro x1 C hC hs ho
  obtain ⟨hAO, hRB, h2⟩ := hC
  have hl : C.gates.length = 63 := hs
  have hrb : ∀ j (hj : j < C.gates.length), ∀ k ∈ (C.gates[j]'hj).inputs, k < 26 + j := by
    intro j hj k hk
    have := hRB j hj k
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ hj] at this
    exact this hk
  refine ⟨fun i => (T (C.gates[i.val]'(by omega))).1,
    fun i => (T (C.gates[i.val]'(by omega))).2.1,
    fun i => (T (C.gates[i.val]'(by omega))).2.2, ?_, ?_⟩
  · intro i
    exact bounds _ _ (h2 _ (List.getElem_mem _)) (hrb i.val (by omega))
  · intro x9
    have hofn : (List.ofFn fun i : Fin 63 => ((T (C.gates[i.val]'(by omega))).1,
        (T (C.gates[i.val]'(by omega))).2.1, (T (C.gates[i.val]'(by omega))).2.2)) =
        C.gates.map T := by
      apply List.ext_getElem
      · simp [hl]
      · intro n h1 h3
        rw [List.getElem_ofFn, List.getElem_map]
    have key : List.foldl stepT (List.ofFn x9) (List.ofFn fun i : Fin 63 =>
        ((T (C.gates[i.val]'(by omega))).1,
        (T (C.gates[i.val]'(by omega))).2.1, (T (C.gates[i.val]'(by omega))).2.2)) =
        C.wires (List.ofFn x9) := by
      rw [hofn, List.foldl_map]
      unfold Circuit.wires
      apply List.foldl_ext
      intro w g hg
      apply step_eq g w (hAO g hg) (h2 g hg)
      intro k hk
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      have := hrb j hj k hk
      omega
    show (List.foldl stepT (List.ofFn x9) _).getD 88 false = _
    rw [key]
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, ho]
