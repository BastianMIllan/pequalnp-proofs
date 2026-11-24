import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3270

open PEqualNP.CircuitLowerBounds

def mkG (o : GateOp) (a b : ℕ) : Gate := { op := o, inputs := [a, b] }

def C0 : Circuit := { gates := [
  mkG GateOp.and 0 1, mkG GateOp.or 0 14, mkG GateOp.or 1 14,
  mkG GateOp.or 7 8, mkG GateOp.or 17 10, mkG GateOp.and 15 18,
  mkG GateOp.or 13 7, mkG GateOp.or 20 9, mkG GateOp.and 16 21,
  mkG GateOp.or 12 13, mkG GateOp.or 23 8, mkG GateOp.and 2 24,
  mkG GateOp.or 11 12, mkG GateOp.or 26 7, mkG GateOp.and 3 27,
  mkG GateOp.or 10 11, mkG GateOp.or 29 13, mkG GateOp.and 4 30,
  mkG GateOp.or 9 10, mkG GateOp.or 32 12, mkG GateOp.and 5 33,
  mkG GateOp.or 8 9, mkG GateOp.or 35 11, mkG GateOp.and 6 36,
  mkG GateOp.or 19 22, mkG GateOp.or 38 25, mkG GateOp.or 39 28,
  mkG GateOp.or 40 31, mkG GateOp.or 41 34, mkG GateOp.or 42 37], output := 43 }

def A (a b : Bool) : Bool := GateOp.eval GateOp.and [a, b]
def O (a b : Bool) : Bool := GateOp.eval GateOp.or [a, b]

lemma hA (a b : Bool) : A a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide
lemma hO (a b : Bool) : O a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

def P (x : Fin 14 → Bool) (k : Fin 7) : Bool := x (Fin.castAdd 7 k)
def L (x : Fin 14 → Bool) (k : Fin 7) : Bool := x (Fin.natAdd 7 k)

def E (x : Fin 14 → Bool) : Bool :=
  O (O (O (O (O (O
    (A (O (P x 0) (A (P x 0) (P x 1))) (O (O (L x 0) (L x 1)) (L x 3)))
    (A (O (P x 1) (A (P x 0) (P x 1))) (O (O (L x 6) (L x 0)) (L x 2))))
    (A (P x 2) (O (O (L x 5) (L x 6)) (L x 1))))
    (A (P x 3) (O (O (L x 4) (L x 5)) (L x 0))))
    (A (P x 4) (O (O (L x 3) (L x 4)) (L x 6))))
    (A (P x 5) (O (O (L x 2) (L x 3)) (L x 5))))
    (A (P x 6) (O (O (L x 1) (L x 2)) (L x 4)))

lemma hE (x : Fin 14 → Bool) : C0.eval (List.ofFn x) = E x := by
  simp only [Circuit.eval, Circuit.wires, C0, mkG, List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero]
  rfl

lemma fwd (x : Fin 14 → Bool) (h : E x = true) : ∃ p l : Fin 7, (p + l = 0 ∨ p + l = 1 ∨ p + l = 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
  simp only [E, hA, hO] at h
  rcases h with (((((⟨hp | ⟨hp, -⟩, (hl | hl) | hl⟩ | ⟨hp | ⟨-, hp⟩, (hl | hl) | hl⟩) | ⟨hp, (hl | hl) | hl⟩) | ⟨hp, (hl | hl) | hl⟩) | ⟨hp, (hl | hl) | hl⟩) | ⟨hp, (hl | hl) | hl⟩) | ⟨hp, (hl | hl) | hl⟩
  · exact ⟨0, 0, by decide, hp, hl⟩
  · exact ⟨0, 1, by decide, hp, hl⟩
  · exact ⟨0, 3, by decide, hp, hl⟩
  · exact ⟨0, 0, by decide, hp, hl⟩
  · exact ⟨0, 1, by decide, hp, hl⟩
  · exact ⟨0, 3, by decide, hp, hl⟩
  · exact ⟨1, 6, by decide, hp, hl⟩
  · exact ⟨1, 0, by decide, hp, hl⟩
  · exact ⟨1, 2, by decide, hp, hl⟩
  · exact ⟨1, 6, by decide, hp, hl⟩
  · exact ⟨1, 0, by decide, hp, hl⟩
  · exact ⟨1, 2, by decide, hp, hl⟩
  · exact ⟨2, 5, by decide, hp, hl⟩
  · exact ⟨2, 6, by decide, hp, hl⟩
  · exact ⟨2, 1, by decide, hp, hl⟩
  · exact ⟨3, 4, by decide, hp, hl⟩
  · exact ⟨3, 5, by decide, hp, hl⟩
  · exact ⟨3, 0, by decide, hp, hl⟩
  · exact ⟨4, 3, by decide, hp, hl⟩
  · exact ⟨4, 4, by decide, hp, hl⟩
  · exact ⟨4, 6, by decide, hp, hl⟩
  · exact ⟨5, 2, by decide, hp, hl⟩
  · exact ⟨5, 3, by decide, hp, hl⟩
  · exact ⟨5, 5, by decide, hp, hl⟩
  · exact ⟨6, 1, by decide, hp, hl⟩
  · exact ⟨6, 2, by decide, hp, hl⟩
  · exact ⟨6, 4, by decide, hp, hl⟩

lemma bwd (x : Fin 14 → Bool) (p l : Fin 7) (hpl : p + l = 0 ∨ p + l = 1 ∨ p + l = 3)
    (hp : P x p = true) (hl : L x l = true) : E x = true := by
  simp only [E, hA, hO]
  have h7 : ∀ q : Fin 7, q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 := by decide
  rcases h7 p with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases h7 l with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | (exfalso; revert hpl; decide) | simp [hp, hl]

lemma gates_ok : ∀ (k : ℕ) (g : Gate), C0.gates[k]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ u v : ℕ, g.inputs = [u, v] ∧ u ≠ v ∧ u < 14 + k ∧ v < 14 + k := by
  intro k g hk
  have hlen30 : C0.gates.length = 30 := rfl
  have hl : k < C0.gates.length := by
    by_contra h'
    rw [List.getElem?_eq_none (by omega)] at hk
    cases hk
  have hg : g = C0.gates[k]'hl := by
    rw [List.getElem?_eq_getElem hl] at hk
    exact (Option.some.inj hk).symm
  subst hg
  have hk30 : k < 30 := by omega
  interval_cases k <;> exact ⟨by first | exact Or.inl rfl | exact Or.inr rfl, _, _, rfl, by decide⟩

lemma read_ok : ∀ k : ℕ, k + 1 < C0.size → ∃ (k' : ℕ) (g : Gate), C0.gates[k']? = some g ∧ 14 + k ∈ g.inputs := by
  intro k hk
  have h30 : C0.size = 30 := rfl
  have hk' : k < 29 := by omega
  have hall : ∀ k < 29, ∃ k' < 30, 14 + k ∈ (C0.gates.getD k' (mkG GateOp.and 0 0)).inputs := by decide
  obtain ⟨k', hk'lt, hm⟩ := hall k hk'
  have hl : k' < C0.gates.length := by
    have hlen30 : C0.gates.length = 30 := rfl
    omega
  refine ⟨k', C0.gates[k'], List.getElem?_eq_getElem hl, ?_⟩
  rw [List.getD_eq_getElem _ _ hl] at hm
  exact hm

lemma last_ok : ∃ j : ℕ, j < C0.size ∧ (∀ i : Fin 14, (C0.wires (List.ofFn (fun t : Fin 14 => decide (t = i)))).getD (14 + j) false = false) ∧ (∃ x : Fin 14 → Bool, (C0.wires (List.ofFn x)).getD (14 + j) false = true ∧ ¬ ∃ p l : Fin 7, (p + l = 0 ∨ p + l = 1 ∨ p + l = 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧ ∃ (k k' : ℕ) (g g' : Gate), k ≠ k' ∧ C0.gates[k]? = some g ∧ C0.gates[k']? = some g' ∧ 14 + j ∈ g.inputs ∧ 14 + j ∈ g'.inputs := by
  refine ⟨0, by decide, by decide, ⟨fun t => decide (t = 0 ∨ t = 1), by decide, by decide⟩, 1, 2, mkG GateOp.or 0 14, mkG GateOp.or 1 14, by decide, rfl, rfl, by decide, by decide⟩

end PEqualNP.Outside.L_meta_3270

theorem PEqualNP.Outside.L_meta_3270 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size = 30 ∧ (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ u v : ℕ, g.inputs = [u, v] ∧ u ≠ v ∧ u < 14 + k ∧ v < 14 + k) ∧ C.output + 1 = 14 + C.size ∧ (∀ k : ℕ, k + 1 < C.size → ∃ (k' : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k']? = some g ∧ 14 + k ∈ g.inputs) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7, (p + l = 0 ∨ p + l = 1 ∨ p + l = 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧ (∃ j : ℕ, j < C.size ∧ (∀ i : Fin 14, (C.wires (List.ofFn (fun t : Fin 14 => decide (t = i)))).getD (14 + j) false = false) ∧ (∃ x : Fin 14 → Bool, (C.wires (List.ofFn x)).getD (14 + j) false = true ∧ ¬ ∃ p l : Fin 7, (p + l = 0 ∨ p + l = 1 ∨ p + l = 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧ ∃ (k k' : ℕ) (g g' : PEqualNP.CircuitLowerBounds.Gate), k ≠ k' ∧ C.gates[k]? = some g ∧ C.gates[k']? = some g' ∧ 14 + j ∈ g.inputs ∧ 14 + j ∈ g'.inputs) :=
  ⟨PEqualNP.Outside.L_meta_3270.C0, rfl, PEqualNP.Outside.L_meta_3270.gates_ok, rfl,
    PEqualNP.Outside.L_meta_3270.read_ok,
    fun x => by
      rw [PEqualNP.Outside.L_meta_3270.hE]
      exact ⟨PEqualNP.Outside.L_meta_3270.fwd x, fun ⟨p, l, hpl, hp, hl⟩ => PEqualNP.Outside.L_meta_3270.bwd x p l hpl hp hl⟩,
    PEqualNP.Outside.L_meta_3270.last_ok⟩
