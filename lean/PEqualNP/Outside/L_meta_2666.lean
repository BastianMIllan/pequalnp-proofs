import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2666

open PEqualNP.CircuitLowerBounds

-- A chain circuit: a constant false OR gate, then for every pair (u, v) an AND of u and v
-- followed by an OR with the running result.
def gs (n : ℕ) : List (ℕ × ℕ) → List Gate
  | [] => [⟨GateOp.or, []⟩]
  | p :: L => gs n L ++ [⟨GateOp.and, [p.1, p.2]⟩,
      ⟨GateOp.or, [n + 2 * L.length, n + 2 * L.length + 1]⟩]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (n : ℕ) (L : List (ℕ × ℕ)) (x : List Bool) : List Bool :=
  (gs n L).foldl step x

lemma W_nil (n : ℕ) (x : List Bool) : W n [] x = x ++ [false] := by
  simp [W, gs, step, GateOp.eval]

lemma W_cons (n : ℕ) (p : ℕ × ℕ) (L : List (ℕ × ℕ)) (x : List Bool) :
    W n (p :: L) x = step (step (W n L x) ⟨GateOp.and, [p.1, p.2]⟩)
      ⟨GateOp.or, [n + 2 * L.length, n + 2 * L.length + 1]⟩ := by
  simp [W, gs, List.foldl_append]

lemma W_length (n : ℕ) (L : List (ℕ × ℕ)) (x : List Bool) :
    (W n L x).length = x.length + 2 * L.length + 1 := by
  induction L with
  | nil => simp [W_nil]
  | cons p L ih =>
    rw [W_cons]
    simp [step, ih]
    ring

lemma getD_app_left (w l : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ l).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma W_prefix (n : ℕ) (L : List (ℕ × ℕ)) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (W n L x).getD i false = x.getD i false := by
  induction L with
  | nil => rw [W_nil]; exact getD_app_left _ _ _ hi
  | cons p L ih =>
    rw [W_cons]
    have h1 : i < (W n L x).length := by rw [W_length]; omega
    have h2 : i < (step (W n L x) ⟨GateOp.and, [p.1, p.2]⟩).length := by
      simp [step]; omega
    unfold step at h2 ⊢
    rw [getD_app_left _ _ _ h2, getD_app_left _ _ _ h1, ih]

lemma W_out (n : ℕ) (L : List (ℕ × ℕ)) (x : List Bool) (hx : x.length = n)
    (hL : ∀ p ∈ L, p.1 < n ∧ p.2 < n) :
    (W n L x).getD (n + 2 * L.length) false =
      L.any (fun p => x.getD p.1 false && x.getD p.2 false) := by
  induction L with
  | nil =>
    rw [W_nil]
    simp [List.getD_eq_getElem?_getD, hx]
  | cons p L ih =>
    have hp := hL p (by simp)
    have ih' := ih (fun q hq => hL q (by simp [hq]))
    rw [W_cons]
    have hlen : (W n L x).length = n + 2 * L.length + 1 := by rw [W_length, hx]
    set w := W n L x with hw
    set a := GateOp.and.eval ([p.1, p.2].map fun i => w.getD i false) with ha
    have e1 : step w ⟨GateOp.and, [p.1, p.2]⟩ = w ++ [a] := rfl
    rw [e1]
    have hA : (w ++ [a]).getD (n + 2 * L.length) false = w.getD (n + 2 * L.length) false :=
      getD_app_left _ _ _ (by omega)
    have hB : (w ++ [a]).getD (n + 2 * L.length + 1) false = a := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, hlen]
    have hwa : (w ++ [a]).length = n + 2 * L.length + 2 := by simp [hlen]
    have hidx : n + 2 * (p :: L).length = (w ++ [a]).length := by
      rw [hwa]; simp; ring
    rw [hidx]
    unfold step
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    simp only [List.map_cons, List.map_nil]
    rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD, hA, hB, ih', ha]
    have hp1 : w.getD p.1 false = x.getD p.1 false := W_prefix n L x p.1 (by omega)
    have hp2 : w.getD p.2 false = x.getD p.2 false := W_prefix n L x p.2 (by omega)
    simp only [List.map_cons, List.map_nil, hp1, hp2, GateOp.eval, List.any_cons]
    simp [Bool.or_comm]

lemma mono_gs (n : ℕ) (L : List (ℕ × ℕ)) :
    ∀ g ∈ gs n L, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction L with
  | nil => intro g hg; simp [gs] at hg; subst hg; simp
  | cons p L ih =>
    intro g hg
    simp only [gs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | hg | hg
    · exact ih g hg
    · subst hg; simp
    · subst hg; simp

lemma ofFn_getD {n : ℕ} (y : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn y).getD i false = y ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma exists_circuit (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  classical
  let L : List (ℕ × ℕ) :=
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun uv => G.Adj uv.1 uv.2)).toList.map
      (fun uv => ((uv.1 : ℕ), (uv.2 : ℕ)))
  refine ⟨⟨gs n L, n + 2 * L.length⟩, mono_gs n L, ?_⟩
  funext y
  have hL : ∀ p ∈ L, p.1 < n ∧ p.2 < n := by
    intro p hp
    simp only [L, List.mem_map] at hp
    obtain ⟨uv, _, rfl⟩ := hp
    exact ⟨uv.1.isLt, uv.2.isLt⟩
  have key := W_out n L (List.ofFn y) (by simp) hL
  change (W n L (List.ofFn y)).getD (n + 2 * L.length) false = _
  rw [key]
  unfold PEqualNP.MetaComplexity.NestedCover.graphFun
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Finset.notMem_empty, false_and, exists_false, false_or]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    have hp' := hp
    simp only [L, List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp'
    obtain ⟨uv, hadj, rfl⟩ := hp'
    refine ⟨uv.1, uv.2, hadj, ?_, ?_⟩
    · rw [ofFn_getD y _ uv.1.isLt] at h1; simpa using h1
    · rw [ofFn_getD y _ uv.2.isLt] at h2; simpa using h2
  · rintro ⟨u, v, hadj, hu, hv⟩
    refine ⟨((u : ℕ), (v : ℕ)), ?_, ?_, ?_⟩
    · simp only [L, List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨(u, v), hadj, rfl⟩
    · rw [ofFn_getD y _ u.isLt]; simpa using hu
    · rw [ofFn_getD y _ v.isLt]; simpa using hv

end PEqualNP.Outside.L_meta_2666

theorem PEqualNP.Outside.L_meta_2666 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x4 ∧ PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ := by
  classical
  intro n G _
  obtain ⟨C₀, hmono₀, hfun₀⟩ := PEqualNP.Outside.L_meta_2666.exists_circuit n G
  let R := fun s : ℕ => ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size = s ∧
    PEqualNP.MetaComplexity.Monotone2 D ∧
    PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
  have hex : ∃ s, R s := ⟨C₀.size, C₀, rfl, hmono₀, hfun₀⟩
  obtain ⟨C, hcsize, hmono, hfun⟩ := Nat.find_spec hex
  refine ⟨C, ⟨hmono, ?_⟩, hfun⟩
  intro E hm he
  rw [hcsize]
  exact Nat.find_min' hex ⟨E, rfl, hm, he.trans hfun⟩
