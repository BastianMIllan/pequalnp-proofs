import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2861

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_len (gs : List Gate) (x : List Bool) :
    (gs.foldl stepW x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, stepW] <;> omega

theorem fold_pre (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl stepW x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp only [stepW, List.length_append, List.length_cons, List.length_nil]; omega)]
    simp only [stepW]
    exact List.getD_append _ _ _ _ hi

theorem fold_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ gs[j].inputs, i < x.length + j) :
    (gs.foldl stepW x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (gs.foldl stepW x).getD i false) := by
  have hF : ((gs.take j).foldl stepW x).length = x.length + j := by
    rw [fold_len, List.length_take]; omega
  have hfull : gs.foldl stepW x =
      (gs.drop (j + 1)).foldl stepW (stepW ((gs.take j).foldl stepW x) gs[j]) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
    rw [List.foldl_append, List.foldl_cons]
  have hread : ∀ i < x.length + j,
      (gs.foldl stepW x).getD i false = ((gs.take j).foldl stepW x).getD i false := by
    intro i hi
    rw [hfull, fold_pre _ _ _ (by simp only [stepW, List.length_append, List.length_cons, List.length_nil, hF]; omega)]
    simp only [stepW]
    exact List.getD_append _ _ _ _ (by omega)
  have hL : (gs.foldl stepW x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => ((gs.take j).foldl stepW x).getD i false) := by
    rw [hfull, fold_pre _ _ _ (by simp only [stepW, List.length_append, List.length_cons, List.length_nil, hF]; omega)]
    simp only [stepW]
    rw [List.getD_append_right _ _ _ _ (by omega), hF, Nat.sub_self, List.getD_cons_zero]
  rw [hL]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (hread i (hrb i hi)).symm

def VV (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem VV_low (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    VV n C x w = (List.ofFn x).getD w false := by
  unfold VV
  exact fold_pre C.gates (List.ofFn x) w (by simpa using hw)

theorem VV_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hrb : ReadsBack n C) (j : ℕ)
    (hj : j < C.gates.length) :
    VV n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (VV n C x)) := by
  have hg : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hl : (List.ofFn x).length = n := List.length_ofFn
  have key := fold_gate C.gates (List.ofFn x) j hj (by
    intro i hi; rw [hl]; exact hrb j hj i (by rw [hg]; exact hi))
  rw [hl] at key
  rw [hg]
  exact key

theorem LR (n : ℕ) (D : Circuit) (hrb : ReadsBack n D) (x : Fin n → Bool) (P : ℕ → Prop)
    (r : ℕ)
    (hP : ∀ w, P w → w ≠ r → ∃ j < D.gates.length, (gateAt D j).op = GateOp.or ∧
      w ∈ (gateAt D j).inputs ∧ P (n + j)) :
    ∀ m w, n + D.gates.length - w = m → P w → VV n D x w = true → VV n D x r = true := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro w hm hPw hv
    by_cases hwr : w = r
    · rw [← hwr]; exact hv
    obtain ⟨j, hj, hor, hin, hPj⟩ := hP w hPw hwr
    have hlt : w < n + j := hrb j hj w hin
    refine ih (n + D.gates.length - (n + j)) (by omega) (n + j) rfl hPj ?_
    rw [VV_gate n D x hrb j hj, hor]
    exact List.any_eq_true.mpr ⟨VV n D x w, List.mem_map.mpr ⟨w, hin, rfl⟩, hv⟩

theorem op2 (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (p q p' q' u : Bool)
    (hp : p' = true → p = true ∨ u = true) (hq : q' = true → q = true ∨ u = true) :
    op.eval [p', q'] = true → op.eval [p, q] = true ∨ u = true := by
  rcases hop with rfl | rfl <;> cases p <;> cases q <;> cases p' <;> cases q' <;> cases u <;>
    simp_all [GateOp.eval]


def C2 (C : Circuit) (n i j a b c : ℕ) : Circuit :=
  ⟨(C.gates.set i ⟨GateOp.and, [a, c]⟩).set j ⟨GateOp.and, [n + i, b]⟩, C.output⟩

theorem C2_len (C : Circuit) (n i j a b c : ℕ) :
    (C2 C n i j a b c).gates.length = C.gates.length := by
  simp [C2]

theorem C2_gate (C : Circuit) (n i j a b c m : ℕ) (hm : m < C.gates.length) :
    gateAt (C2 C n i j a b c) m = if m = j then ⟨GateOp.and, [n + i, b]⟩
      else if m = i then ⟨GateOp.and, [a, c]⟩ else gateAt C m := by
  unfold gateAt C2
  rw [List.getD_eq_getElem _ _ (by simpa using hm), List.getD_eq_getElem _ _ hm]
  simp only [List.getElem_set]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem VV_big (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    VV n C x w = false := by
  unfold VV
  apply List.getD_eq_default
  rw [show C.wires (List.ofFn x) = C.gates.foldl stepW (List.ofFn x) from rfl, fold_len]
  simp only [List.length_ofFn]
  omega

theorem main (n : ℕ) (C : Circuit) (i j a b c : ℕ) (hrb : ReadsBack n C)
    (hj : j < C.gates.length) (hij : i < j)
    (hiop : (gateAt C i).op = GateOp.and) (hiin : (gateAt C i).inputs = [a, b])
    (hjop : (gateAt C j).op = GateOp.and) (hjin : (gateAt C j).inputs = [n + i, c])
    (hc : c < n + i) (hnot : ∀ k < C.gates.length, k ≠ j → n + i ∉ (gateAt C k).inputs)
    (hout : C.output ≠ n + i) :
    ReadsBack n (C2 C n i j a b c) ∧ (C2 C n i j a b c).size = C.size ∧
      ∀ x : Fin n → Bool, (C2 C n i j a b c).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hi : i < C.gates.length := by omega
  have ha : a < n + i := hrb i hi a (by rw [hiin]; simp)
  have hb : b < n + i := hrb i hi b (by rw [hiin]; simp)
  have hlen := C2_len C n i j a b c
  have hrb' : ReadsBack n (C2 C n i j a b c) := by
    intro m hm w hw
    rw [hlen] at hm
    rw [C2_gate C n i j a b c m hm] at hw
    split_ifs at hw with h1 h2
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
      omega
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
      omega
    · exact hrb m hm w hw
  refine ⟨hrb', by unfold Circuit.size; rw [hlen], ?_⟩
  intro x
  have key : ∀ w, w ≠ n + i → VV n (C2 C n i j a b c) x w = VV n C x w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
    intro hwi
    by_cases hwn : w < n
    · rw [VV_low _ _ x w hwn, VV_low _ _ x w hwn]
    by_cases hwl : w < n + C.gates.length
    · obtain ⟨m, rfl⟩ : ∃ m, w = n + m := ⟨w - n, by omega⟩
      have hm : m < C.gates.length := by omega
      have hmi : m ≠ i := fun h => hwi (by rw [h])
      rw [VV_gate n _ x hrb' m (by rw [hlen]; exact hm), VV_gate n C x hrb m hm,
        C2_gate C n i j a b c m hm]
      by_cases hmj : m = j
      · rw [if_pos hmj]
        rw [hmj, hjop, hjin]
        have hi' : VV n (C2 C n i j a b c) x (n + i) = (VV n C x a && VV n C x c) := by
          rw [VV_gate n _ x hrb' i (by rw [hlen]; exact hi), C2_gate C n i j a b c i hi,
            if_neg (by omega), if_pos rfl]
          simp only [List.map_cons, List.map_nil]
          rw [ih a (by omega) (by omega), ih c (by omega) (by omega)]
          simp [GateOp.eval]
        have hiC : VV n C x (n + i) = (VV n C x a && VV n C x b) := by
          rw [VV_gate n C x hrb i hi, hiop, hiin]
          simp [GateOp.eval]
        simp only [List.map_cons, List.map_nil]
        rw [hi', hiC, ih b (by omega) (by omega)]
        generalize VV n C x a = A
        generalize VV n C x b = B
        generalize VV n C x c = Cc
        cases A <;> cases B <;> cases Cc <;> simp [GateOp.eval]
      · rw [if_neg hmj, if_neg hmi]
        congr 1
        apply List.map_congr_left
        intro v hv
        exact ih v (hrb m hm v hv) (fun h => hnot m hm hmj (h ▸ hv))
    · rw [VV_big n _ x w (by rw [hlen]; omega), VV_big n C x w (by omega)]
  exact key C.output hout

end PEqualNP.Outside.L_meta_2861

theorem PEqualNP.Outside.L_meta_2861 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (i j a b c : ℕ), PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → j < C.gates.length → i < j → (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [n + i, c] → c < n + i → (∀ k < C.gates.length, k ≠ j → n + i ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → C.output ≠ n + i → PEqualNP.MetaComplexity.NestedCover.ReadsBack n (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ ∀ x : Fin n → Bool, (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro n C i j a b c hrb hj hij hiop hiin hjop hjin hc hnot hout
  exact PEqualNP.Outside.L_meta_2861.main n C i j a b c hrb hj hij hiop hiin hjop hjin hc hnot hout
