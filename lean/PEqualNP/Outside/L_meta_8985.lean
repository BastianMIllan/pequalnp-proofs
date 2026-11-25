import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8985

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)




def remap (N L : ℕ) (P : List Gate) (w : Fin L → ℕ) (m : ℕ) (i : ℕ) : ℕ :=
  if h : i < L then (if w ⟨i, h⟩ < N + P.length then w ⟨i, h⟩ else N + P.length + m)
  else if i < L + m then N + P.length + (i - L) else N + P.length + m

theorem remap_lt (N L : ℕ) (P : List Gate) (w : Fin L → ℕ) (m i : ℕ) (h : i < L) :
    remap N L P w m i = if w ⟨i, h⟩ < N + P.length then w ⟨i, h⟩ else N + P.length + m := by
  unfold remap
  rw [dif_pos h]

theorem remap_mid (N L : ℕ) (P : List Gate) (w : Fin L → ℕ) (m i : ℕ) (h : ¬ i < L) (h2 : i < L + m) :
    remap N L P w m i = N + P.length + (i - L) := by
  unfold remap
  rw [dif_neg h, if_pos h2]

theorem remap_hi (N L : ℕ) (P : List Gate) (w : Fin L → ℕ) (m i : ℕ) (h : ¬ i < L) (h2 : ¬ i < L + m) :
    remap N L P w m i = N + P.length + m := by
  unfold remap
  rw [dif_neg h, if_neg h2]

def mapG (f : ℕ → ℕ) (gt : Gate) : Gate := ⟨gt.op, gt.inputs.map f⟩

theorem compose (N L : ℕ) (D : Set (List Bool)) (P : List Gate) (w : Fin L → ℕ)
    (g : Fin L → List Bool → Bool) (C : Circuit)
    (hD : ∀ x ∈ D, x.length = N) (hP : PEqualNP.MetaComplexity.Monotone2 (⟨P, 0⟩ : Circuit))
    (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (hw : ∀ x ∈ D, ∀ j, ((⟨P, 0⟩ : Circuit).wires x).getD (w j) false = g j x) :
    ∃ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size ≤ P.length + C.size ∧
      ∀ x ∈ D, C'.eval x = C.eval (List.ofFn fun j => g j x) := by
  classical
  set m := C.gates.length with hm
  set r : ℕ → ℕ := remap N L P w m with hr
  set Q : List Gate := C.gates.map (mapG r) with hQ
  have hQl : Q.length = m := by rw [hQ, List.length_map]
  refine ⟨⟨P ++ Q, r C.output⟩, ?_, ?_, ?_⟩
  · intro gt hgt
    rcases List.mem_append.1 hgt with h | h
    · exact hP gt h
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      obtain ⟨h1, h2⟩ := hC g0 hg0
      exact ⟨h1, by simpa [mapG] using h2⟩
  · show (P ++ Q).length ≤ P.length + C.gates.length
    rw [List.length_append, hQl]
  · intro x hxD
    have hx : x.length = N := hD x hxD
    set y : List Bool := List.ofFn fun j => g j x with hy
    have hyl : y.length = L := by rw [hy, List.length_ofFn]
    set V' := run (P ++ Q) x with hV'
    set V := run C.gates y with hV
    have hV'l : V'.length = N + P.length + m := by
      rw [hV', run_length, List.length_append, hQl, hx]
      omega
    have hVl : V.length = L + m := by rw [hV, run_length, hyl]
    have hPw : ∀ j, (run P x).getD (w j) false = g j x := fun j => hw x hxD j
    have hPl : (run P x).length = N + P.length := by rw [run_length, hx]
    have hin : ∀ i (hi : i < L), V'.getD (r i) false = g ⟨i, hi⟩ x := by
      intro i hi
      rw [hr, remap_lt N L P w m i hi]
      split_ifs with hlt
      · rw [hV', run_prefix P Q x _ (by rw [hx]; exact hlt)]
        exact hPw _
      · rw [List.getD_eq_default _ _ (by rw [hV'l])]
        rw [← hPw ⟨i, hi⟩, List.getD_eq_default _ _ (by rw [hPl]; omega)]
    have hyi : ∀ i (hi : i < L), V.getD i false = g ⟨i, hi⟩ x := by
      intro i hi
      rw [hV, run_input _ _ _ (by rw [hyl]; exact hi), hy]
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
    have hmain : ∀ k, k < m → V'.getD (N + P.length + k) false = V.getD (L + k) false := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk
        have hk1 : P.length + k < (P ++ Q).length := by rw [List.length_append, hQl]; omega
        have hk2 : k < C.gates.length := by omega
        have e1 := run_gate (P ++ Q) x (P.length + k) hk1
        have e2 := run_gate C.gates y k hk2
        rw [← hV'] at e1
        rw [← hV] at e2
        rw [hx, ← Nat.add_assoc] at e1
        rw [hyl] at e2
        rw [e1, e2]
        have hq : (P ++ Q)[P.length + k] = mapG r (C.gates[k]) := by
          rw [List.getElem_append_right (by omega)]
          simp [hQ]
        rw [hq]
        simp only [mapG, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp]
        by_cases hi : i < L
        · have hrv : (if r i < N + P.length + k then V'.getD (r i) false else false) = V'.getD (r i) false := by
            split_ifs with hc
            · rfl
            · have hri : r i = _ := remap_lt N L P w m i hi
              have : r i = N + P.length + m := by
                split_ifs at hri with h2
                · omega
                · exact hri
              rw [this, List.getD_eq_default _ _ (by rw [hV'l])]
          rw [hrv, if_pos (by omega), hin i hi, hyi i hi]
        · by_cases hi2 : i < L + k
          · have : r i = N + P.length + (i - L) := by
              rw [hr, remap_mid N L P w m i hi (by omega)]
            rw [this, if_pos (by omega), if_pos hi2, ih (i - L) (by omega) (by omega)]
            congr 1
            omega
          · rw [if_neg hi2, if_neg]
            by_cases hi3 : i < L + m
            · rw [hr, remap_mid N L P w m i hi hi3]
              omega
            · rw [hr, remap_hi N L P w m i hi hi3]
              omega
    show V'.getD (r C.output) false = V.getD C.output false
    by_cases ho : C.output < L
    · rw [hin _ ho, hyi _ ho]
    · by_cases ho2 : C.output < L + m
      · have : r C.output = N + P.length + (C.output - L) := by
          rw [hr, remap_mid N L P w m _ ho ho2]
        rw [this, hmain _ (by omega)]
        congr 1
        omega
      · have : r C.output = N + P.length + m := by
          rw [hr, remap_hi N L P w m _ ho ho2]
        rw [this, List.getD_eq_default _ _ (by rw [hV'l]),
          List.getD_eq_default _ _ (by rw [hVl]; omega)]

end PEqualNP.Outside.L_meta_8985

theorem PEqualNP.Outside.L_meta_8985 : ∀ (N L : ℕ) (D : Set (List Bool)) (P : List PEqualNP.CircuitLowerBounds.Gate) (w : Fin L → ℕ) (g : Fin L → List Bool → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ x ∈ D, x.length = N) → PEqualNP.MetaComplexity.Monotone2 (⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x ∈ D, ∀ j, ((⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).getD (w j) false = g j x) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size ≤ P.length + C.size ∧ ∀ x ∈ D, C'.eval x = C.eval (List.ofFn fun j => g j x) := by
  exact PEqualNP.Outside.L_meta_8985.compose
