import Mathlib
import PEqualNP.Defs

-- A circuit with at most one gate reads at most two wires at its gate, so some edge of the graph
-- avoids them: setting that edge true and everything else false gives the same output as the
-- all-false input, while the edge function differs on the two.
namespace PEqualNP.Outside.L_meta_7883
open PEqualNP.CircuitLowerBounds

def F (x5 : Fin 9 → Bool) : Bool :=
  (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))

def ind (u v : ℕ) : Fin 9 → Bool := fun k => decide (k.val = u ∨ k.val = v)

theorem wires_nil (o : ℕ) (w : List Bool) : (Circuit.mk [] o).wires w = w := rfl

theorem wires_one (g : Gate) (o : ℕ) (w : List Bool) :
    (Circuit.mk [g] o).wires w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem getD_ofFn (x : Fin 9 → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < 9 then x ⟨i, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem F_ind_self : ∀ o : Fin 9, F (ind o.val o.val) = false := by decide

theorem F_true : F (fun _ => true) = true := by decide

theorem F_false : F (fun _ => false) = false := by decide

theorem F01 : F (ind 0 1) = true := by decide
theorem F23 : F (ind 2 3) = true := by decide
theorem F57 : F (ind 5 7) = true := by decide

theorem avoid (l : List ℕ) (hl : l.length ≤ 2) :
    ∃ u v : ℕ, F (ind u v) = true ∧ ∀ i ∈ l, i ≠ u ∧ i ≠ v := by
  match l, hl with
  | [], _ => exact ⟨0, 1, F01, by simp⟩
  | [a], _ =>
    by_cases h : a ≠ 0 ∧ a ≠ 1
    · exact ⟨0, 1, F01, by simpa using h⟩
    · exact ⟨2, 3, F23, by simp; omega⟩
  | [a, b], _ =>
    by_cases h1 : a ≠ 0 ∧ a ≠ 1 ∧ b ≠ 0 ∧ b ≠ 1
    · exact ⟨0, 1, F01, by simp; omega⟩
    · by_cases h2 : a ≠ 2 ∧ a ≠ 3 ∧ b ≠ 2 ∧ b ≠ 3
      · exact ⟨2, 3, F23, by simp; omega⟩
      · exact ⟨5, 7, F57, by simp; omega⟩
  | _ :: _ :: _ :: _, h => simp at h

end PEqualNP.Outside.L_meta_7883

theorem PEqualNP.Outside.L_meta_7883 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (15 : ℕ) → x1.gates[(1 : ℕ)]? = Option.none → ∃ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5) ≠ (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) := by
  intro C hfan _ hnone
  by_contra hall
  push_neg at hall
  have hF : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_7883.F x :=
    fun x => hall x
  obtain ⟨gs, o⟩ := C
  have hlen : gs.length ≤ 1 := by
    have h : gs[1]? = none := hnone
    rw [List.getElem?_eq_none_iff] at h; omega
  match gs, hlen with
  | [], _ =>
    have hE : ∀ x : Fin 9 → Bool, (List.ofFn x).getD o false =
        PEqualNP.Outside.L_meta_7883.F x := by
      intro x
      have h := hF x
      rwa [PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.Outside.L_meta_7883.wires_nil] at h
    by_cases ho : o < 9
    · have h := hE (PEqualNP.Outside.L_meta_7883.ind o o)
      rw [PEqualNP.Outside.L_meta_7883.getD_ofFn, dif_pos ho,
        PEqualNP.Outside.L_meta_7883.F_ind_self ⟨o, ho⟩] at h
      simp [PEqualNP.Outside.L_meta_7883.ind] at h
    · have h := hE (fun _ => true)
      rw [PEqualNP.Outside.L_meta_7883.getD_ofFn, dif_neg ho,
        PEqualNP.Outside.L_meta_7883.F_true] at h
      exact Bool.noConfusion h
  | [g], _ =>
    have hE : ∀ x : Fin 9 → Bool, (List.ofFn x ++
        [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)]).getD o false =
        PEqualNP.Outside.L_meta_7883.F x := by
      intro x
      have h := hF x
      rwa [PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.Outside.L_meta_7883.wires_one] at h
    by_cases ho : o < 9
    · have h := hE (PEqualNP.Outside.L_meta_7883.ind o o)
      rw [List.getD_append _ _ _ _ (by simpa using ho), PEqualNP.Outside.L_meta_7883.getD_ofFn,
        dif_pos ho, PEqualNP.Outside.L_meta_7883.F_ind_self ⟨o, ho⟩] at h
      simp [PEqualNP.Outside.L_meta_7883.ind] at h
    · by_cases h9 : o = 9
      · subst h9
        have hg := (hfan g (by simp)).2
        obtain ⟨u, v, hFuv, hav⟩ := PEqualNP.Outside.L_meta_7883.avoid g.inputs hg
        have h1 := hE (PEqualNP.Outside.L_meta_7883.ind u v)
        have h0 := hE (fun _ => false)
        rw [List.getD_append_right _ _ _ _ (by simp)] at h1 h0
        simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero] at h1 h0
        have hmap : (g.inputs.map fun i =>
            (List.ofFn (PEqualNP.Outside.L_meta_7883.ind u v)).getD i false) =
            (g.inputs.map fun i => (List.ofFn (fun _ : Fin 9 => false)).getD i false) := by
          apply List.map_congr_left
          intro i hi
          obtain ⟨hu, hv⟩ := hav i hi
          rw [PEqualNP.Outside.L_meta_7883.getD_ofFn, PEqualNP.Outside.L_meta_7883.getD_ofFn]
          split_ifs
          · simp [PEqualNP.Outside.L_meta_7883.ind, hu, hv]
          · rfl
        rw [hmap, h0, PEqualNP.Outside.L_meta_7883.F_false, hFuv] at h1
        exact Bool.noConfusion h1
      · have h := hE (fun _ => true)
        rw [List.getD_eq_default _ _ (by simp; omega),
          PEqualNP.Outside.L_meta_7883.F_true] at h
        exact Bool.noConfusion h
