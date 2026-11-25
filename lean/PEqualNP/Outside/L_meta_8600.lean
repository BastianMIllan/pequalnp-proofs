import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8600

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : t - l.length ≠ 0 := by omega
      simp [List.getElem?_cons, this]

theorem getD_ge {l : List Bool} {t : ℕ} (h : l.length ≤ t) : l.getD t false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  simp

def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩

theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (W gs x) (W gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (W gs x).length = (W gs y).length := by simp [W_length, hl]
    rw [W_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (W gs x).length
    · rw [if_pos h1] at ht ⊢; exact ih t ht
    · rw [if_neg h1] at ht ⊢
      by_cases h2 : t = (W gs x).length
      · rw [if_pos h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [if_neg h2] at ht; simp at ht

theorem foldl_prefix (q : List Gate) (w : List Bool) :
    ∃ s, q.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ s := by
  induction q generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g q ih =>
    obtain ⟨s, hs⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ s, ?_⟩
    simp only [List.foldl_cons]
    rw [hs]
    simp

theorem W_prefix (p q : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + p.length) :
    (W (p ++ q) x).getD i false = (W p x).getD i false := by
  obtain ⟨s, hs⟩ := foldl_prefix q (W p x)
  have h1 : W (p ++ q) x = W p x ++ s := by
    unfold W
    rw [List.foldl_append]
    exact hs
  have hl : i < (W p x).length := by rw [W_length]; exact hi
  rw [h1]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hl]

def newGate (c : ℕ → Bool) (n j : ℕ) (g : Gate) : Gate :=
  if c (n + j) = true then ⟨GateOp.or, []⟩
  else ⟨g.op, g.inputs.filter (fun i => !(decide (i < n + j) && c i))⟩

theorem claim (n : ℕ) (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x z : List Bool) (hx : x.length = n) (hz : z.length = n)
    (hz0 : ∀ i, z.getD i false = false)
    (c : ℕ → Bool) (hc : ∀ i, c i = (W gs z).getD i false) :
    ∀ p q, p ++ q = gs → ∀ i,
      (W (p.mapIdx (newGate c n)) x).getD i false = ((W p x).getD i false && !c i) := by
  have ha : ∀ k, c k = true → (W gs x).getD k false = true := by
    intro k hk
    apply W_mono gs hm z x (by rw [hx, hz]) (fun i hi => by rw [hz0 i] at hi; exact absurd hi (by simp))
    rw [← hc k]; exact hk
  intro p
  induction p using List.reverseRecOn with
  | nil =>
    intro q _ i
    show x.getD i false = (x.getD i false && !c i)
    cases hxi : x.getD i false
    · simp
    · have hi : i < n := by
        by_contra h
        rw [getD_ge (by omega)] at hxi
        exact absurd hxi (by simp)
      have hci : c i = false := by
        rw [hc i]
        have := W_prefix [] gs z i (by simp [hz, hi])
        simp only [List.nil_append] at this
        rw [this]
        exact hz0 i
      simp [hci]
  | append_singleton p g ih =>
    intro q hpq i
    have ih := ih ([g] ++ q) (by rw [← hpq]; simp)
    have hmap : (p ++ [g]).mapIdx (newGate c n) =
        p.mapIdx (newGate c n) ++ [newGate c n p.length g] := by
      simp [List.mapIdx_append]
    have hl1 : (W (p.mapIdx (newGate c n)) x).length = n + p.length := by
      rw [W_length, List.length_mapIdx, hx]
    have hl2 : (W p x).length = n + p.length := by rw [W_length, hx]
    rw [hmap, W_snoc, W_snoc, getD_snoc, getD_snoc, hl1, hl2]
    by_cases h1 : i < n + p.length
    · simp only [if_pos h1]; exact ih i
    · simp only [if_neg h1]
      by_cases h2 : i = n + p.length
      · simp only [if_pos h2]
        subst h2
        have hgm := hm g (by rw [← hpq]; simp)
        by_cases hct : c (n + p.length) = true
        · have hng : newGate c n p.length g = ⟨GateOp.or, []⟩ := by simp [newGate, hct]
          rw [hng]
          simp [hct, GateOp.eval]
        · have hcf : c (n + p.length) = false := by simpa using hct
          have hng : newGate c n p.length g =
              ⟨g.op, g.inputs.filter (fun i => !(decide (i < n + p.length) && c i))⟩ := by
            simp [newGate, hcf]
          rw [hng]
          dsimp only
          rw [hcf, Bool.not_false, Bool.and_true]
          have hcongr : (g.inputs.filter (fun i => !(decide (i < n + p.length) && c i))).map
              (fun k => (W (p.mapIdx (newGate c n)) x).getD k false) =
              (g.inputs.filter (fun i => !(decide (i < n + p.length) && c i))).map
              (fun k => (W p x).getD k false) := by
            apply List.map_congr_left
            intro k hk
            rw [ih k]
            rw [List.mem_filter] at hk
            cases hck : c k
            · simp
            · have hkk : ¬ k < n + p.length := by
                intro hlt
                simp [hlt, hck] at hk
              rw [getD_ge (by omega)]
              simp
          rw [hcongr]
          rcases hgm with hop | hop
          · rw [hop]
            simp only [GateOp.eval, List.all_map]
            rw [Bool.eq_iff_iff]
            simp only [List.all_eq_true, List.mem_filter, Function.comp_apply, id_eq]
            constructor
            · intro h k hk
              by_cases hP : (!(decide (k < n + p.length) && c k)) = true
              · exact h k ⟨hk, hP⟩
              · have hlt : k < n + p.length := by
                  by_contra hn; simp [hn] at hP
                have hck : c k = true := by
                  by_contra hn; simp [hn] at hP
                have := ha k hck
                rw [← hpq, List.append_assoc, W_prefix p ([g] ++ q) x k (by rw [hx]; exact hlt)] at this
                simpa using this
            · intro h k hk
              exact h k hk.1
          · have hfilt : g.inputs.filter (fun i => !(decide (i < n + p.length) && c i)) = g.inputs := by
              rw [List.filter_eq_self]
              intro k hk
              have hc0 := hc (n + p.length)
              rw [hcf] at hc0
              rw [← hpq,
                W_prefix (p ++ [g]) q z (n + p.length) (by simp [hz]), W_snoc, getD_snoc] at hc0
              rw [W_length, hz] at hc0
              simp only [lt_irrefl, if_false, if_true, hop, GateOp.eval] at hc0
              have hzk : (W p z).getD k false = false := by
                by_contra hn
                have hn' : (W p z).getD k false = true := by simpa using hn
                have : (g.inputs.map fun i => (W p z).getD i false).any id = true := by
                  simp only [List.any_map, List.any_eq_true, Function.comp]
                  exact ⟨k, hk, by simpa using hn'⟩
                rw [← hc0] at this
                exact absurd this (by simp)
              by_cases hlt : k < n + p.length
              · have hck : c k = false := by
                  rw [hc k, ← hpq, List.append_assoc,
                    W_prefix p ([g] ++ q) z k (by rw [hz]; exact hlt)]
                  exact hzk
                simp [hck]
              · simp [hlt]
            rw [hfilt]
      · simp only [if_neg h2]
        simp

end PEqualNP.Outside.L_meta_8600

theorem PEqualNP.Outside.L_meta_8600 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 : Fin x1 → Bool), x4.eval (List.ofFn x6) = Decidable.decide (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8 ∧ x6 x7 = Bool.true ∧ x6 x8 = Bool.true)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ (∀ (x8 : Fin x1 → Bool), x7.eval (List.ofFn x8) = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true)) ∧ x7.size ≤ x4.size ∧ ∀ (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate), x7.gates[x8]? = Option.some x9 → x9.op = PEqualNP.CircuitLowerBounds.GateOp.and → (x7.wires (List.ofFn fun (x12 : Fin x1) => Bool.false)).getD (x1 + x8) Bool.false = Bool.false := by
  intro n G _ C hmono hfun
  have hm : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have := (hmono g hg).1
    simpa using this
  set z : List Bool := List.ofFn fun (_ : Fin n) => false with hzdef
  have hzl : z.length = n := by simp [hzdef]
  have hz0 : ∀ i, z.getD i false = false := by
    intro i
    by_cases hi : i < n
    · simp [hzdef, List.getD_eq_getElem?_getD, hi]
    · exact PEqualNP.Outside.L_meta_8600.getD_ge (by rw [hzl]; omega)
  set c : ℕ → Bool := fun i => (PEqualNP.Outside.L_meta_8600.W C.gates z).getD i false with hcdef
  have hc : ∀ i, c i = (PEqualNP.Outside.L_meta_8600.W C.gates z).getD i false := fun i => rfl
  have hout : c C.output = false := by
    have := hfun (fun _ => false)
    have h2 : C.eval (List.ofFn fun (_ : Fin n) => false) = c C.output := rfl
    rw [h2] at this
    rw [this]
    simp
  refine ⟨⟨C.gates.mapIdx (PEqualNP.Outside.L_meta_8600.newGate c n), C.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [List.mem_mapIdx] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    unfold PEqualNP.Outside.L_meta_8600.newGate
    split_ifs
    · simp
    · refine ⟨(hmono _ (List.getElem_mem hj)).1, ?_⟩
      exact le_trans (List.length_filter_le _ _) (hmono _ (List.getElem_mem hj)).2
  · intro x8
    have key := PEqualNP.Outside.L_meta_8600.claim n C.gates hm (List.ofFn x8) z (by simp) hzl hz0 c hc
      C.gates [] (by simp) C.output
    show (PEqualNP.Outside.L_meta_8600.W _ _).getD C.output false = _
    rw [key, hout, Bool.not_false, Bool.and_true]
    exact hfun x8
  · show (C.gates.mapIdx _).length ≤ C.gates.length
    simp
  · intro j g' hj hop
    rw [List.getElem?_mapIdx] at hj
    cases hgj : C.gates[j]? with
    | none => rw [hgj] at hj; simp at hj
    | some g =>
      rw [hgj] at hj
      simp only [Option.map_some] at hj
      have hj2 := Option.some.inj hj
      have hcj : c (n + j) = false := by
        by_contra hn
        have hn2 : c (n + j) = true := by simpa using hn
        rw [← hj2] at hop
        unfold PEqualNP.Outside.L_meta_8600.newGate at hop
        rw [if_pos hn2] at hop
        simp at hop
      have key := PEqualNP.Outside.L_meta_8600.claim n C.gates hm z z hzl hzl hz0 c hc
        C.gates [] (by simp) (n + j)
      show (PEqualNP.Outside.L_meta_8600.W _ z).getD (n + j) false = false
      rw [key]
      have h3 : (PEqualNP.Outside.L_meta_8600.W C.gates z).getD (n + j) false = c (n + j) := rfl
      rw [h3, hcj]
      rfl
