import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3312

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_trans (n : ℕ) (C : Circuit) (a b : ℕ) :
    ∀ c, InCone n C a b → InCone n C b c → InCone n C a c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hab hbc
    rw [inCone_iff] at hbc
    obtain ⟨hc, k, hk, hin, hb⟩ := hbc
    rw [inCone_iff]
    refine ⟨hc, k, hk, hin, ?_⟩
    rcases hb with hb | hb
    · subst hb; exact Or.inr hab
    · exact Or.inr (ih k hk hab hb)

lemma split_range (p : ℕ → Bool) (j m : ℕ) (hj : j < m) (hp : p j = true) :
    ∃ T, (List.range m).filter p = (List.range j).filter p ++ j :: T := by
  have hm : m = j + ((m - j - 1) + 1) := by omega
  rw [hm, List.range_add, List.range_succ_eq_map, List.filter_append, List.map_cons,
    List.filter_cons_of_pos (by simpa using hp)]
  exact ⟨_, rfl⟩

lemma rank_lt (p : ℕ → Bool) (k j : ℕ) (hk : k < j) (hp : p k = true) :
    ((List.range k).filter p).length < ((List.range j).filter p).length := by
  obtain ⟨T, hT⟩ := split_range p k j hk hp
  rw [hT]; simp

end PEqualNP.Outside.L_meta_3312

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_3312 in
theorem PEqualNP.Outside.L_meta_3312 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size = PEqualNP.FactorSubst.liveSize n C ∧ ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n D D.output x = PEqualNP.CleanedNonEdge.wireVal n C C.output x := by
  intro n C hC
  obtain ⟨hAO, hRB, hFan⟩ := hC
  by_cases hout : n ≤ C.output ∧ C.output - n < C.gates.length
  swap
  · -- no gate is live
    refine ⟨⟨[], C.output⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro g hg; simp at hg
    · intro j hj; simp at hj
    · intro g hg; simp at hg
    · show ([] : List Gate).length = _
      unfold PEqualNP.FactorSubst.liveSize PEqualNP.FactorSubst.liveGates
      symm
      simp only [List.length_nil, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
        Finset.mem_range]
      intro j hj ⟨h1, h2⟩
      rcases h2 with h2 | h2
      · exact hout ⟨h1, by omega⟩
      · rw [inCone_iff] at h2
        exact hout ⟨h1, h2.1⟩
    · intro x
      show val ⟨[], C.output⟩ (List.ofFn x) C.output = val C (List.ofFn x) C.output
      by_cases h1 : n ≤ C.output
      · rw [val_ge (n := n) (by simp) (by simp; omega),
          val_ge (n := n) (by simp) (by have := fun h => hout ⟨h1, h⟩; omega)]
      · rw [val_input (n := n) (by simp) (by omega), val_input (n := n) (by simp) (by omega)]
  · obtain ⟨hno, hol⟩ := hout
    set o := C.output - n with ho
    set L := PEqualNP.FactorSubst.liveGates n C with hL
    have memL : ∀ j, j ∈ L ↔ j < C.gates.length ∧ (j = o ∨ InCone n C j o) := by
      intro j
      rw [hL]
      unfold PEqualNP.FactorSubst.liveGates
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, hno, h3⟩
    have closed : ∀ j k, j ∈ L → n + k ∈ (gateAt C j).inputs → k < j → k ∈ L := by
      intro j k hj hk hkj
      rw [memL] at hj ⊢
      obtain ⟨hjl, hj⟩ := hj
      have hcone : InCone n C k j := by
        rw [inCone_iff]; exact ⟨hjl, k, hkj, hk, Or.inl rfl⟩
      refine ⟨by omega, Or.inr ?_⟩
      rcases hj with hj | hj
      · rw [← hj]; exact hcone
      · exact inCone_trans n C k j o hcone hj
    let p : ℕ → Bool := fun j => decide (j ∈ L)
    let S : List ℕ := (List.range C.gates.length).filter p
    let r : ℕ → ℕ := fun j => ((List.range j).filter p).length
    let ren : ℕ → ℕ := fun w => if w < n then w else n + r (w - n)
    let f : ℕ → Gate := fun j => ⟨(gateAt C j).op, (gateAt C j).inputs.map ren⟩
    let D : Circuit := ⟨S.map f, n + r o⟩
    have hpL : ∀ j, p j = true ↔ j ∈ L := by intro j; simp [p]
    have memS : ∀ j, j ∈ S ↔ j ∈ L := by
      intro j
      simp only [S, List.mem_filter, List.mem_range, hpL]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨((memL j).1 h).1, h⟩
    have Sidx : ∀ j, j ∈ L → ∃ h : r j < S.length, S[r j] = j := by
      intro j hj
      obtain ⟨T, hT⟩ := split_range p j C.gates.length ((memL j).1 hj).1 ((hpL j).2 hj)
      have hlen : r j < S.length := by
        show r j < ((List.range C.gates.length).filter p).length
        rw [hT]; simp [r]
      refine ⟨hlen, ?_⟩
      have : S[r j]'hlen = ((List.range j).filter p ++ j :: T)[r j]'(by
          simp [r]) := by
        simp only [S, hT]
      rw [this, List.getElem_append_right (by simp [r])]
      simp [r]
    have hnd : S.Nodup := (List.nodup_range).filter _
    have rS : ∀ t (ht : t < S.length), r (S[t]) = t := by
      intro t ht
      have hmem : S[t] ∈ L := (memS _).1 (List.getElem_mem ht)
      obtain ⟨h1, h2⟩ := Sidx _ hmem
      exact ((List.Nodup.getElem_inj_iff hnd).1 h2)
    have hDlen : D.gates.length = S.length := by simp [D]
    have gD : ∀ j, j ∈ L → gateAt D (r j) = f j := by
      intro j hj
      obtain ⟨h1, h2⟩ := Sidx j hj
      rw [gateAt_eq (by rw [hDlen]; exact h1)]
      simp only [D, List.getElem_map, h2]
    -- the inputs of a live gate are renamed below its rank
    have renLt : ∀ j, j ∈ L → ∀ w ∈ (gateAt C j).inputs, ren w < n + r j := by
      intro j hj w hw
      have hwl : w < n + j := hRB j ((memL j).1 hj).1 w hw
      by_cases hwn : w < n
      · simp only [ren, if_pos hwn]; omega
      · simp only [ren, if_neg hwn]
        have hk : w - n < j := by omega
        have hkL : w - n ∈ L :=
          closed j (w - n) hj (by rw [show n + (w - n) = w by omega]; exact hw) hk
        have := rank_lt p (w - n) j hk ((hpL _).2 hkL)
        simp only [r]; omega
    have keyval : ∀ x : List Bool, x.length = n → ∀ j, j ∈ L →
        val D x (n + r j) = val C x (n + j) := by
      intro x hx j
      induction j using Nat.strong_induction_on with
      | _ j ih =>
        intro hj
        have hjl : j < C.gates.length := ((memL j).1 hj).1
        obtain ⟨h1, _⟩ := Sidx j hj
        rw [val_gate hx (by rw [hDlen]; exact h1), val_gate hx hjl, gD j hj]
        simp only [f, List.map_map]
        congr 1
        apply List.map_congr_left
        intro w hw
        have hwl : w < n + j := hRB j hjl w hw
        simp only [Function.comp, if_pos (renLt j hj w hw), if_pos hwl]
        by_cases hwn : w < n
        · simp only [ren, if_pos hwn]
          rw [val_input hx hwn, val_input hx hwn]
        · simp only [ren, if_neg hwn]
          have hk : w - n < j := by omega
          have hkL : w - n ∈ L :=
            closed j (w - n) hj (by rw [show n + (w - n) = w by omega]; exact hw) hk
          rw [ih (w - n) hk hkL, show n + (w - n) = w by omega]
    have hoL : o ∈ L := (memL o).2 ⟨hol, Or.inl rfl⟩
    refine ⟨D, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro g hg
      simp only [D, List.mem_map] at hg
      obtain ⟨j, hj, rfl⟩ := hg
      have hjL := (memS j).1 hj
      show (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or
      exact hAO _ (gateAt_mem ((memL j).1 hjL).1)
    · intro t ht w hw
      rw [hDlen] at ht
      have hmem : S[t] ∈ L := (memS _).1 (List.getElem_mem ht)
      have e := rS t ht
      rw [← e] at hw ⊢
      rw [gD _ hmem] at hw
      simp only [f, List.mem_map] at hw
      obtain ⟨w0, hw0, rfl⟩ := hw
      exact renLt _ hmem w0 hw0
    · intro g hg
      simp only [D, List.mem_map] at hg
      obtain ⟨j, hj, rfl⟩ := hg
      have hjL := (memS j).1 hj
      simp only [f, List.length_map]
      exact hFan _ (gateAt_mem ((memL j).1 hjL).1)
    · show D.gates.length = L.card
      rw [hDlen]
      have : S.toFinset = L := by
        ext j; simp only [List.mem_toFinset, memS]
      rw [← this, List.toFinset_card_of_nodup hnd]
    · intro x
      show val D (List.ofFn x) (n + r o) = val C (List.ofFn x) C.output
      rw [keyval (List.ofFn x) (by simp) o hoL, ho]
      congr 1
      omega
