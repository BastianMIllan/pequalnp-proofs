import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8411

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    (Circuit.wires ⟨gs, o⟩ x) = gs.foldl stepF x := rfl

theorem foldl_prefix (gs : List Gate) : ∀ init : List Bool,
    ∃ t, gs.foldl stepF init = init ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro init; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro init
    obtain ⟨t, ht, hl⟩ := ih (stepF init g)
    refine ⟨[g.op.eval (g.inputs.map fun i => init.getD i false)] ++ t, ?_, ?_⟩
    · rw [List.foldl_cons, ht, stepF, List.append_assoc]
    · simp [hl]

theorem foldl_len (gs : List Gate) (init : List Bool) :
    (gs.foldl stepF init).length = init.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := foldl_prefix gs init
  rw [ht, List.length_append, hl]

theorem foldl_snoc (gs : List Gate) (g : Gate) (init : List Bool) :
    (gs ++ [g]).foldl stepF init = stepF (gs.foldl stepF init) g := by
  rw [List.foldl_append]; rfl

-- good gate lists
def Good (n : ℕ) (gs : List Gate) : Prop :=
  Monotone2 ⟨gs, 0⟩ ∧ ReadsBack n ⟨gs, 0⟩

theorem good_snoc (n : ℕ) (gs : List Gate) (g : Gate) (hgs : Good n gs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < n + gs.length) : Good n (gs ++ [g]) := by
  obtain ⟨hm, hr⟩ := hgs
  constructor
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with h | h
    · exact hm g' h
    · subst h
      refine ⟨?_, hlen⟩
      rcases hop with h | h <;> simp [h]
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    unfold gateAt at hi
    by_cases hjl : j < gs.length
    · rw [List.getD_append _ _ _ _ hjl] at hi
      exact hr j hjl i hi
    · have hje : j = gs.length := by omega
      subst hje
      rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
      simp only [Nat.sub_self, List.getD_cons_zero] at hi
      exact hin i hi

-- value of a wire of a gate list
def val (gs : List Gate) (x : List Bool) (w : ℕ) : Bool := (gs.foldl stepF x).getD w false

theorem val_snoc_old (gs : List Gate) (g : Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs.length) : val (gs ++ [g]) x w = val gs x w := by
  unfold val
  rw [foldl_snoc]
  rw [stepF]
  rw [List.getD_append _ _ _ _ (by rw [foldl_len]; exact hw)]

theorem val_snoc_new (gs : List Gate) (g : Gate) (x : List Bool) :
    val (gs ++ [g]) x (x.length + gs.length) =
      g.op.eval (g.inputs.map fun i => val gs x i) := by
  unfold val
  rw [foldl_snoc]
  rw [stepF]
  rw [List.getD_append_right _ _ _ _ (by rw [foldl_len])]
  rw [foldl_len, Nat.sub_self]
  rfl

theorem val_input (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (b : Fin n) :
    val gs (List.ofFn x) b.val = x b := by
  unfold val
  obtain ⟨t, ht, _⟩ := foldl_prefix gs (List.ofFn x)
  rw [ht, List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

-- the OR chain
theorem chain (n : ℕ) (_x0 : Unit) : ∀ (l : List (Fin n)) (gs : List Gate) (w : ℕ)
    (F : (Fin n → Bool) → Bool), Good n gs → w < n + gs.length →
    (∀ x : Fin n → Bool, val gs (List.ofFn x) w = F x) →
    ∃ ex : List Gate, ∃ w' : ℕ, Good n (gs ++ ex) ∧ ex.length = l.length ∧
      w' < n + (gs ++ ex).length ∧
      (∀ x : Fin n → Bool, val (gs ++ ex) (List.ofFn x) w' = (F x || l.any x)) ∧
      (∀ v < n + gs.length, ∀ x : Fin n → Bool,
        val (gs ++ ex) (List.ofFn x) v = val gs (List.ofFn x) v) := by
  intro l
  induction l with
  | nil =>
    intro gs w F hg hw hF
    refine ⟨[], w, by simpa using hg, rfl, by simpa using hw, ?_, ?_⟩
    · intro x; simp [hF x]
    · intro v _ x; simp
  | cons b l ih =>
    intro gs w F hg hw hF
    let g : Gate := ⟨GateOp.or, [w, b.val]⟩
    have hg1 : Good n (gs ++ [g]) := by
      apply good_snoc n gs g hg (Or.inr rfl) (by simp [g])
      intro i hi
      simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h | h <;> omega
    have hlen1 : (gs ++ [g]).length = gs.length + 1 := by simp
    have hF1 : ∀ x : Fin n → Bool, val (gs ++ [g]) (List.ofFn x) (n + gs.length) =
        (F x || x b) := by
      intro x
      have := val_snoc_new gs g (List.ofFn x)
      rw [List.length_ofFn] at this
      rw [this]
      simp [g, GateOp.eval, hF x, val_input]
    obtain ⟨ex, w', hgood, hexl, hw', hval, hpres⟩ :=
      ih (gs ++ [g]) (n + gs.length) (fun x => F x || x b) hg1 (by omega) hF1
    refine ⟨g :: ex, w', by simpa using hgood, by simp [hexl], by simpa using hw', ?_, ?_⟩
    · intro x
      have := hval x
      simp only [List.append_assoc, List.singleton_append] at this
      rw [this]
      simp [Bool.or_assoc]
    · intro v hv x
      have := hpres v (by omega) x
      simp only [List.append_assoc, List.singleton_append] at this
      rw [this]
      have h2 := val_snoc_old gs g (List.ofFn x) v (by rw [List.length_ofFn]; exact hv)
      exact h2

-- one item
theorem item (n : ℕ) (a : Fin n) (l : List (Fin n)) (gs : List Gate) (u : ℕ)
    (F : (Fin n → Bool) → Bool) (hg : Good n gs) (hu : u < n + gs.length)
    (hF : ∀ x : Fin n → Bool, val gs (List.ofFn x) u = F x) :
    ∃ ex : List Gate, ∃ u' : ℕ, Good n (gs ++ ex) ∧ ex.length ≤ l.length + 1 ∧
      u' < n + (gs ++ ex).length ∧
      (∀ x : Fin n → Bool, val (gs ++ ex) (List.ofFn x) u' = (F x || (x a && l.any x))) := by
  cases l with
  | nil =>
    refine ⟨[], u, by simpa using hg, by simp, by simpa using hu, ?_⟩
    intro x; simp [hF x]
  | cons b l =>
    obtain ⟨ex, w, hgood, hexl, hw, hval, hpres⟩ :=
      chain n () l gs b.val (fun x => x b) hg (by omega) (fun x => val_input n gs x b)
    let gs1 := gs ++ ex
    let gA : Gate := ⟨GateOp.and, [a.val, w]⟩
    have hgA : Good n (gs1 ++ [gA]) := by
      apply good_snoc n gs1 gA hgood (Or.inl rfl) (by simp [gA])
      intro i hi
      simp only [gA, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h | h
      · have := a.isLt; omega
      · exact h ▸ hw
    let gO : Gate := ⟨GateOp.or, [u, n + gs1.length]⟩
    have hgO : Good n (gs1 ++ [gA] ++ [gO]) := by
      apply good_snoc n (gs1 ++ [gA]) gO hgA (Or.inr rfl) (by simp [gO])
      intro i hi
      simp only [gO, List.mem_cons, List.not_mem_nil, or_false] at hi
      have : gs.length ≤ gs1.length := by simp [gs1]
      rcases hi with h | h
      · simp only [List.length_append, List.length_singleton]; omega
      · simp only [List.length_append, List.length_singleton]; omega
    refine ⟨ex ++ [gA, gO], n + (gs1 ++ [gA]).length, ?_, ?_, ?_, ?_⟩
    · have : gs ++ (ex ++ [gA, gO]) = gs1 ++ [gA] ++ [gO] := by simp [gs1]
      rw [this]; exact hgO
    · simp [hexl]
    · simp [gs1]
    · intro x
      have e : gs ++ (ex ++ [gA, gO]) = gs1 ++ [gA] ++ [gO] := by simp [gs1]
      rw [e]
      have h1 := val_snoc_new (gs1 ++ [gA]) gO (List.ofFn x)
      rw [List.length_ofFn] at h1
      rw [h1]
      have hA := val_snoc_new gs1 gA (List.ofFn x)
      rw [List.length_ofFn] at hA
      have hU : val (gs1 ++ [gA]) (List.ofFn x) u = F x := by
        rw [val_snoc_old gs1 gA (List.ofFn x) u (by
          rw [List.length_ofFn]; simp only [gs1, List.length_append]; omega)]
        rw [hpres u hu x, hF x]
      have hW : val gs1 (List.ofFn x) w = (x b || l.any x) := hval x
      have hAv : val gs1 (List.ofFn x) a.val = x a := val_input n gs1 x a
      simp only [gO, gA, GateOp.eval, List.map_cons, List.map_nil] at hA ⊢
      rw [hU, hA]
      simp [hW, hAv]

theorem items (n : ℕ) : ∀ (L : List (Fin n × List (Fin n))) (gs : List Gate) (u : ℕ)
    (F : (Fin n → Bool) → Bool), Good n gs → u < n + gs.length →
    (∀ x : Fin n → Bool, val gs (List.ofFn x) u = F x) →
    ∃ ex : List Gate, ∃ u' : ℕ, Good n (gs ++ ex) ∧
      ex.length ≤ (L.map fun p : Fin n × List (Fin n) => p.2.length + 1).sum ∧
      (∀ x : Fin n → Bool, val (gs ++ ex) (List.ofFn x) u' =
        (F x || L.any fun p => x p.1 && p.2.any x)) := by
  intro L
  induction L with
  | nil =>
    intro gs u F hg _ hF
    exact ⟨[], u, by simpa using hg, by simp, fun x => by simp [hF x]⟩
  | cons p L ih =>
    intro gs u F hg hu hF
    obtain ⟨ex1, u1, hg1, hl1, hu1, hv1⟩ := item n p.1 p.2 gs u F hg hu hF
    obtain ⟨ex2, u2, hg2, hl2, hv2⟩ := ih (gs ++ ex1) u1 _ hg1 hu1 hv1
    refine ⟨ex1 ++ ex2, u2, by simpa using hg2, ?_, ?_⟩
    · simp only [List.length_append, List.map_cons, List.sum_cons]; omega
    · intro x
      have := hv2 x
      simp only [List.append_assoc] at this
      rw [this]
      simp [Bool.or_assoc]

end PEqualNP.Outside.L_meta_8411

theorem PEqualNP.Outside.L_meta_8411 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List (Fin x1 × List (Fin x1))), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x2.output < x1 + x2.size → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 ∧ x7.size ≤ x2.size + (List.map (fun (x8 : Fin x1 × List (Fin x1)) => x8.2.length + (1 : ℕ)) x3).sum ∧ ∀ (x8 : Fin x1 → Bool), x7.eval (List.ofFn x8) = (x2.eval (List.ofFn x8) || x3.any fun (x9 : Fin x1 × List (Fin x1)) => x8 x9.1 && x9.2.any x8) := by
  intro n C L hm hr ho
  obtain ⟨gs, o⟩ := C
  obtain ⟨ex, u', hg, hl, hv⟩ := PEqualNP.Outside.L_meta_8411.items n L gs o
    (fun x => PEqualNP.Outside.L_meta_8411.val gs (List.ofFn x) o) ⟨hm, hr⟩ ho (fun x => rfl)
  refine ⟨⟨gs ++ ex, u'⟩, hg.1, hg.2, ?_, ?_⟩
  · show (gs ++ ex).length ≤ gs.length + _
    simp only [List.length_append]; omega
  · intro x
    exact hv x
