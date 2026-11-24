import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2642

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves

theorem getD_app_lt {α : Type} (l l' : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_len {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem stepW_len (w : List Bool) (g : Gate) : (stepW w g).length = w.length + 1 := by
  simp [stepW]

theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, stepW_len]
    simp
    omega

theorem foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by rw [stepW_len]; omega
    rw [ih (stepW w g) hlt]
    simp only [stepW]
    exact getD_app_lt _ _ _ _ hi

def ren (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

-- where index i may sit, relative to the two current lengths, so that one more gate keeps it
def Good (f : ℕ → ℕ) (l l' i : ℕ) : Prop :=
  (i < l ∧ f i ≠ l') ∨ (i = l ∧ f i = l') ∨ (l < i ∧ l' < f i)

theorem sim (f : ℕ → ℕ) (ok : ℕ → Prop) (B : List Gate) :
    ∀ U U' : List Bool,
    (∀ g ∈ B, ∀ i ∈ g.inputs, ok i) →
    (∀ k < B.length, ∀ i, ok i → Good f (U.length + k) (U'.length + k) i) →
    (∀ i, ok i → U.getD i false = U'.getD (f i) false) →
    ∀ i, ok i → (B.foldl stepW U).getD i false =
      ((B.map (ren f)).foldl stepW U').getD (f i) false := by
  induction B with
  | nil =>
    intro U U' _ _ hinv i hi
    simpa using hinv i hi
  | cons g B ih =>
    intro U U' hok hgood hinv
    simp only [List.map_cons, List.foldl_cons]
    have hokg : ∀ i ∈ g.inputs, ok i := hok g (List.mem_cons_self ..)
    have hok' : ∀ g' ∈ B, ∀ i ∈ g'.inputs, ok i :=
      fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')
    apply ih (stepW U g) (stepW U' (ren f g)) hok'
    · intro k hk i hi
      have := hgood (k + 1) (by simp; omega) i hi
      rw [stepW_len, stepW_len]
      have e1 : U.length + 1 + k = U.length + (k + 1) := by omega
      have e2 : U'.length + 1 + k = U'.length + (k + 1) := by omega
      rw [e1, e2]
      exact this
    · intro i hi
      have hG := hgood 0 (by simp) i hi
      simp only [Nat.add_zero] at hG
      have hgate : g.op.eval (g.inputs.map fun j => U.getD j false) =
          (ren f g).op.eval ((ren f g).inputs.map fun j => U'.getD j false) := by
        simp only [ren, List.map_map]
        congr 1
        apply List.map_congr_left
        intro j hj
        exact hinv j (hokg j hj)
      rcases hG with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases lt_or_gt_of_ne h2 with h3 | h3
        · simp only [stepW]
          rw [getD_app_lt _ _ _ _ h1, getD_app_lt _ _ _ _ h3]
          exact hinv i hi
        · have e1 : (stepW U g).getD i false = U.getD i false := by
            simp only [stepW]; exact getD_app_lt _ _ _ _ h1
          have e2 : (stepW U' (ren f g)).getD (f i) false = false :=
            getD_ge _ _ _ (by rw [stepW_len]; omega)
          have e3 : U'.getD (f i) false = false := getD_ge _ _ _ (by omega)
          rw [e1, e2, hinv i hi, e3]
      · simp only [stepW]
        rw [h2, h1, getD_app_len, getD_app_len]
        exact hgate
      · have e1 : (stepW U g).getD i false = false :=
          getD_ge _ _ _ (by rw [stepW_len]; omega)
        have e2 : (stepW U' (ren f g)).getD (f i) false = false :=
          getD_ge _ _ _ (by rw [stepW_len]; omega)
        rw [e1, e2]

theorem erase_def (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    eraseGate n C m p =
      { gates := C.gates.take m ++ (C.gates.drop (m + 1)).map (ren (eraseRedirect n m p))
        output := eraseRedirect n m p C.output } := by
  simp only [eraseGate, if_pos hm]; rfl

theorem erase_fanin (n : ℕ) (C : Circuit) (m p : ℕ) (hM : FanInTwo C)
    (hm : m < C.gates.length) : FanInTwo (eraseGate n C m p) := by
  rw [erase_def n C m p hm]
  intro g hg
  simp only [List.mem_append, List.mem_map] at hg
  rcases hg with hg | ⟨g0, hg0, rfl⟩
  · exact hM g (List.mem_of_mem_take hg)
  · have := hM g0 (List.mem_of_mem_drop hg0)
    simpa [ren] using this

theorem erase_size (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).size + 1 = C.size := by
  rw [erase_def n C m p hm]
  simp only [Circuit.size, List.length_append, List.length_take, List.length_map,
    List.length_drop]
  omega

theorem erase_eval (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hp : p < n + m ∨ n + C.gates.length ≤ p) (X : List Bool) (hXl : X.length = n)
    (h : (C.wires X).getD (n + m) false = (C.wires X).getD p false ∨
      (C.output ≠ n + m ∧ ∀ g ∈ C.gates.drop (m + 1), n + m ∉ g.inputs)) :
    (eraseGate n C m p).eval X = C.eval X := by
  obtain ⟨V, hV⟩ : ∃ V, V = (C.gates.take m).foldl stepW X := ⟨_, rfl⟩
  have hVl : V.length = n + m := by
    rw [hV, foldl_len, hXl]; simp; omega
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    conv_lhs => rw [← List.take_append_drop m C.gates]
    rw [List.drop_eq_getElem_cons hm]
  have hW : C.wires X = (C.gates.drop (m + 1)).foldl stepW (stepW V C.gates[m]) := by
    show C.gates.foldl stepW X = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons, hV]
  have hW' : (eraseGate n C m p).wires X =
      ((C.gates.drop (m + 1)).map (ren (eraseRedirect n m p))).foldl stepW V := by
    rw [erase_def n C m p hm]
    show (C.gates.take m ++ (C.gates.drop (m + 1)).map (ren (eraseRedirect n m p))).foldl
      stepW X = _
    rw [List.foldl_append, hV]
  have hWl : (C.wires X).length = n + C.gates.length := by
    show (C.gates.foldl stepW X).length = _
    rw [foldl_len, hXl]
  have hS : (stepW V C.gates[m]).length = n + m + 1 := by rw [stepW_len, hVl]
  have hDl : (C.gates.drop (m + 1)).length + m + 1 = C.gates.length := by
    simp; omega
  let A : Prop := (C.wires X).getD (n + m) false = (C.wires X).getD p false
  let ok : ℕ → Prop := fun i => i ≠ n + m ∨ A
  have hok : ∀ g ∈ C.gates.drop (m + 1), ∀ i ∈ g.inputs, ok i := by
    intro g hg i hi
    rcases h with hA | ⟨_, hB⟩
    · exact Or.inr hA
    · left
      intro he
      exact hB g hg (he ▸ hi)
  have hgood : ∀ k < (C.gates.drop (m + 1)).length, ∀ i, ok i →
      Good (eraseRedirect n m p) ((stepW V C.gates[m]).length + k) (V.length + k) i := by
    intro k hk i _
    rw [hS, hVl]
    unfold Good eraseRedirect
    split_ifs with h1 h2 <;> omega
  have hinit : ∀ i, ok i → (stepW V C.gates[m]).getD i false =
      V.getD (eraseRedirect n m p i) false := by
    intro i hi
    rcases lt_trichotomy i (n + m) with h1 | h1 | h1
    · have hf : eraseRedirect n m p i = i := by
        unfold eraseRedirect; split_ifs <;> omega
      rw [hf]; simp only [stepW]
      rw [getD_app_lt _ _ _ _ (by omega)]
    · have hA : A := by
        rcases hi with hi | hi
        · exact absurd h1 hi
        · exact hi
      have hf : eraseRedirect n m p i = p := by
        unfold eraseRedirect; simp [h1]
      rw [hf]
      have e1 : (stepW V C.gates[m]).getD i false = (C.wires X).getD (n + m) false := by
        rw [hW, foldl_getD_lt _ _ _ (by omega), h1]
      rw [e1, hA]
      rcases hp with hp | hp
      · rw [hW, foldl_getD_lt _ _ _ (by omega)]
        simp only [stepW]
        rw [getD_app_lt _ _ _ _ (by omega)]
      · rw [getD_ge _ _ _ (by omega), getD_ge _ _ _ (by omega)]
    · have hf : eraseRedirect n m p i = i - 1 := by
        unfold eraseRedirect; split_ifs <;> omega
      rw [hf, getD_ge _ _ _ (by omega), getD_ge _ _ _ (by omega)]
  have hout : ok C.output := by
    rcases h with hA | ⟨hB, _⟩
    · exact Or.inr hA
    · exact Or.inl hB
  have hsim := sim (eraseRedirect n m p) ok (C.gates.drop (m + 1)) (stepW V C.gates[m]) V
    hok hgood hinit C.output hout
  show ((eraseGate n C m p).wires X).getD (eraseGate n C m p).output false =
    (C.wires X).getD C.output false
  rw [hW', hW, hsim, erase_def n C m p hm]

def restr {n : ℕ} (a b : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  Function.update (Function.update x a false) b false

def subF (n L a b : ℕ) (i : ℕ) : ℕ := if i = a ∨ i = b then n + L else i

def subC (n : ℕ) (a b : ℕ) (D : Circuit) : Circuit :=
  ⟨D.gates.map (ren (subF n D.gates.length a b)), subF n D.gates.length a b D.output⟩

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · exact getD_ge _ _ _ (by simp; omega)

theorem subC_eval {n : ℕ} (a b : Fin n) (D : Circuit) (x : Fin n → Bool) :
    (subC n a.val b.val D).eval (List.ofFn x) = D.eval (List.ofFn (restr a b x)) := by
  have hsim := sim (subF n D.gates.length a.val b.val) (fun _ => True) D.gates
    (List.ofFn (restr a b x)) (List.ofFn x) (fun _ _ _ _ => trivial)
    (by
      intro k hk i _
      simp only [List.length_ofFn]
      have ha := a.isLt
      have hb := b.isLt
      unfold Good
      by_cases hab : i = a.val ∨ i = b.val
      · have hs : subF n D.gates.length a.val b.val i = n + D.gates.length := by
          unfold subF; rw [if_pos hab]
        rw [hs]; left; constructor
        · rcases hab with h | h <;> omega
        · omega
      · have hs : subF n D.gates.length a.val b.val i = i := by
          unfold subF; rw [if_neg hab]
        rw [hs]; omega)
    (by
      intro i _
      rw [ofFn_getD, ofFn_getD]
      have ha := a.isLt
      have hb := b.isLt
      by_cases hab : i = a.val ∨ i = b.val
      · have hs : subF n D.gates.length a.val b.val i = n + D.gates.length := by
          unfold subF; rw [if_pos hab]
        have hin : i < n := by rcases hab with h | h <;> omega
        rw [hs, dif_pos hin, dif_neg (by omega)]
        rcases hab with h | h
        · have he : (⟨i, hin⟩ : Fin n) = a := Fin.ext h
          rw [he]
          simp only [restr]
          by_cases hab2 : a = b
          · rw [hab2, Function.update_self]
          · rw [Function.update_of_ne hab2, Function.update_self]
        · have he : (⟨i, hin⟩ : Fin n) = b := Fin.ext h
          rw [he]
          simp only [restr, Function.update_self]
      · have hs : subF n D.gates.length a.val b.val i = i := by
          unfold subF; rw [if_neg hab]
        rw [hs]
        by_cases hin : i < n
        · rw [dif_pos hin, dif_pos hin]
          simp only [restr]
          have hb' : (⟨i, hin⟩ : Fin n) ≠ b := fun he => hab (Or.inr (by rw [← he]))
          have ha' : (⟨i, hin⟩ : Fin n) ≠ a := fun he => hab (Or.inl (by rw [← he]))
          rw [Function.update_of_ne hb', Function.update_of_ne ha']
        · rw [dif_neg hin, dif_neg hin])
    D.output trivial
  show ((subC n a.val b.val D).wires (List.ofFn x)).getD (subC n a.val b.val D).output false =
    (D.wires (List.ofFn (restr a b x))).getD D.output false
  have e1 : D.wires (List.ofFn (restr a b x)) = D.gates.foldl stepW (List.ofFn (restr a b x)) :=
    rfl
  have e2 : (subC n a.val b.val D).wires (List.ofFn x) =
      (D.gates.map (ren (subF n D.gates.length a.val b.val))).foldl stepW (List.ofFn x) := rfl
  rw [e1, e2, hsim]
  rfl

theorem subC_fanin (n a b : ℕ) (D : Circuit) (hD : FanInTwo D) : FanInTwo (subC n a b D) := by
  intro g hg
  simp only [subC, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have := hD g0 hg0
  simpa [ren] using this

theorem main : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x1) (x5 : ℕ → Circuit),
    FanInTwo (x5 0) →
    (∀ x7 < x2, ∃ (x9 : ℕ) (x10 : ℕ), x9 < (x5 x7).size ∧
      (x10 < x1 + x9 ∨ x1 + (x5 x7).size ≤ x10) ∧
      x5 (x7 + 1) = eraseGate x1 (x5 x7) x9 x10 ∧
      ((∀ (x11 : Fin x1 → Bool),
        ((x5 x7).wires (List.ofFn (restr x3 x4 x11))).getD (x1 + x9) false =
          ((x5 x7).wires (List.ofFn (restr x3 x4 x11))).getD x10 false) ∨
        (x5 x7).output ≠ x1 + x9 ∧ ∀ x11 ∈ List.drop (x9 + 1) (x5 x7).gates,
          x1 + x9 ∉ x11.inputs)) →
    ∃ (x8 : Circuit), FanInTwo x8 ∧ x8.size + x2 = (x5 0).size ∧
      ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = (x5 0).eval (List.ofFn (restr x3 x4 x9)) := by
  intro n K a b C h0 hstep
  have key : ∀ k ≤ K, FanInTwo (C k) ∧ (C k).size + k = (C 0).size ∧
      ∀ x : Fin n → Bool, (C k).eval (List.ofFn (restr a b x)) =
        (C 0).eval (List.ofFn (restr a b x)) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨h0, by simp, fun _ => rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨hF, hS, hE⟩ := ih (by omega)
      obtain ⟨m, p, hm, hp, heq, hcase⟩ := hstep k (by omega)
      have hm' : m < (C k).gates.length := hm
      have hS1 := erase_size n (C k) m p hm'
      rw [heq]
      refine ⟨erase_fanin n (C k) m p hF hm', by omega, ?_⟩
      intro x
      rw [← hE x]
      apply erase_eval n (C k) m p hm' hp _ (by simp)
      rcases hcase with hA | hB
      · exact Or.inl (hA x)
      · exact Or.inr hB
  obtain ⟨hF, hS, hE⟩ := key K le_rfl
  refine ⟨subC n a.val b.val (C K), subC_fanin _ _ _ _ hF, ?_, ?_⟩
  · have : (subC n a.val b.val (C K)).size = (C K).size := by
      simp [subC, Circuit.size]
    rw [this]; exact hS
  · intro x
    rw [subC_eval a b (C K) x, hE x]

end PEqualNP.Outside.L_meta_2642

theorem PEqualNP.Outside.L_meta_2642 : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x1) (x5 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo (x5 (0 : ℕ)) →     (∀ x7 < x2,         ∃ (x9 : ℕ) (x10 : ℕ),           x9 < (x5 x7).size ∧             (x10 < x1 + x9 ∨ x1 + (x5 x7).size ≤ x10) ∧               x5 (x7 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x5 x7) x9 x10 ∧                 ((∀ (x11 : Fin x1 → Bool),                     have x12 : List Bool := (x5 x7).wires (List.ofFn (Function.update (Function.update x11 x3 Bool.false) x4 Bool.false));                     x12.getD (x1 + x9) Bool.false = x12.getD x10 Bool.false) ∨                   (x5 x7).output ≠ x1 + x9 ∧ ∀ x11 ∈ List.drop (x9 + (1 : ℕ)) (x5 x7).gates, x1 + x9 ∉ x11.inputs)) →       ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + x2 = (x5 (0 : ℕ)).size ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = (x5 (0 : ℕ)).eval (List.ofFn (Function.update (Function.update x9 x3 Bool.false) x4 Bool.false)) :=
  PEqualNP.Outside.L_meta_2642.main
