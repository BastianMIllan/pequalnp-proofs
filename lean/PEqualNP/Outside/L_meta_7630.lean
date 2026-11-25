import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7630
open PEqualNP.CircuitLowerBounds

def touches (Z : Finset ℕ) (g : Gate) : Bool := g.inputs.any fun i => decide (i ∈ Z)

def repl (Z : Finset ℕ) (B : ℕ) (f : ℕ → ℕ) (g : Gate) : ℕ :=
  match g.op with
  | GateOp.or => (((g.inputs.filter (fun i => decide (i ∉ Z))).head?).map f).getD B
  | _ => B

def go (Z : Finset ℕ) (B : ℕ) : (ℕ → ℕ) → ℕ → ℕ → List Gate → List Gate × (ℕ → ℕ)
  | f, _, _, [] => ([], f)
  | f, o, c, g :: gs =>
    if touches Z g then go Z B (Function.update f o (repl Z B f g)) (o + 1) c gs
    else
      ((⟨g.op, g.inputs.map f⟩ : Gate) :: (go Z B (Function.update f o c) (o + 1) (c + 1) gs).1,
        (go Z B (Function.update f o c) (o + 1) (c + 1) gs).2)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem small (xs : List ℕ) (h : xs.length ≤ 2) :
    xs = [] ∨ (∃ a, xs = [a]) ∨ ∃ a b, xs = [a, b] := by
  match xs, h with
  | [], _ => exact Or.inl rfl
  | [a], _ => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | [a, b], _ => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
  | _ :: _ :: _ :: _, h => simp at h

theorem go_len (Z : Finset ℕ) (B : ℕ) : ∀ (gs : List Gate) (f : ℕ → ℕ) (o c : ℕ),
    (go Z B f o c gs).1.length + (gs.filter (touches Z)).length = gs.length := by
  intro gs
  induction gs with
  | nil => intro f o c; simp [go]
  | cons g gs ih =>
    intro f o c
    by_cases ht : touches Z g = true
    · have := ih (Function.update f o (repl Z B f g)) (o + 1) c
      simp only [go, ht, if_true, List.filter_cons, List.length_cons]
      omega
    · have := ih (Function.update f o c) (o + 1) (c + 1)
      simp only [go, ht, List.filter_cons, List.length_cons]
      simp only [Bool.false_eq_true, if_false, List.length_cons]
      omega

theorem go_mono (Z : Finset ℕ) (B : ℕ) : ∀ (gs : List Gate) (f : ℕ → ℕ) (o c : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    ∀ g ∈ (go Z B f o c gs).1,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro gs
  induction gs with
  | nil => intro f o c _ g hg; simp [go] at hg
  | cons g0 gs ih =>
    intro f o c hm g hg
    have hm' : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        g.inputs.length ≤ 2 := fun g h => hm g (List.mem_cons_of_mem _ h)
    by_cases ht : touches Z g0 = true
    · simp only [go, ht, if_true] at hg
      exact ih _ _ _ hm' g hg
    · simp only [go, ht, Bool.false_eq_true, if_false, List.mem_cons] at hg
      rcases hg with rfl | hg
      · obtain ⟨h1, h2⟩ := hm g0 List.mem_cons_self
        exact ⟨h1, by simpa using h2⟩
      · exact ih _ _ _ hm' g hg

theorem opt_cases (P : ℕ → Prop) (f : ℕ → ℕ) (B : ℕ) (h : ∀ k, P (f k)) (hB : P B) :
    ∀ o : Option ℕ, P ((o.map f).getD B) := by
  intro o
  cases o <;> simp [hB, h]

theorem repl_cases (Z : Finset ℕ) (B : ℕ) (f : ℕ → ℕ) (g : Gate) (P : ℕ → Prop)
    (h : ∀ k, P (f k)) (hB : P B) : P (repl Z B f g) := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp only [repl] <;> first | exact hB | exact opt_cases P f B h hB _

theorem repl_val (Z : Finset ℕ) (B : ℕ) (f : ℕ → ℕ) (g : Gate) (V W : List Bool)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hl : g.inputs.length ≤ 2)
    (ht : touches Z g = true) (hz : ∀ z ∈ Z, W.getD z false = false)
    (hinv : ∀ k, V.getD (f k) false = W.getD k false) (hB : V.getD B false = false) :
    V.getD (repl Z B f g) false = g.op.eval (g.inputs.map fun i => W.getD i false) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hl
  rcases small ins hl with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · rcases hop with rfl | rfl <;> simp [touches] at ht
  · rcases hop with rfl | rfl <;> by_cases ha : a ∈ Z <;>
      simp_all [repl, touches, GateOp.eval]
  · rcases hop with rfl | rfl <;> by_cases ha : a ∈ Z <;> by_cases hb : b ∈ Z <;>
      simp_all [repl, touches, GateOp.eval]

theorem go_spec (Z : Finset ℕ) (B : ℕ) : ∀ (gs : List Gate) (f : ℕ → ℕ) (o c : ℕ)
    (V W : List Bool),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    o + gs.length = B → c ≤ o → V.length = c → W.length = o →
    (∀ z ∈ Z, z < W.length ∧ W.getD z false = false) →
    (∀ k, f k < c ∨ f k = B) → (∀ k, o ≤ k → f k = B) →
    (∀ k, V.getD (f k) false = W.getD k false) →
    ∀ k, (run (go Z B f o c gs).1 V).getD ((go Z B f o c gs).2 k) false =
      (run gs W).getD k false := by
  intro gs
  induction gs with
  | nil =>
    intro f o c V W _ _ _ _ _ _ _ _ hinv k
    simpa [go, run] using hinv k
  | cons g gs ih =>
    intro f o c V W hm hB hco hV hW hz hlt hge hinv k
    have hm' : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        g.inputs.length ≤ 2 := fun g h => hm g (List.mem_cons_of_mem _ h)
    obtain ⟨hop, hl⟩ := hm g List.mem_cons_self
    simp only [List.length_cons] at hB
    have hVB : ∀ j, c ≤ j → V.getD j false = false := fun j hj =>
      List.getD_eq_default _ _ (by omega)
    have hWB : ∀ j, o ≤ j → W.getD j false = false := fun j hj =>
      List.getD_eq_default _ _ (by omega)
    have hrunW : run (g :: gs) W =
        run gs (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
    rw [hrunW]
    by_cases ht : touches Z g = true
    · simp only [go, ht, if_true]
      apply ih
      · exact hm'
      · omega
      · omega
      · exact hV
      · simp [hW]
      · intro z hzZ
        obtain ⟨h1, h2⟩ := hz z hzZ
        refine ⟨by simp; omega, ?_⟩
        rw [List.getD_append _ _ _ _ h1]; exact h2
      · intro j
        by_cases hj : j = o
        · subst hj; simp only [Function.update_self]
          exact repl_cases Z B f g (fun t => t < c ∨ t = B) hlt (Or.inr rfl)
        · simp only [Function.update_of_ne hj]; exact hlt j
      · intro j hj
        rw [Function.update_of_ne (by omega)]; exact hge j (by omega)
      · intro j
        rcases lt_trichotomy j o with hj | hj | hj
        · rw [Function.update_of_ne (by omega), List.getD_append _ _ _ _ (by omega)]
          exact hinv j
        · subst hj
          rw [Function.update_self, List.getD_append_right _ _ _ _ (by omega)]
          simp only [hW, Nat.sub_self, List.getD_cons_zero]
          exact repl_val Z B f g V W hop hl ht (fun z hzZ => (hz z hzZ).2) hinv
            (hVB B (by omega))
        · rw [Function.update_of_ne (by omega), hge j (by omega), hVB B (by omega),
            List.getD_eq_default _ _ (by simp; omega)]
    · have hval : g.op.eval ((g.inputs.map f).map fun i => V.getD i false) =
          g.op.eval (g.inputs.map fun i => W.getD i false) := by
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact hinv i
      have hrunV : ∀ rest : List Gate, run ((⟨g.op, g.inputs.map f⟩ : Gate) :: rest) V =
          run rest (V ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := by
        intro rest
        rw [← hval]; rfl
      simp only [go, ht, Bool.false_eq_true, if_false]
      rw [hrunV]
      apply ih
      · exact hm'
      · omega
      · omega
      · simp [hV]
      · simp [hW]
      · intro z hzZ
        obtain ⟨h1, h2⟩ := hz z hzZ
        refine ⟨by simp; omega, ?_⟩
        rw [List.getD_append _ _ _ _ h1]; exact h2
      · intro j
        by_cases hj : j = o
        · subst hj; simp only [Function.update_self]; omega
        · simp only [Function.update_of_ne hj]
          rcases hlt j with h | h
          · left; omega
          · right; exact h
      · intro j hj
        rw [Function.update_of_ne (by omega)]; exact hge j (by omega)
      · intro j
        rcases lt_trichotomy j o with hj | hj | hj
        · rw [Function.update_of_ne (by omega),
            List.getD_append _ _ _ _ (show j < W.length by omega)]
          rcases hlt j with h | h
          · rw [List.getD_append _ _ _ _ (show f j < V.length by omega)]; exact hinv j
          · have hlen : (V ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]).length ≤ B := by
              simp only [List.length_append, List.length_singleton]; omega
            rw [h, List.getD_eq_default _ _ hlen, ← hinv j, h, hVB B (by omega)]
        · subst hj
          rw [Function.update_self, List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega)]
          simp [hW, hV]
        · rw [Function.update_of_ne (by omega), hge j (by omega),
            List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_7630

theorem PEqualNP.Outside.L_meta_7630 : ∀ (x1 : ℕ) (x2 : Finset ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x4 ∈ x2, x4 < x1) → PEqualNP.MetaComplexity.Monotone2 x3 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size + (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.inputs.any fun (x8 : ℕ) => Decidable.decide (x8 ∈ x2)) x3.gates).length = x3.size ∧ ∀ (x7 : List Bool), x7.length = x1 → (∀ x9 ∈ x2, x7.getD x9 Bool.false = Bool.false) → x6.eval x7 = x3.eval x7 := by
  intro n Z C hZ hmon
  obtain ⟨gs, out⟩ := C
  let B := n + gs.length
  let f0 : ℕ → ℕ := fun k => if k < n then k else B
  refine ⟨⟨(PEqualNP.Outside.L_meta_7630.go Z B f0 n n gs).1,
    (PEqualNP.Outside.L_meta_7630.go Z B f0 n n gs).2 out⟩, ?_, ?_, ?_⟩
  · intro g hg
    exact PEqualNP.Outside.L_meta_7630.go_mono Z B gs f0 n n hmon g hg
  · exact PEqualNP.Outside.L_meta_7630.go_len Z B gs f0 n n
  · intro x hx hz0
    change (PEqualNP.Outside.L_meta_7630.run (PEqualNP.Outside.L_meta_7630.go Z B f0 n n gs).1 x).getD
        ((PEqualNP.Outside.L_meta_7630.go Z B f0 n n gs).2 out) false =
      (PEqualNP.Outside.L_meta_7630.run gs x).getD out false
    apply PEqualNP.Outside.L_meta_7630.go_spec Z B gs f0 n n x x hmon rfl le_rfl hx hx
    · intro z hzZ
      exact ⟨by rw [hx]; exact hZ z hzZ, hz0 z hzZ⟩
    · intro k
      by_cases hk : k < n
      · left; simp [f0, hk]
      · right; simp [f0, hk]
    · intro k hk
      simp [f0, show ¬ k < n by omega]
    · intro k
      by_cases hk : k < n
      · simp [f0, hk]
      · simp only [f0, hk, if_false]
        rw [List.getD_eq_default _ _ (by simp [B]; omega),
          List.getD_eq_default _ _ (by omega)]
