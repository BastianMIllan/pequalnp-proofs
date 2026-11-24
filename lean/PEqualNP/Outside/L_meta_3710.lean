import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3710

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

lemma foldl_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stp w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, stp, List.length_append, List.length_cons,
      List.length_singleton, List.length_nil]
    omega

lemma foldl_prefix (gs : List Gate) : ∀ w : List Bool, w <+: gs.foldl stp w := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; exact (List.prefix_append w _).trans (ih _)

lemma getD_of_prefix {w L : List Bool} (h : w <+: L) {i : ℕ} (hi : i < w.length) :
    L.getD i false = w.getD i false := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (C.gates[j]).inputs, i < x.length + j) :
    (C.wires x).getD (x.length + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  rw [wires_eq]
  have hsplit : C.gates = C.gates.take j ++ (C.gates[j] :: C.gates.drop (j+1)) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have hPl : ((C.gates.take j).foldl stp x).length = x.length + j := by
    rw [foldl_len]; simp [List.length_take]; omega
  have hW : C.gates.foldl stp x =
      (C.gates.drop (j+1)).foldl stp (stp ((C.gates.take j).foldl stp x) C.gates[j]) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hpre1 : stp ((C.gates.take j).foldl stp x) C.gates[j] <+: C.gates.foldl stp x := by
    rw [hW]; exact foldl_prefix _ _
  have hpre0 : (C.gates.take j).foldl stp x <+: C.gates.foldl stp x :=
    (List.prefix_append _ _).trans hpre1
  rw [getD_of_prefix hpre1 (by simp [stp, hPl])]
  have e : (stp ((C.gates.take j).foldl stp x) C.gates[j]).getD (x.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        ((C.gates.take j).foldl stp x).getD i false) := by
    rw [← hPl]
    simp [stp, List.getD_eq_getElem?_getD]
  rw [e]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [getD_of_prefix hpre0 (by rw [hPl]; exact hrb i hi)]

lemma wires_input (C : Circuit) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < n) :
    (C.wires (List.ofFn x)).getD k false = x ⟨k, hk⟩ := by
  rw [wires_eq, getD_of_prefix (foldl_prefix _ _) (by simpa using hk)]
  simp [List.getD_eq_getElem?_getD, hk]

lemma wires_big (C : Circuit) (x : List Bool) (k : ℕ) (hk : x.length + C.gates.length ≤ k) :
    (C.wires x).getD k false = false := by
  rw [wires_eq, List.getD_eq_default]
  rw [foldl_len]; exact hk

def RB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j (hj : j < C.gates.length), ∀ i ∈ (C.gates[j]).inputs, i < n + j

lemma compare {n : ℕ} (D1 D2 : Circuit) (x1 x2 : Fin n → Bool)
    (hlen : D1.gates.length = D2.gates.length)
    (h1 : RB n D1) (h2 : RB n D2)
    (hx : ∀ i, x1 i = true → x2 i = true)
    (hstep : ∀ j (hj1 : j < D1.gates.length) (hj2 : j < D2.gates.length),
      (∀ k < n + j, (D1.wires (List.ofFn x1)).getD k false = true →
        (D2.wires (List.ofFn x2)).getD k false = true) →
      (D1.gates[j]).op.eval ((D1.gates[j]).inputs.map fun i =>
        (D1.wires (List.ofFn x1)).getD i false) = true →
      (D2.gates[j]).op.eval ((D2.gates[j]).inputs.map fun i =>
        (D2.wires (List.ofFn x2)).getD i false) = true) :
    ∀ k, (D1.wires (List.ofFn x1)).getD k false = true →
      (D2.wires (List.ofFn x2)).getD k false = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hkn : k < n
    · rw [wires_input _ _ k hkn] at hk ⊢; exact hx _ hk
    · by_cases hkm : k < n + D1.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, by omega⟩
        have hj1 : j < D1.gates.length := by omega
        have hj2 : j < D2.gates.length := by omega
        have e1 := wires_gate D1 (List.ofFn x1) j hj1 (by simpa using h1 j hj1)
        have e2 := wires_gate D2 (List.ofFn x2) j hj2 (by simpa using h2 j hj2)
        simp only [List.length_ofFn] at e1 e2
        rw [e1] at hk; rw [e2]
        exact hstep j hj1 hj2 (fun k' hk' => ih k' hk') hk
      · rw [wires_big D1 (List.ofFn x1) k (by simp; omega)] at hk
        exact absurd hk (by simp)

lemma eval_mono (op : GateOp) (hop : op = .and ∨ op = .or) (u1 u2 v1 v2 : Bool)
    (h1 : u1 = true → v1 = true) (h2 : u2 = true → v2 = true) :
    op.eval [u1, u2] = true → op.eval [v1, v2] = true := by
  rcases hop with rfl | rfl <;> cases u1 <;> cases u2 <;> cases v1 <;> cases v2 <;>
    simp_all [GateOp.eval]

def rew (C : Circuit) (r : ℕ → ℕ) : Circuit :=
  { gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map r } : Gate)),
    output := C.output }

lemma rew_len (C : Circuit) (r : ℕ → ℕ) : (rew C r).gates.length = C.gates.length := by
  simp [rew]

lemma rew_get (C : Circuit) (r : ℕ → ℕ) (j : ℕ) (hj1 : j < (rew C r).gates.length)
    (hj : j < C.gates.length) :
    (rew C r).gates[j] = ({ op := (C.gates[j]).op, inputs := (C.gates[j]).inputs.map r } : Gate) := by
  simp [rew]

lemma rew_RB {n : ℕ} (C : Circuit) (r : ℕ → ℕ) (hC : RB n C)
    (hr : ∀ j (hj : j < C.gates.length), ∀ i ∈ (C.gates[j]).inputs, r i ≤ i) :
    RB n (rew C r) := by
  intro j hj i hi
  have hj' : j < C.gates.length := by simpa [rew] using hj
  rw [rew_get C r j hj hj'] at hi
  simp only [List.mem_map] at hi
  obtain ⟨i0, hi0, rfl⟩ := hi
  exact lt_of_le_of_lt (hr j hj' i0 hi0) (hC j hj' i0 hi0)

lemma two_of {g : Gate} (h : g.inputs.length = 2) : ∃ p q, g.inputs = [p, q] :=
  List.length_eq_two.mp h

-- monotonicity of an AND/OR circuit
lemma mono {n : ℕ} (C : Circuit) (hRB : RB n C)
    (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ k, (C.wires (List.ofFn x)).getD k false = true →
      (C.wires (List.ofFn y)).getD k false = true := by
  apply compare C C x y rfl hRB hRB hxy
  intro j hj1 _ ih
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj1
  obtain ⟨p, q, hpq⟩ := two_of (h2 _ hmem)
  rw [hpq]
  simp only [List.map_cons, List.map_nil]
  apply eval_mono _ (hAO _ hmem)
  · exact ih p (hRB j hj1 p (by rw [hpq]; simp))
  · exact ih q (hRB j hj1 q (by rw [hpq]; simp))

theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (g a b : ℕ) (v : Fin n),
  PEqualNP.TopForm.IsAO2 n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  g < C.gates.length →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [a, b] ∨
    (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [b, a]) →
  (C.wires (List.ofFn (PEqualNP.SplitCount.unitInput v))).getD b false = true →
  (∀ w : Fin n, G.Adj v w → (C.wires (List.ofFn (PEqualNP.SplitCount.unitInput w))).getD b false = true) →
  PEqualNP.MetaComplexity.circuitFun n
      ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun i => if i = n + g then a else i) } : PEqualNP.CircuitLowerBounds.Gate)),
         output := C.output } : PEqualNP.CircuitLowerBounds.Circuit)
    = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C g a b v hAO2 hfun hg hop hin hbv hbN
  obtain ⟨hAO, hRB0, h2⟩ := hAO2
  have hRB : RB n C := by
    intro j hj i hi
    have := hRB0 j hj i
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ hj] at this
    exact this hi
  have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C g = C.gates[g] := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    exact List.getD_eq_getElem _ _ hg
  rw [hgate] at hop hin
  set r : ℕ → ℕ := fun i => if i = n + g then a else i with hr
  have ha : a < n + g := hRB g hg a (by rcases hin with h | h <;> rw [h] <;> simp)
  -- the value of gate g
  have hgval : ∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD (n + g) false =
      ((C.wires (List.ofFn z)).getD a false && (C.wires (List.ofFn z)).getD b false) := by
    intro z
    have e := wires_gate C (List.ofFn z) g hg (by simpa using hRB g hg)
    simp only [List.length_ofFn] at e
    rw [e, hop]
    rcases hin with h | h <;> rw [h] <;> simp [GateOp.eval, Bool.and_comm]
  have hrle : ∀ j (hj : j < C.gates.length), ∀ i ∈ (C.gates[j]).inputs, r i ≤ i := by
    intro j hj i hi
    simp only [hr]
    split_ifs with h
    · omega
    · exact le_rfl
  have hRB' : RB n (rew C r) := rew_RB C r hRB hrle
  have hlen := rew_len C r
  -- direction B: old at x below new at x
  have dirB : ∀ x : Fin n → Bool, ∀ k, (C.wires (List.ofFn x)).getD k false = true →
      ((rew C r).wires (List.ofFn x)).getD k false = true := by
    intro x
    apply compare C (rew C r) x x hlen.symm hRB hRB' (fun _ h => h)
    intro j hj1 hj2 ih
    have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj1
    obtain ⟨p, q, hpq⟩ := two_of (h2 _ hmem)
    rw [rew_get C r j hj2 hj1]
    simp only [hpq, List.map_cons, List.map_nil]
    apply eval_mono _ (hAO _ hmem)
    · intro hp
      have hpl : p < n + j := hRB j hj1 p (by rw [hpq]; simp)
      by_cases hpg : p = n + g
      · have : r p = a := by simp [hr, hpg]
        rw [this]
        rw [hpg, hgval] at hp
        exact ih a (by omega) ((Bool.and_eq_true _ _).mp hp).1
      · have : r p = p := by simp [hr, hpg]
        rw [this]; exact ih p hpl hp
    · intro hp
      have hpl : q < n + j := hRB j hj1 q (by rw [hpq]; simp)
      by_cases hpg : q = n + g
      · have : r q = a := by simp [hr, hpg]
        rw [this]
        rw [hpg, hgval] at hp
        exact ih a (by omega) ((Bool.and_eq_true _ _).mp hp).1
      · have : r q = q := by simp [hr, hpg]
        rw [this]; exact ih q hpl hp
  -- direction A: new at x below old at y when b is on at y
  have dirA : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      (C.wires (List.ofFn y)).getD b false = true →
      ∀ k, ((rew C r).wires (List.ofFn x)).getD k false = true →
        (C.wires (List.ofFn y)).getD k false = true := by
    intro x y hxy hby
    apply compare (rew C r) C x y hlen hRB' hRB hxy
    intro j hj1 hj2 ih
    have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj2
    obtain ⟨p, q, hpq⟩ := two_of (h2 _ hmem)
    rw [rew_get C r j hj1 hj2]
    simp only [hpq, List.map_cons, List.map_nil]
    apply eval_mono _ (hAO _ hmem)
    · intro hp
      have hpl : p < n + j := hRB j hj2 p (by rw [hpq]; simp)
      by_cases hpg : p = n + g
      · have : r p = a := by simp [hr, hpg]
        rw [this] at hp
        rw [hpg, hgval, hby]
        simpa using ih a (by omega) hp
      · have : r p = p := by simp [hr, hpg]
        rw [this] at hp; exact ih p hpl hp
    · intro hp
      have hpl : q < n + j := hRB j hj2 q (by rw [hpq]; simp)
      by_cases hpg : q = n + g
      · have : r q = a := by simp [hr, hpg]
        rw [this] at hp
        rw [hpg, hgval, hby]
        simpa using ih a (by omega) hp
      · have : r q = q := by simp [hr, hpg]
        rw [this] at hp; exact ih q hpl hp
  have hmono := mono C hRB hAO h2
  -- the main argument
  have hC : ∀ x, (C.wires (List.ofFn x)).getD C.output false =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x := fun x => congrFun hfun x
  show (fun x => ((rew C r).wires (List.ofFn x)).getD (rew C r).output false) = _
  funext x
  have hout : (rew C r).output = C.output := rfl
  rw [hout]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hnew
    by_cases hbx : (C.wires (List.ofFn x)).getD b false = true
    · rw [← hC]; exact dirA x x (fun _ h => h) hbx _ hnew
    · -- v and its neighbours are off in x
      have hxw : ∀ w, G.Adj v w → x w = false := by
        intro w hw
        by_contra hc
        apply hbx
        apply hmono (PEqualNP.SplitCount.unitInput w) x _ b (hbN w hw)
        intro i hi
        simp [PEqualNP.SplitCount.unitInput] at hi
        subst hi; simpa using hc
      set y := Function.update x v true with hy
      have hxy : ∀ i, x i = true → y i = true := by
        intro i hi
        by_cases h : i = v
        · subst h; simp [hy]
        · simp [hy, h, hi]
      have hby : (C.wires (List.ofFn y)).getD b false = true := by
        apply hmono (PEqualNP.SplitCount.unitInput v) y _ b hbv
        intro i hi
        simp [PEqualNP.SplitCount.unitInput] at hi
        subst hi; simp [hy]
      have hFy := dirA x y hxy hby _ hnew
      rw [hC] at hFy
      simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true,
        decide_eq_true_eq] at hFy ⊢
      rcases hFy with ⟨a', ha', _⟩ | ⟨u, w, huw, hu, hw⟩
      · simp at ha'
      right
      by_cases huv : u = v
      · have hwv : w ≠ v := fun h => huw.ne (huv.trans h.symm)
        have : y w = x w := by simp [hy, hwv]
        rw [this, hxw w (by rw [← huv]; exact huw)] at hw; exact absurd hw (by simp)
      · by_cases hwv : w = v
        · have : y u = x u := by simp [hy, huv]
          rw [this, hxw u (by rw [← hwv]; exact huw.symm)] at hu; exact absurd hu (by simp)
        · refine ⟨u, w, huw, ?_, ?_⟩
          · simpa [hy, huv] using hu
          · simpa [hy, hwv] using hw
  · intro hF
    rw [← hC] at hF
    exact dirB x _ hF

end PEqualNP.Outside.L_meta_3710

theorem PEqualNP.Outside.L_meta_3710 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (g a b : ℕ) (v : Fin n),
  PEqualNP.TopForm.IsAO2 n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  g < C.gates.length →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [a, b] ∨
    (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [b, a]) →
  (C.wires (List.ofFn (PEqualNP.SplitCount.unitInput v))).getD b false = true →
  (∀ w : Fin n, G.Adj v w → (C.wires (List.ofFn (PEqualNP.SplitCount.unitInput w))).getD b false = true) →
  PEqualNP.MetaComplexity.circuitFun n
      ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun i => if i = n + g then a else i) } : PEqualNP.CircuitLowerBounds.Gate)),
         output := C.output } : PEqualNP.CircuitLowerBounds.Circuit)
    = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C g a b v
  exact PEqualNP.Outside.L_meta_3710.main n G C g a b v
