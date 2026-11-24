import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1708

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (s : List Bool) : List Bool := gs.foldl step s

def ren (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def pin (v dead : ℕ) (i : ℕ) : ℕ := if i = v then dead else i

def shift (k r : ℕ) (i : ℕ) : ℕ := if i < k then i else if i = k then r else i - 1

theorem run_append (a b : List Gate) (s : List Bool) : run (a ++ b) s = run b (run a s) := by
  simp [run, List.foldl_append]

theorem run_cons (g : Gate) (b : List Gate) (s : List Bool) :
    run (g :: b) s = run b (step s g) := rfl

theorem run_length (gs : List Gate) (s : List Bool) :
    (run gs s).length = s.length + gs.length := by
  induction gs generalizing s with
  | nil => simp [run]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp [step]
    omega

theorem sim (f : ℕ → ℕ) (P P' : List Bool) (N : ℕ)
    (H : ∀ c : List Bool, c.length ≤ N → ∀ i, (P ++ c).getD i false = (P' ++ c).getD (f i) false) :
    ∀ (B : List Gate) (c : List Bool), c.length + B.length ≤ N →
      ∃ c₂ : List Bool, c₂.length = c.length + B.length ∧ run B (P ++ c) = P ++ c₂ ∧
        run (B.map (ren f)) (P' ++ c) = P' ++ c₂ := by
  intro B
  induction B with
  | nil =>
    intro c _
    exact ⟨c, by simp, rfl, rfl⟩
  | cons g B ih =>
    intro c hc
    have hc' : c.length ≤ N := by
      simp at hc
      omega
    have hv : g.op.eval (g.inputs.map fun i => (P ++ c).getD i false)
        = (ren f g).op.eval ((ren f g).inputs.map fun i => (P' ++ c).getD i false) := by
      simp only [ren, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact H c hc' i
    obtain ⟨c₂, h1, h2, h3⟩ := ih (c ++ [g.op.eval (g.inputs.map fun i => (P ++ c).getD i false)])
      (by
        simp at hc ⊢
        omega)
    refine ⟨c₂, by
      simp at h1 ⊢
      omega, ?_, ?_⟩
    · rw [run_cons]
      unfold step
      rw [List.append_assoc]
      exact h2
    · rw [List.map_cons, run_cons]
      unfold step
      rw [← hv, List.append_assoc]
      exact h3

theorem pinH {n : ℕ} (v : Fin n) (x : Fin n → Bool) (N dead : ℕ) (hd : n + N < dead) :
    ∀ c : List Bool, c.length ≤ N → ∀ i,
      (List.ofFn (Function.update x v false) ++ c).getD i false
        = (List.ofFn x ++ c).getD (pin v.val dead i) false := by
  intro c hc i
  unfold pin
  by_cases hi : i = v.val
  · rw [if_pos hi, hi, List.getD_eq_default (List.ofFn x ++ c) _ (by
      simp
      omega), List.getD_append (List.ofFn (Function.update x v false)) _ _ _ (by simp),
      List.getD_eq_getElem _ _ (by simp)]
    simp
  · rw [if_neg hi]
    by_cases hin : i < n
    · rw [List.getD_append _ _ _ _ (by simpa using hin),
        List.getD_append _ _ _ _ (by simpa using hin),
        List.getD_eq_getElem _ _ (by simpa using hin),
        List.getD_eq_getElem _ _ (by simpa using hin)]
      simp only [List.getElem_ofFn]
      apply Function.update_of_ne
      intro h
      apply hi
      rw [← h]
    · rw [List.getD_append_right _ _ _ _ (by
        simp
        omega), List.getD_append_right _ _ _ _ (by
        simp
        omega)]
      simp

theorem delH (u : List Bool) (k r N : ℕ) (hk : u.length = k) (hr : r < k ∨ k + N < r) :
    ∀ c : List Bool, c.length ≤ N → ∀ i,
      ((u ++ [u.getD r false]) ++ c).getD i false = (u ++ c).getD (shift k r i) false := by
  subst hk
  intro c hc i
  unfold shift
  by_cases h1 : i < u.length
  · rw [if_pos h1, List.getD_append _ _ _ _ (by
      simp
      omega), List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h1]
  · rw [if_neg h1]
    by_cases h2 : i = u.length
    · rw [if_pos h2, h2, List.getD_append _ _ _ _ (by simp),
        List.getD_append_right _ _ _ _ (le_refl _)]
      rcases hr with hr | hr
      · rw [List.getD_append _ _ _ _ hr]
        simp
      · rw [List.getD_eq_default (u ++ c) _ (by
          simp
          omega), List.getD_eq_default u _ (by omega)]
        simp
    · rw [if_neg h2, List.getD_append_right _ _ _ _ (by
        simp
        omega), List.getD_append_right _ _ _ _ (by omega)]
      congr 1
      simp
      omega

theorem gate_repl (g : Gate) (k dead : ℕ) (hk : k ≤ dead)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (hd : dead ∈ g.inputs) :
    ∃ r, (r < k ∨ r = dead) ∧ ∀ u : List Bool, u.length = k →
      g.op.eval (g.inputs.map fun i => u.getD i false) = u.getD r false := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen hd ⊢
  have hdead : ∀ u : List Bool, u.length = k → u.getD dead false = false :=
    fun u hu => List.getD_eq_default _ _ (by omega)
  match ins, hlen, hd with
  | [], _, hd => simp at hd
  | [a], _, hd =>
    simp at hd
    subst hd
    refine ⟨dead, Or.inr rfl, fun u hu => ?_⟩
    rcases hop with h | h <;> subst h <;> simp only [List.map_cons, List.map_nil, hdead u hu] <;> simp [GateOp.eval]
  | [a, b], _, hd =>
    simp at hd
    rcases hop with h | h
    · subst h
      refine ⟨dead, Or.inr rfl, fun u hu => ?_⟩
      rcases hd with h | h <;> subst h <;> simp only [List.map_cons, List.map_nil, hdead u hu] <;> simp [GateOp.eval]
    · subst h
      rcases hd with h | h
      · subst h
        by_cases hb : b < k
        · exact ⟨b, Or.inl hb, fun u hu => by
            simp only [List.map_cons, List.map_nil, hdead u hu]
            simp [GateOp.eval]⟩
        · exact ⟨dead, Or.inr rfl, fun u hu => by
            have hb' : u.getD b false = false := List.getD_eq_default _ _ (by omega)
            simp only [List.map_cons, List.map_nil, hdead u hu, hb']
            simp [GateOp.eval]⟩
      · subst h
        by_cases ha : a < k
        · exact ⟨a, Or.inl ha, fun u hu => by
            simp only [List.map_cons, List.map_nil, hdead u hu]
            simp [GateOp.eval]⟩
        · exact ⟨dead, Or.inr rfl, fun u hu => by
            have ha' : u.getD a false = false := List.getD_eq_default _ _ (by omega)
            simp only [List.map_cons, List.map_nil, hdead u hu, ha']
            simp [GateOp.eval]⟩
  | _ :: _ :: _ :: _, hlen, _ =>
    simp at hlen

theorem mono_ren (f : ℕ → ℕ) (L : List Gate)
    (h : ∀ g ∈ L, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ L.map (ren f), g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  have h0 := h g0 hg0
  simpa [ren] using h0

theorem deletion_eval {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (x : Fin n → Bool) :
    (∃ a b, G.Adj a b ∧ Function.update x v false a = true ∧
        Function.update x v false b = true) ↔
      ∃ a b, (G.deleteIncidenceSet v).Adj a b ∧ x a = true ∧ x b = true := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have hav : a ≠ v := by
      rintro rfl
      simp at ha
    have hbv : b ≠ v := by
      rintro rfl
      simp at hb
    exact ⟨a, b, (G.deleteIncidenceSet_adj).mpr ⟨hab, hav, hbv⟩,
      (Function.update_of_ne hav _ _).symm.trans ha, (Function.update_of_ne hbv _ _).symm.trans hb⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨hab, hav, hbv⟩ := G.deleteIncidenceSet_adj.mp hab
    exact ⟨a, b, hab, (Function.update_of_ne hav _ _).trans ha,
      (Function.update_of_ne hbv _ _).trans hb⟩

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) (v u : Fin n) (hu : G.Adj v u)
    (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) :
    ∃ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size < C.size ∧
      ∀ x : Fin n → Bool,
        C'.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v false)) := by
  obtain ⟨N, hN⟩ : ∃ N, N = C.gates.length := ⟨_, rfl⟩
  obtain ⟨dead, hdead⟩ : ∃ dead, dead = n + 2 * N + 1 := ⟨_, rfl⟩
  have hpin : ∀ x : Fin n → Bool, ∃ c₂ : List Bool, c₂.length = N ∧
      run C.gates (List.ofFn (Function.update x v false))
        = List.ofFn (Function.update x v false) ++ c₂ ∧
      run (C.gates.map (ren (pin v.val dead))) (List.ofFn x) = List.ofFn x ++ c₂ := by
    intro x
    obtain ⟨c₂, h0, h1, h2⟩ := sim (pin v.val dead) _ _ N (pinH v x N dead (by omega)) C.gates []
      (by
        simp
        omega)
    refine ⟨c₂, by
      simp at h0
      omega, ?_, ?_⟩
    · simpa using h1
    · simpa using h2
  have hCx : ∀ x : Fin n → Bool, ∀ c₂ : List Bool, c₂.length = N →
      run C.gates (List.ofFn (Function.update x v false))
        = List.ofFn (Function.update x v false) ++ c₂ →
      C.eval (List.ofFn (Function.update x v false))
        = (List.ofFn x ++ c₂).getD (pin v.val dead C.output) false := by
    intro x c₂ hc₂ h1
    show (run C.gates (List.ofFn (Function.update x v false))).getD C.output false = _
    rw [h1]
    exact pinH v x N dead (by omega) c₂ (by omega) C.output
  by_cases hex : ∃ g ∈ C.gates, v.val ∈ g.inputs
  · obtain ⟨g, hg, hvg⟩ := hex
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hg
    have hNAB : N = A.length + B.length + 1 := by
      rw [hN, hAB]
      simp
      omega
    have hgm := hm g hg
    have hop : (ren (pin v.val dead) g).op = GateOp.and ∨ (ren (pin v.val dead) g).op = GateOp.or := by
      simpa [ren] using hgm.1
    have hlen : (ren (pin v.val dead) g).inputs.length ≤ 2 := by
      simpa [ren] using hgm.2
    have hdm : dead ∈ (ren (pin v.val dead) g).inputs := by
      show dead ∈ g.inputs.map (pin v.val dead)
      exact List.mem_map.mpr ⟨v.val, hvg, by simp [pin]⟩
    obtain ⟨r, hr, hval⟩ := gate_repl (ren (pin v.val dead) g) (n + A.length) dead (by omega)
      hop hlen hdm
    have hr' : r < n + A.length ∨ n + A.length + N < r := by
      rcases hr with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    refine ⟨⟨A.map (ren (pin v.val dead)) ++
        (B.map (ren (pin v.val dead))).map (ren (shift (n + A.length) r)),
        shift (n + A.length) r (pin v.val dead C.output)⟩, ?_, ?_, ?_⟩
    · show ∀ g' ∈ (A.map (ren (pin v.val dead)) ++
        (B.map (ren (pin v.val dead))).map (ren (shift (n + A.length) r))),
        g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2
      intro g' hg'
      rcases List.mem_append.mp hg' with h | h
      · exact mono_ren _ A (fun g0 hg0 => hm g0 (by
          rw [hAB]
          simp [hg0])) g' h
      · exact mono_ren _ _ (mono_ren _ B (fun g0 hg0 => hm g0 (by
          rw [hAB]
          simp [hg0]))) g' h
    · show (A.map (ren (pin v.val dead)) ++
        (B.map (ren (pin v.val dead))).map (ren (shift (n + A.length) r))).length < C.gates.length
      rw [hAB]
      simp
    · intro x
      obtain ⟨c₂, hc₂, h1, h2⟩ := hpin x
      rw [hCx x c₂ hc₂ h1, ← h2]
      have hsplit : C.gates.map (ren (pin v.val dead))
          = A.map (ren (pin v.val dead)) ++ ren (pin v.val dead) g :: B.map (ren (pin v.val dead)) := by
        rw [hAB]
        simp
      rw [hsplit]
      show (run (A.map (ren (pin v.val dead)) ++
        (B.map (ren (pin v.val dead))).map (ren (shift (n + A.length) r))) (List.ofFn x)).getD
          (shift (n + A.length) r (pin v.val dead C.output)) false = _
      rw [run_append, run_append, run_cons]
      have hu' : (run (A.map (ren (pin v.val dead))) (List.ofFn x)).length = n + A.length := by
        rw [run_length]
        simp
      generalize run (A.map (ren (pin v.val dead))) (List.ofFn x) = w at hu'
      have hstep : step w (ren (pin v.val dead) g) = w ++ [w.getD r false] := by
        unfold step
        rw [hval w hu']
      rw [hstep]
      have hD := delH w (n + A.length) r N hu' hr'
      obtain ⟨c₃, hc₃, h3, h4⟩ := sim (shift (n + A.length) r) (w ++ [w.getD r false]) w N hD
        (B.map (ren (pin v.val dead))) [] (by
          simp
          omega)
      simp only [List.append_nil] at h3 h4
      rw [h3, h4]
      exact (hD c₃ (by
        simp at hc₃
        omega) (pin v.val dead C.output)).symm
  · exfalso
    have hmap : C.gates.map (ren (pin v.val dead)) = C.gates := by
      conv_rhs => rw [← List.map_id C.gates]
      apply List.map_congr_left
      intro g hg
      have hnot : v.val ∉ g.inputs := fun h => hex ⟨g, hg, h⟩
      obtain ⟨op, ins⟩ := g
      simp only [ren, id]
      congr 1
      conv_rhs => rw [← List.map_id ins]
      apply List.map_congr_left
      intro i hi
      simp only [pin, id]
      rw [if_neg]
      rintro rfl
      exact hnot hi
    have hloop : ∀ y : Fin n → Bool, (∀ t, y t = true → t = v) → C.eval (List.ofFn y) = true → False := by
      intro y hy h
      obtain ⟨a, b, hab, ha, hb⟩ := (hfun y).mp h
      rw [hy a ha, hy b hb] at hab
      exact G.irrefl hab
    by_cases hout : C.output = v.val
    · obtain ⟨c₂, hc₂, h1, h2⟩ := hpin (fun t => decide (t = v))
      rw [hmap] at h2
      apply hloop (fun t => decide (t = v)) (by
        intro t ht
        simpa using ht)
      show (run C.gates (List.ofFn (fun t => decide (t = v)))).getD C.output false = true
      rw [h2, hout, List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
      simp
    · obtain ⟨c₂, hc₂, h1, h2⟩ := hpin (fun t => decide (t = v ∨ t = u))
      rw [hmap] at h2
      have ht : C.eval (List.ofFn (fun t => decide (t = v ∨ t = u))) = true :=
        (hfun _).mpr ⟨v, u, hu, by simp, by simp⟩
      have hf := hCx (fun t => decide (t = v ∨ t = u)) c₂ hc₂ h1
      have hpo : pin v.val dead C.output = C.output := by
        simp [pin, hout]
      rw [hpo, ← h2] at hf
      have ht' : C.eval (List.ofFn (Function.update (fun t => decide (t = v ∨ t = u)) v false)) = true := by
        rw [hf]
        exact ht
      obtain ⟨a, b, hab, ha, hb⟩ := (hfun _).mp ht'
      have hav : a ≠ v := by
        rintro rfl
        simp at ha
      have hbv : b ≠ v := by
        rintro rfl
        simp at hb
      rw [Function.update_of_ne hav] at ha
      rw [Function.update_of_ne hbv] at hb
      have hau : a = u := by
        simpa [hav] using ha
      have hbu : b = u := by
        simpa [hbv] using hb
      rw [hau, hbu] at hab
      exact G.irrefl hab

end PEqualNP.Outside.L_meta_1708

theorem PEqualNP.Outside.L_meta_1708 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Fin x1), (0 : ℕ) < x2.degree x4 → x2.degree x4 ≤ (2 : ℕ) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (PEqualNP.MetaComplexity.circuitFun x1 x7 = fun (x9 : Fin x1 → Bool) => Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size < x7.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x10 = fun (x11 : Fin x1 → Bool) => Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x1), (x2.deleteIncidenceSet x4).Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) := by
  intro n G _ v hdeg _ C hm hfun
  obtain ⟨u, hu⟩ := (G.degree_pos_iff_exists_adj v).mp hdeg
  have hfun' : ∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) := by
    intro x
    have h := congrFun hfun x
    change C.eval (List.ofFn x) = _ at h
    rw [h]
    exact decide_eq_true_iff
  obtain ⟨C', hm', hs, hev⟩ := PEqualNP.Outside.L_meta_1708.main n G v u hu C hm hfun'
  refine ⟨C', hm', hs, ?_⟩
  funext x
  change C'.eval (List.ofFn x) = _
  rw [hev x, Bool.eq_iff_iff]
  exact (hfun' _).trans ((PEqualNP.Outside.L_meta_1708.deletion_eval G v x).trans
    decide_eq_true_iff.symm)
