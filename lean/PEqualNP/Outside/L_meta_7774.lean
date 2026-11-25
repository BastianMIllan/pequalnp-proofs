import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7774

open PEqualNP.CircuitLowerBounds

def rmap (n p t i : ℕ) : ℕ := if i < n + p then i else if i = n + p then t else i - 1

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_def (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepF x := rfl

def remap (n p t : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rmap n p t)⟩

def del (C : Circuit) (n p t : ℕ) : Circuit :=
  ⟨C.gates.take p ++ (C.gates.drop (p + 1)).map (remap n p t), rmap n p t C.output⟩

theorem foldl_prefix : ∀ (gs : List Gate) (w : List Bool), ∃ L, gs.foldl stepF w = w ++ L
  | [], w => ⟨[], by simp⟩
  | g :: gs, w => by
    obtain ⟨L, hL⟩ := foldl_prefix gs (stepF w g)
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ L, by
      rw [List.foldl_cons, hL]; simp [stepF]⟩

theorem foldl_length : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl stepF w).length = w.length + gs.length
  | [], w => by simp
  | g :: gs, w => by
    rw [List.foldl_cons, foldl_length gs (stepF w g)]
    simp [stepF]; omega

theorem getD_foldl_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl stepF w).getD i false = w.getD i false := by
  obtain ⟨L, hL⟩ := foldl_prefix gs w
  rw [hL, List.getD_append _ _ _ _ h]

def Inv (n p t : ℕ) (W W' : List Bool) : Prop :=
  W.length = W'.length + 1 ∧ n + p < W.length ∧
    ∀ i, W'.getD (rmap n p t i) false = W.getD i false

theorem inv_step (n p t : ℕ) (ht : t < n + p) (W W' : List Bool) (h : Inv n p t W W')
    (g : Gate) : Inv n p t (stepF W g) (stepF W' (remap n p t g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (remap n p t g).op.eval ((remap n p t g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [remap, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact h3 i
  refine ⟨by simp [stepF]; omega, by simp [stepF]; omega, ?_⟩
  intro i
  simp only [stepF]
  rw [hv]
  rcases lt_trichotomy i W.length with hi | hi | hi
  · have hr : rmap n p t i < W'.length := by unfold rmap; split_ifs <;> omega
    rw [List.getD_append _ _ _ _ hr, List.getD_append _ _ _ _ hi]
    exact h3 i
  · have hr : rmap n p t i = W'.length := by unfold rmap; split_ifs <;> omega
    rw [hr, List.getD_append_right _ _ _ _ le_rfl, hi, List.getD_append_right _ _ _ _ le_rfl]
    simp
  · have hr : W'.length + 1 < rmap n p t i + 1 := by unfold rmap; split_ifs <;> omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem inv_fold (n p t : ℕ) (ht : t < n + p) : ∀ (gs : List Gate) (W W' : List Bool),
    Inv n p t W W' → Inv n p t (gs.foldl stepF W) ((gs.map (remap n p t)).foldl stepF W')
  | [], _, _, h => h
  | g :: gs, W, W', h => by
    simp only [List.map_cons, List.foldl_cons]
    exact inv_fold n p t ht gs _ _ (inv_step n p t ht W W' h g)

theorem del_wires (C : Circuit) (n p t : ℕ) (hp : p < C.gates.length) (ht : t < n + p)
    (x : List Bool) (hx : x.length = n)
    (heq : (C.wires x).getD (n + p) false = (C.wires x).getD t false) :
    ∀ i, ((del C n p t).wires x).getD (rmap n p t i) false = (C.wires x).getD i false := by
  have hC : C.wires x = (C.gates.take p ++ C.gates.drop p).foldl stepF x := by
    rw [List.take_append_drop]; rfl
  rw [List.foldl_append, List.drop_eq_getElem_cons hp, List.foldl_cons] at hC
  have hC1 : (del C n p t).wires x
      = ((C.gates.drop (p + 1)).map (remap n p t)).foldl stepF
          ((C.gates.take p).foldl stepF x) := by
    rw [wires_def]
    show (C.gates.take p ++ (C.gates.drop (p + 1)).map (remap n p t)).foldl stepF x = _
    rw [List.foldl_append]
  set w0 := (C.gates.take p).foldl stepF x with hw0
  have hw0len : w0.length = n + p := by
    rw [hw0, foldl_length, hx, List.length_take]; omega
  have hinv0 : Inv n p t (stepF w0 C.gates[p]) w0 := by
    refine ⟨by simp [stepF], by simp [stepF]; omega, fun i => ?_⟩
    rcases lt_trichotomy i (n + p) with hi | hi | hi
    · have hr : rmap n p t i = i := by unfold rmap; split_ifs <;> omega
      rw [hr, stepF, List.getD_append _ _ _ _ (by omega)]
    · have hr : rmap n p t i = t := by unfold rmap; split_ifs <;> omega
      have hl : (stepF w0 C.gates[p]).length = n + p + 1 := by simp [stepF]; omega
      have e1 : (C.wires x).getD t false = (stepF w0 C.gates[p]).getD t false := by
        rw [hC]; exact getD_foldl_lt _ _ _ (by omega)
      have e2 : (C.wires x).getD (n + p) false = (stepF w0 C.gates[p]).getD (n + p) false := by
        rw [hC]; exact getD_foldl_lt _ _ _ (by omega)
      rw [hr, hi, ← e2, heq, e1, stepF, List.getD_append _ _ _ _ (by omega)]
    · have hr : rmap n p t i = i - 1 := by unfold rmap; split_ifs <;> omega
      rw [hr, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp [stepF]; omega)]
  have hf := inv_fold n p t ht (C.gates.drop (p + 1)) _ _ hinv0
  intro i
  rw [hC, hC1]
  exact hf.2.2 i

theorem del_fan (C : Circuit) (n p t : ℕ) (hF : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (del C n p t) := by
  intro g hg
  simp only [del] at hg
  rw [List.mem_append] at hg
  rcases hg with hg | hg
  · exact hF g (List.mem_of_mem_take hg)
  · rw [List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    obtain ⟨h1, h2⟩ := hF g' (List.mem_of_mem_drop hg')
    exact ⟨h1, by simpa [remap] using h2⟩

theorem del_size (C : Circuit) (n p t : ℕ) (hp : p < C.gates.length) :
    (del C n p t).gates.length = C.gates.length - 1 := by
  simp [del, List.length_take, List.length_drop]; omega

def Good (n : ℕ) (D : List Bool → Prop) (C : Circuit) (S : Finset ℕ) : Prop :=
  ∀ q ∈ S, q < C.gates.length ∧ ∃ t, t < n + q ∧
    ∀ x, D x → (C.wires x).getD (n + q) false = (C.wires x).getD t false

theorem main (n : ℕ) (D : List Bool → Prop) (hD : ∀ x, D x → x.length = n) (k : ℕ) :
    ∀ (C : Circuit) (S : Finset ℕ), S.card = k → Good n D C S →
      PEqualNP.MetaComplexity.FanInTwo C →
      ∃ C' : Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧ C'.size + k ≤ C.size ∧
        ∀ x, D x → C'.eval x = C.eval x := by
  induction k with
  | zero => exact fun C S _ _ hF => ⟨C, hF, by simp, fun _ _ => rfl⟩
  | succ k ih =>
    intro C S hS hG hF
    obtain ⟨p, hpS⟩ : S.Nonempty := by rw [← Finset.card_pos, hS]; omega
    obtain ⟨hp, t, ht, hteq⟩ := hG p hpS
    have key := fun x (hx : D x) => del_wires C n p t hp ht x (hD x hx) (hteq x hx)
    have hds := del_size C n p t hp
    let sh : ℕ → ℕ := fun q => if q < p then q else q - 1
    have hcard : ((S.erase p).image sh).card = k := by
      rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem hpS, hS]
      · simp
      · intro a ha b hb hab
        rw [Finset.mem_coe, Finset.mem_erase] at ha hb
        simp only [sh] at hab
        split_ifs at hab <;> omega
    have hgood : Good n D (del C n p t) ((S.erase p).image sh) := by
      intro q1 hq1
      rw [Finset.mem_image] at hq1
      obtain ⟨q, hq, rfl⟩ := hq1
      rw [Finset.mem_erase] at hq
      obtain ⟨hqp, hqS⟩ := hq
      obtain ⟨hq, tq, htq, hqeq⟩ := hG q hqS
      refine ⟨?_, rmap n p t tq, ?_, ?_⟩
      · rw [hds]; simp only [sh]; split_ifs <;> omega
      · simp only [sh, rmap]; split_ifs <;> omega
      · intro x hx
        have h1 := key x hx (n + q)
        have h2 := key x hx tq
        have hh : n + sh q = rmap n p t (n + q) := by simp only [sh, rmap]; split_ifs <;> omega
        rw [hh, h1, h2]
        exact hqeq x hx
    obtain ⟨C', hF', hsz, hev⟩ := ih (del C n p t) _ hcard hgood (del_fan C n p t hF)
    refine ⟨C', hF', ?_, ?_⟩
    · unfold Circuit.size at *; omega
    · intro x hx
      rw [hev x hx]
      exact key x hx C.output

end PEqualNP.Outside.L_meta_7774

theorem PEqualNP.Outside.L_meta_7774 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x4 : Finset (Fin x1.gates.length)), x4.card = (3 : ℕ) ∧ ∀ x5 ∈ x4, ∃ x7 < (10 : ℕ) + ↑x5, ∀ (x8 : Fin (10 : ℕ) → Bool), x8 x2 = Bool.false → (x1.wires (List.ofFn x8)).getD ((10 : ℕ) + ↑x5) Bool.false = (x1.wires (List.ofFn x8)).getD x7 Bool.false) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size + (3 : ℕ) ≤ x1.size ∧ ∀ (x6 : Fin (10 : ℕ) → Bool), x6 x2 = Bool.false → x5.eval (List.ofFn x6) = x1.eval (List.ofFn x6) := by
  intro x1 x2 hF hS
  obtain ⟨S, hS, hprop⟩ := hS
  obtain ⟨C', hF', hsz, hev⟩ := PEqualNP.Outside.L_meta_7774.main 10
    (fun x => ∃ y : Fin 10 → Bool, y x2 = false ∧ x = List.ofFn y)
    (by rintro x ⟨y, _, rfl⟩; simp) 3 x1 (S.map Fin.valEmbedding) (by simp [hS]) (by
      intro q hq
      rw [Finset.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      obtain ⟨t, ht, hteq⟩ := hprop q' hq'
      refine ⟨q'.isLt, t, ht, ?_⟩
      rintro x ⟨y, hy, rfl⟩
      exact hteq y hy) hF
  exact ⟨C', hF', hsz, fun x6 hx6 => hev _ ⟨x6, hx6, rfl⟩⟩
