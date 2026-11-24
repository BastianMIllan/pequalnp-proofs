import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2471

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK PEqualNP.MetaComplexity

def fl {α : Type} (F : List α → Gate → α) (init : List α) (gs : List Gate) : List α :=
  gs.foldl (fun R g => R ++ [F R g]) init

lemma fl_append {α : Type} (F : List α → Gate → α) (init : List α) (gs : List Gate) (g : Gate) :
    fl F init (gs ++ [g]) = fl F init gs ++ [F (fl F init gs) g] := by
  simp [fl, List.foldl_append]

lemma fl_len {α : Type} (F : List α → Gate → α) (init : List α) (gs : List Gate) :
    (fl F init gs).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [fl]
  | append_singleton gs g ih =>
    rw [fl_append, List.length_append, ih]
    simp
    omega

lemma fl_getD {α : Type} (F : List α → Gate → α) (init : List α) (gs : List Gate) (g : Gate)
    (t : ℕ) (d : α) :
    (fl F init (gs ++ [g])).getD t d =
      if t = init.length + gs.length then F (fl F init gs) g else (fl F init gs).getD t d := by
  rw [fl_append]
  have hl := fl_len F init gs
  split_ifs with h
  · rw [h, ← hl]
    simp [List.getD]
  · by_cases hlt : t < (fl F init gs).length
    · rw [List.getD_append _ _ _ _ hlt]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def FB (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def FV (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def iv (n k : ℕ) (S : List ℕ) : List (List (List ℕ)) := (List.range n).map (leafVectors S k)

lemma rv_eq (C : Circuit) (n k : ℕ) (S : List ℕ) :
    readVectors C n S k = fl (FV S k) (iv n k S) C.gates := by
  unfold readVectors fl iv
  congr 1

def WC {n : ℕ} (x : Fin n → Bool) (gs : List Gate) : List Bool := fl FB (List.ofFn x) gs

def VC (n k : ℕ) (S : List ℕ) (gs : List Gate) : List (List (List ℕ)) := fl (FV S k) (iv n k S) gs

lemma WC_snoc {n : ℕ} (x : Fin n → Bool) (gs : List Gate) (g : Gate) (t : ℕ) :
    (WC x (gs ++ [g])).getD t false =
      if t = n + gs.length then FB (WC x gs) g else (WC x gs).getD t false := by
  unfold WC
  rw [fl_getD, List.length_ofFn]

lemma VC_snoc (n k : ℕ) (S : List ℕ) (gs : List Gate) (g : Gate) (t : ℕ) :
    (VC n k S (gs ++ [g])).getD t [] =
      if t = n + gs.length then FV S k (VC n k S gs) g else (VC n k S gs).getD t [] := by
  unfold VC
  rw [fl_getD]
  simp [iv]

lemma mem_foldl_insertNew (L acc : List (List ℕ)) (v : List ℕ) :
    v ∈ L.foldl insertNew acc ↔ v ∈ acc ∨ v ∈ L := by
  induction L generalizing acc with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldl_cons, ih, insertNew, List.mem_cons]
    split_ifs with h
    · constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | rfl | h1)
        · exact Or.inl h1
        · exact Or.inl h
        · exact Or.inr h1
    · simp only [List.mem_append, List.mem_singleton]
      tauto

lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) :
    v ∈ andStep k A B ↔ ∃ u ∈ A, ∃ w ∈ B, capAdd k u w = v := by
  simp [andStep, mem_foldl_insertNew, List.mem_flatMap]

lemma andStep_nil_left (k : ℕ) (B : List (List ℕ)) : andStep k [] B = [] := by
  simp [andStep]

lemma andStep_nil_right (k : ℕ) (A : List (List ℕ)) : andStep k A [] = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro v hv
  obtain ⟨u, _, w, hw, _⟩ := (mem_andStep k A [] v).mp hv
  simp at hw

lemma mem_or2 (A B : List (List ℕ)) (v : List ℕ) :
    v ∈ B.foldl insertNew (A.foldl insertNew []) ↔ v ∈ A ∨ v ∈ B := by
  rw [mem_foldl_insertNew, mem_foldl_insertNew]
  simp

def Good (m k : ℕ) (v : List ℕ) : Prop := v.length = m ∧ ∀ i, v.getD i 0 ≤ k + 1

def LE (v' v : List ℕ) : Prop := ∀ i, v'.getD i 0 ≤ v.getD i 0

lemma LE_refl (v : List ℕ) : LE v v := fun _ => le_refl _

lemma LE_trans {a b c : List ℕ} (h1 : LE a b) (h2 : LE b c) : LE a c :=
  fun i => (h1 i).trans (h2 i)

lemma getD_capAdd {k : ℕ} {u w : List ℕ} (h : u.length = w.length) (i : ℕ) :
    (capAdd k u w).getD i 0 = min (u.getD i 0 + w.getD i 0) (k + 1) := by
  unfold capAdd
  by_cases hi : i < u.length
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_zipWith,
      List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega)]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega)]
    simp

lemma good_capAdd {m k : ℕ} {u w : List ℕ} (hu : Good m k u) (hw : Good m k w) :
    Good m k (capAdd k u w) := by
  refine ⟨by simp [capAdd, hu.1, hw.1], fun i => ?_⟩
  rw [getD_capAdd (hu.1.trans hw.1.symm)]
  exact min_le_right _ _

lemma LE_capAdd_right {m k : ℕ} {u w : List ℕ} (hu : Good m k u) (hw : Good m k w) :
    LE w (capAdd k u w) := by
  intro i
  rw [getD_capAdd (hu.1.trans hw.1.symm)]
  have := hw.2 i
  omega

lemma LE_capAdd_left {m k : ℕ} {u w : List ℕ} (hu : Good m k u) (hw : Good m k w) :
    LE u (capAdd k u w) := by
  intro i
  rw [getD_capAdd (hu.1.trans hw.1.symm)]
  have := hu.2 i
  omega

lemma capAdd_mono {m k : ℕ} {u' u w' w : List ℕ} (hu' : Good m k u') (hu : Good m k u)
    (hw' : Good m k w') (hw : Good m k w) (h1 : LE u' u) (h2 : LE w' w) :
    LE (capAdd k u' w') (capAdd k u w) := by
  intro i
  rw [getD_capAdd (hu'.1.trans hw'.1.symm), getD_capAdd (hu.1.trans hw.1.symm)]
  have := h1 i
  have := h2 i
  omega

lemma good_of_mem {m k : ℕ} {v : List ℕ} (hl : v.length = m) (h : ∀ a ∈ v, a ≤ k + 1) :
    Good m k v := by
  refine ⟨hl, fun i => ?_⟩
  by_cases hi : i < v.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    omega

lemma good_zero (k : ℕ) (S : List ℕ) : Good S.length k (S.map fun _ => 0) :=
  good_of_mem (by simp) (by intro a ha; simp at ha; omega)

lemma good_andStep {m k : ℕ} {A B : List (List ℕ)} (hA : ∀ v ∈ A, Good m k v)
    (hB : ∀ v ∈ B, Good m k v) : ∀ v ∈ andStep k A B, Good m k v := by
  intro v hv
  obtain ⟨u, hu, w, hw, rfl⟩ := (mem_andStep k A B v).mp hv
  exact good_capAdd (hA u hu) (hB w hw)

lemma or_fold_good {m k : ℕ} (ins : List (List (List ℕ))) (acc : List (List ℕ))
    (hacc : ∀ v ∈ acc, Good m k v) (hins : ∀ A ∈ ins, ∀ v ∈ A, Good m k v) :
    ∀ v ∈ ins.foldl (fun acc A => A.foldl insertNew acc) acc, Good m k v := by
  induction ins generalizing acc with
  | nil => simpa using hacc
  | cons A ins ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro v hv
      rw [mem_foldl_insertNew] at hv
      rcases hv with hv | hv
      · exact hacc v hv
      · exact hins A (by simp) v hv
    · intro B hB
      exact hins B (by simp [hB])

lemma and_fold_good {m k : ℕ} (ins : List (List (List ℕ))) (acc : List (List ℕ))
    (hacc : ∀ v ∈ acc, Good m k v) (hins : ∀ A ∈ ins, ∀ v ∈ A, Good m k v) :
    ∀ v ∈ ins.foldl (andStep k) acc, Good m k v := by
  induction ins generalizing acc with
  | nil => simpa using hacc
  | cons A ins ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact good_andStep hacc (hins A (by simp))
    · intro B hB
      exact hins B (by simp [hB])

def AllGood (m k : ℕ) (R : List (List (List ℕ))) : Prop := ∀ t, ∀ v ∈ R.getD t [], Good m k v

lemma allGood_snoc (k : ℕ) (S : List ℕ) (R : List (List (List ℕ))) (h : AllGood S.length k R)
    (g : Gate) : AllGood S.length k (R ++ [FV S k R g]) := by
  intro t v hv
  by_cases ht : t < R.length
  · rw [List.getD_append _ _ _ _ ht] at hv
    exact h t v hv
  · by_cases he : t = R.length
    · subst he
      rw [show (R ++ [FV S k R g]).getD R.length [] = FV S k R g by simp [List.getD]] at hv
      have hA : ∀ A ∈ g.inputs.map (fun i => R.getD i []), ∀ v ∈ A, Good S.length k v := by
        intro A hA v hv
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hA
        exact h i v hv
      unfold FV at hv
      split at hv
      · exact or_fold_good _ _ (by simp) hA v hv
      · exact and_fold_good _ _ (by simpa using good_zero k S) hA v hv
      · simp at hv
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hv
      simp at hv

lemma allGood_iv (n k : ℕ) (S : List ℕ) : AllGood S.length k (iv n k S) := by
  intro t v hv
  unfold iv at hv
  by_cases ht : t < n
  · rw [List.getD_eq_getElem _ _ (by simpa using ht)] at hv
    simp only [List.getElem_map, List.getElem_range, leafVectors] at hv
    split_ifs at hv with hS
    · rw [List.mem_singleton] at hv
      subst hv
      refine good_of_mem (by simp) ?_
      intro a ha
      simp only [List.mem_map] at ha
      obtain ⟨j, _, rfl⟩ := ha
      split_ifs <;> omega
    · simp at hv
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hv
    simp at hv

lemma allGood_VC (n k : ℕ) (S : List ℕ) (gs : List Gate) : AllGood S.length k (VC n k S gs) := by
  induction gs using List.reverseRecOn with
  | nil => exact allGood_iv n k S
  | append_singleton gs g ih =>
    unfold VC at ih ⊢
    rw [fl_append]
    exact allGood_snoc k S _ ih g

def RepF (n k : ℕ) (new : List Gate) (f : (Fin n → Bool) → Bool) (V : List ℕ → List (List ℕ)) :
    Prop :=
  ((∀ x, f x = false) ∧ ∀ S, V S = []) ∨ (∀ x, f x = true) ∨
  ∃ j, j < n + new.length ∧ (∀ x, (WC x new).getD j false = f x) ∧
    ∀ S v, v ∈ V S → ∃ v' ∈ (VC n k S new).getD j [], LE v' v

lemma repF_congr {n k : ℕ} {new : List Gate} {f1 f2 : (Fin n → Bool) → Bool}
    {V1 V2 : List ℕ → List (List ℕ)} (h : RepF n k new f1 V1) (hf : ∀ x, f1 x = f2 x)
    (hV0 : ∀ S, V1 S = [] → V2 S = []) (hV : ∀ S v, v ∈ V2 S → ∃ u ∈ V1 S, LE u v) :
    RepF n k new f2 V2 := by
  rcases h with ⟨h1, h2⟩ | h1 | ⟨j, hj, h1, h2⟩
  · exact Or.inl ⟨fun x => by rw [← hf x]; exact h1 x, fun S => hV0 S (h2 S)⟩
  · exact Or.inr (Or.inl fun x => by rw [← hf x]; exact h1 x)
  · refine Or.inr (Or.inr ⟨j, hj, fun x => (h1 x).trans (hf x), fun S v hv => ?_⟩)
    obtain ⟨u, hu, hle⟩ := hV S v hv
    obtain ⟨v', hv', hle'⟩ := h2 S u hu
    exact ⟨v', hv', LE_trans hle' hle⟩

lemma repF_eq {n k : ℕ} {new : List Gate} {f1 f2 : (Fin n → Bool) → Bool}
    {V1 V2 : List ℕ → List (List ℕ)} (h : RepF n k new f1 V1) (hf : ∀ x, f1 x = f2 x)
    (hV : ∀ S, V1 S = V2 S) : RepF n k new f2 V2 := by
  obtain rfl : f1 = f2 := funext hf
  obtain rfl : V1 = V2 := funext hV
  exact h

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (n : ℕ) (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h ∧ ∀ i ∈ h.inputs, i < n + new.length

lemma repF_mono {n k : ℕ} {new new' : List Gate} (he : Ext n new new')
    {f : (Fin n → Bool) → Bool} {V : List ℕ → List (List ℕ)} (h : RepF n k new f V) :
    RepF n k new' f V := by
  rcases he with rfl | ⟨g, rfl, _, _⟩
  · exact h
  · rcases h with h | h | ⟨j, hj, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ⟨j, by simp; omega, fun x => ?_, fun S v hv => ?_⟩)
      · rw [WC_snoc, if_neg (by omega)]
        exact h1 x
      · rw [VC_snoc, if_neg (by omega)]
        exact h2 S v hv

lemma good_VC {n k : ℕ} {S : List ℕ} {gs : List Gate} {j : ℕ} {v : List ℕ}
    (hv : v ∈ (VC n k S gs).getD j []) : Good S.length k v :=
  allGood_VC n k S gs j v hv

lemma rep_and2 {n k : ℕ} (new : List Gate) {fa fb : (Fin n → Bool) → Bool}
    {Va Vb : List ℕ → List (List ℕ)} (ha : RepF n k new fa Va) (hb : RepF n k new fb Vb)
    (hGa : ∀ S, ∀ v ∈ Va S, Good S.length k v) (hGb : ∀ S, ∀ v ∈ Vb S, Good S.length k v) :
    ∃ new', Ext n new new' ∧ RepF n k new' (fun x => fa x && fb x)
      (fun S => andStep k (andStep k [S.map fun _ => 0] (Va S)) (Vb S)) := by
  rcases ha with ⟨ha1, ha2⟩ | ha1 | ⟨j1, hj1, ha1, ha2⟩
  · exact ⟨new, Or.inl rfl, Or.inl ⟨fun x => by simp [ha1 x], fun S => by
      dsimp only
      rw [ha2 S, andStep_nil_right, andStep_nil_left]⟩⟩
  · refine ⟨new, Or.inl rfl, repF_congr hb (fun x => by simp [ha1 x]) (fun S h => by
      rw [h, andStep_nil_right]) (fun S v hv => ?_)⟩
    obtain ⟨t, ht, u, hu, rfl⟩ := (mem_andStep _ _ _ v).mp hv
    have hgt : Good S.length k t := good_andStep (by simpa using good_zero k S) (hGa S) t ht
    exact ⟨u, hu, LE_capAdd_right hgt (hGb S u hu)⟩
  · rcases hb with ⟨hb1, hb2⟩ | hb1 | ⟨j2, hj2, hb1, hb2⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨fun x => by simp [hb1 x], fun S => by
        dsimp only
        rw [hb2 S, andStep_nil_right]⟩⟩
    · refine ⟨new, Or.inl rfl, repF_congr (Or.inr (Or.inr ⟨j1, hj1, ha1, ha2⟩))
        (fun x => by simp [hb1 x]) (fun S h => by rw [h, andStep_nil_right, andStep_nil_left])
        (fun S v hv => ?_)⟩
      obtain ⟨t, ht, w, hw, rfl⟩ := (mem_andStep _ _ _ v).mp hv
      obtain ⟨z, hz, u, hu, rfl⟩ := (mem_andStep _ _ _ t).mp ht
      rw [List.mem_singleton] at hz
      subst hz
      have hgu := hGa S u hu
      have hgt := good_capAdd (good_zero k S) hgu
      exact ⟨u, hu, LE_trans (LE_capAdd_right (good_zero k S) hgu)
        (LE_capAdd_left hgt (hGb S w hw))⟩
    · refine ⟨new ++ [⟨GateOp.and, [j1, j2]⟩], Or.inr ⟨_, rfl, ⟨Or.inl rfl, rfl⟩, ?_⟩,
        Or.inr (Or.inr ⟨n + new.length, by simp, fun x => ?_, fun S v hv => ?_⟩)⟩
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> assumption
      · rw [WC_snoc, if_pos rfl]
        show GateOp.and.eval [(WC x new).getD j1 false, (WC x new).getD j2 false] = _
        rw [ha1 x, hb1 x]
        simp [GateOp.eval]
      · rw [VC_snoc, if_pos rfl]
        obtain ⟨t, ht, w, hw, rfl⟩ := (mem_andStep _ _ _ v).mp hv
        obtain ⟨z, hz, u, hu, rfl⟩ := (mem_andStep _ _ _ t).mp ht
        rw [List.mem_singleton] at hz
        subst hz
        obtain ⟨u', hu', hle1⟩ := ha2 S u hu
        obtain ⟨w', hw', hle2⟩ := hb2 S w hw
        have g0 := good_zero k S
        have gu := hGa S u hu
        have gw := hGb S w hw
        have gu' := good_VC hu'
        have gw' := good_VC hw'
        refine ⟨capAdd k (capAdd k (S.map fun _ => 0) u') w', ?_, ?_⟩
        · show _ ∈ andStep k (andStep k [S.map fun _ => 0] ((VC n k S new).getD j1 []))
            ((VC n k S new).getD j2 [])
          rw [mem_andStep]
          refine ⟨_, ?_, w', hw', rfl⟩
          rw [mem_andStep]
          exact ⟨_, List.mem_singleton_self _, u', hu', rfl⟩
        · exact capAdd_mono (good_capAdd g0 gu') (good_capAdd g0 gu) gw' gw
            (capAdd_mono g0 g0 gu' gu (LE_refl _) hle1) hle2

lemma rep_or2 {n k : ℕ} (new : List Gate) {fa fb : (Fin n → Bool) → Bool}
    {Va Vb : List ℕ → List (List ℕ)} (ha : RepF n k new fa Va) (hb : RepF n k new fb Vb) :
    ∃ new', Ext n new new' ∧ RepF n k new' (fun x => fa x || fb x)
      (fun S => (Vb S).foldl insertNew ((Va S).foldl insertNew [])) := by
  have hnil : ∀ A B : List (List ℕ), A = [] → B = [] →
      B.foldl insertNew (A.foldl insertNew []) = [] := by
    intro A B hA hB
    subst hA hB
    rfl
  rcases ha with ⟨ha1, ha2⟩ | ha1 | ⟨j1, hj1, ha1, ha2⟩
  · refine ⟨new, Or.inl rfl, repF_congr hb (fun x => by simp [ha1 x])
      (fun S h => hnil _ _ (ha2 S) h) (fun S v hv => ?_)⟩
    rcases (mem_or2 _ _ v).mp hv with h | h
    · rw [ha2 S] at h
      simp at h
    · exact ⟨v, h, LE_refl _⟩
  · exact ⟨new, Or.inl rfl, Or.inr (Or.inl fun x => by simp [ha1 x])⟩
  · rcases hb with ⟨hb1, hb2⟩ | hb1 | ⟨j2, hj2, hb1, hb2⟩
    · refine ⟨new, Or.inl rfl, repF_congr (Or.inr (Or.inr ⟨j1, hj1, ha1, ha2⟩))
        (fun x => by simp [hb1 x]) (fun S h => hnil _ _ h (hb2 S)) (fun S v hv => ?_)⟩
      rcases (mem_or2 _ _ v).mp hv with h | h
      · exact ⟨v, h, LE_refl _⟩
      · rw [hb2 S] at h
        simp at h
    · exact ⟨new, Or.inl rfl, Or.inr (Or.inl fun x => by simp [hb1 x])⟩
    · refine ⟨new ++ [⟨GateOp.or, [j1, j2]⟩], Or.inr ⟨_, rfl, ⟨Or.inr rfl, rfl⟩, ?_⟩,
        Or.inr (Or.inr ⟨n + new.length, by simp, fun x => ?_, fun S v hv => ?_⟩)⟩
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> assumption
      · rw [WC_snoc, if_pos rfl]
        show GateOp.or.eval [(WC x new).getD j1 false, (WC x new).getD j2 false] = _
        rw [ha1 x, hb1 x]
        simp [GateOp.eval]
      · rw [VC_snoc, if_pos rfl]
        show ∃ v' ∈ ((VC n k S new).getD j2 []).foldl insertNew
          (((VC n k S new).getD j1 []).foldl insertNew []), LE v' v
        rcases (mem_or2 _ _ v).mp hv with h | h
        · obtain ⟨v', hv', hle⟩ := ha2 S v h
          exact ⟨v', (mem_or2 _ _ v').mpr (Or.inl hv'), hle⟩
        · obtain ⟨v', hv', hle⟩ := hb2 S v h
          exact ⟨v', (mem_or2 _ _ v').mpr (Or.inr hv'), hle⟩

lemma gate_rep {n k : ℕ} (old new : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : ∀ t, RepF n k new (fun x => (WC x old).getD t false) (fun S => (VC n k S old).getD t [])) :
    ∃ new', Ext n new new' ∧
      RepF n k new' (fun x => FB (WC x old) g) (fun S => FV S k (VC n k S old) g) := by
  have hG : ∀ t S, ∀ v ∈ (VC n k S old).getD t [], Good S.length k v :=
    fun t S v hv => good_VC hv
  obtain ⟨op, l⟩ := g
  simp only at hop hlen
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inr (Or.inl fun x => by simp [FB, GateOp.eval])⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨fun x => by simp [FB, GateOp.eval], fun S => rfl⟩⟩
  · rcases hop with rfl | rfl
    · refine ⟨new, Or.inl rfl, repF_congr (h a) (fun x => by simp [FB, GateOp.eval])
        (fun S hA => ?_) (fun S v hv => ?_)⟩
      · show andStep k [S.map fun _ => 0] ((VC n k S old).getD a []) = []
        rw [hA, andStep_nil_right]
      · change v ∈ andStep k [S.map fun _ => 0] ((VC n k S old).getD a []) at hv
        obtain ⟨z, hz, u, hu, rfl⟩ := (mem_andStep _ _ _ v).mp hv
        rw [List.mem_singleton] at hz
        subst hz
        exact ⟨u, hu, LE_capAdd_right (good_zero k S) (hG a S u hu)⟩
    · refine ⟨new, Or.inl rfl, repF_congr (h a) (fun x => by simp [FB, GateOp.eval])
        (fun S hA => ?_) (fun S v hv => ?_)⟩
      · show ((VC n k S old).getD a []).foldl insertNew [] = []
        rw [hA]
        rfl
      · change v ∈ ((VC n k S old).getD a []).foldl insertNew [] at hv
        rw [mem_foldl_insertNew] at hv
        rcases hv with hv | hv
        · simp at hv
        · exact ⟨v, hv, LE_refl _⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and2 new (h a) (h b) (fun S => hG a S) (fun S => hG b S)
      exact ⟨new', he, repF_congr hr (fun x => by simp [FB, GateOp.eval])
        (fun S h0 => h0) (fun S v hv => ⟨v, hv, LE_refl _⟩)⟩
    · obtain ⟨new', he, hr⟩ := rep_or2 new (h a) (h b)
      exact ⟨new', he, repF_congr hr (fun x => by simp [FB, GateOp.eval])
        (fun S h0 => h0) (fun S v hv => ⟨v, hv, LE_refl _⟩)⟩
  · simp only [List.length_cons] at hlen
    omega

def RB (n : ℕ) (new : List Gate) : Prop :=
  ∀ j < new.length, ∀ i ∈ (new.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

lemma rb_snoc {n : ℕ} {new : List Gate} {h : Gate} (hrb : RB n new)
    (hh : ∀ i ∈ h.inputs, i < n + new.length) : RB n (new ++ [h]) := by
  intro j hj i hi
  rw [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < new.length
  · have e : (new ++ [h]).getD j ⟨GateOp.or, []⟩ = new.getD j ⟨GateOp.or, []⟩ := by
      simp [List.getD, List.getElem?_append_left hlt]
    rw [e] at hi
    exact hrb j hlt i hi
  · have hj' : j = new.length := by omega
    subst hj'
    have e : (new ++ [h]).getD new.length ⟨GateOp.or, []⟩ = h := by simp [List.getD]
    rw [e] at hi
    exact hh i hi

def Inv (n k : ℕ) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ RB n new ∧ new.length ≤ old.length ∧
    ∀ t, RepF n k new (fun x => (WC x old).getD t false) (fun S => (VC n k S old).getD t [])

lemma inv_step (n k : ℕ) (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : Inv n k old) : Inv n k (old ++ [g]) := by
  obtain ⟨new, hfan, hrb, hl, hrep⟩ := h
  obtain ⟨new', he, hr⟩ := gate_rep old new g hop hlen hrep
  refine ⟨new', ?_, ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨q, rfl, hq, _⟩
    · exact hfan
    · intro r hr'
      rcases List.mem_append.mp hr' with hr' | hr'
      · exact hfan r hr'
      · rw [List.mem_singleton] at hr'
        rw [hr']
        exact hq
  · rcases he with rfl | ⟨q, rfl, _, hqb⟩
    · exact hrb
    · exact rb_snoc hrb hqb
  · rcases he with rfl | ⟨q, rfl, _, _⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
      omega
  · intro t
    by_cases ht : t = n + old.length
    · exact repF_eq hr (fun x => by rw [WC_snoc, if_pos ht])
        (fun S => by rw [VC_snoc, if_pos ht])
    · exact repF_eq (repF_mono he (hrep t)) (fun x => by rw [WC_snoc, if_neg ht])
        (fun S => by rw [VC_snoc, if_neg ht])

lemma inv_base (n k : ℕ) : Inv n k [] := by
  refine ⟨[], by simp, (by intro j hj; simp at hj), le_refl _, fun t => ?_⟩
  by_cases ht : t < n
  · exact Or.inr (Or.inr ⟨t, by simpa using ht, fun x => rfl, fun S v hv => ⟨v, hv, LE_refl _⟩⟩)
  · refine Or.inl ⟨fun x => ?_, fun S => ?_⟩
    · show (List.ofFn x).getD t false = false
      exact List.getD_eq_default _ _ (by simp; omega)
    · show (iv n k S).getD t [] = []
      exact List.getD_eq_default _ _ (by simp [iv]; omega)

lemma inv_all (n k : ℕ) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Inv n k gates := by
  have hall : ∀ (post pre : List Gate), pre ++ post = gates → Inv n k pre → Inv n k gates := by
    intro post
    induction post with
    | nil =>
      intro pre h hinv
      rw [List.append_nil] at h
      rw [← h]
      exact hinv
    | cons g post ih =>
      intro pre h hinv
      have hmem : g ∈ gates := by
        rw [← h]
        simp
      exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
        (inv_step n k pre g (hg g hmem).1 (hg g hmem).2 hinv)
  exact hall gates [] (List.nil_append _) (inv_base n k)

theorem main : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.circuitFun n C (fun _ => false) = false → (∃ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = true) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ C'.size ≤ C.size ∧ PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.circuitFun n C ∧ ∀ (S : List ℕ) (v : List ℕ), v ∈ (PEqualNP.ReadK.readVectors C n S 2).getD C.output [] → ∃ v' ∈ (PEqualNP.ReadK.readVectors C' n S 2).getD C'.output [], ∀ i : ℕ, v'.getD i 0 ≤ v.getD i 0 := by
  intro n C hm h0 hx
  obtain ⟨x0, hx0⟩ := hx
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hgm
    have h := hm g hgm
    refine ⟨?_, h.2⟩
    have h1 := h.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact h1
  obtain ⟨new, hfan, hrb, hl, hrep⟩ := inv_all n 2 C.gates hg
  rcases hrep C.output with ⟨hf, _⟩ | hT | ⟨j, _, h1, h2⟩
  · have e : circuitFun n C x0 = false := hf x0
    rw [e] at hx0
    exact absurd hx0 (by simp)
  · have e : circuitFun n C (fun _ => false) = true := hT (fun _ => false)
    rw [e] at h0
    exact absurd h0 (by simp)
  · refine ⟨⟨new, j⟩, ⟨?_, ?_, ?_⟩, hl, ?_, ?_⟩
    · intro g hgm
      exact (hfan g hgm).1
    · intro j' hj' i hi
      exact hrb j' hj' i hi
    · intro g hgm
      exact (hfan g hgm).2
    · funext x
      exact h1 x
    · intro S v hv
      rw [rv_eq] at hv
      rw [rv_eq]
      exact h2 S v hv

end PEqualNP.Outside.L_meta_2471

theorem PEqualNP.Outside.L_meta_2471 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.circuitFun n C (fun _ => false) = false → (∃ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = true) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ C'.size ≤ C.size ∧ PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.circuitFun n C ∧ ∀ (S : List ℕ) (v : List ℕ), v ∈ (PEqualNP.ReadK.readVectors C n S 2).getD C.output [] → ∃ v' ∈ (PEqualNP.ReadK.readVectors C' n S 2).getD C'.output [], ∀ i : ℕ, v'.getD i 0 ≤ v.getD i 0 := by
  exact PEqualNP.Outside.L_meta_2471.main
