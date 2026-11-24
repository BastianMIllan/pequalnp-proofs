import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1696

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

lemma wiresFrom_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wiresFrom (gs ++ [g]) w =
      wiresFrom gs w ++ [g.op.eval (g.inputs.map fun i => (wiresFrom gs w).getD i false)] := by
  simp [wiresFrom, List.foldl_append]

lemma length_wiresFrom (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    have hstep : wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) := rfl
    rw [hstep, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_snoc (l : List Bool) (b : Bool) (j : ℕ) :
    (l ++ [b]).getD j false =
      if j < l.length then l.getD j false else if j = l.length then b else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    simp
  · rw [List.getD_eq_default]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def V {N : ℕ} (gs : List Gate) (j : ℕ) (x : Fin N → Bool) : Bool :=
  (wiresFrom gs (List.ofFn x)).getD j false

lemma V_snoc {N : ℕ} (gs : List Gate) (g : Gate) (j : ℕ) (x : Fin N → Bool) :
    V (gs ++ [g]) j x =
      if j < N + gs.length then V gs j x
      else if j = N + gs.length then g.op.eval (g.inputs.map fun i => V gs i x) else false := by
  simp only [V, wiresFrom_snoc, getD_snoc, length_wiresFrom, List.length_ofFn]

lemma V_big {N : ℕ} (gs : List Gate) (j : ℕ) (x : Fin N → Bool) (h : N + gs.length ≤ j) :
    V gs j x = false := by
  unfold V
  rw [List.getD_eq_default]
  rw [length_wiresFrom, List.length_ofFn]
  exact h

lemma V_snoc_ne {N : ℕ} (gs : List Gate) (g : Gate) {j : ℕ} (h : j ≠ N + gs.length)
    (x : Fin N → Bool) : V (gs ++ [g]) j x = V gs j x := by
  rw [V_snoc]
  by_cases h1 : j < N + gs.length
  · simp only [h1, ↓reduceIte]
  · simp only [h1, h, ↓reduceIte]
    exact (V_big gs j x (by omega)).symm

lemma V_and {N : ℕ} (gs : List Gate) (g : Gate) (a b : ℕ) (hab : g.inputs = [a, b])
    (hop : g.op = GateOp.and) (x : Fin N → Bool) :
    V (gs ++ [g]) (N + gs.length) x = (V gs a x && V gs b x) := by
  rw [V_snoc]
  simp [hab, hop, GateOp.eval]

lemma V_or {N : ℕ} (gs : List Gate) (g : Gate) (a b : ℕ) (hab : g.inputs = [a, b])
    (hop : g.op = GateOp.or) (x : Fin N → Bool) :
    V (gs ++ [g]) (N + gs.length) x = (V gs a x || V gs b x) := by
  rw [V_snoc]
  simp [hab, hop, GateOp.eval]

lemma ofFn_getD {N : ℕ} (z : Fin N → Bool) (j : ℕ) (hj : j < N) :
    (List.ofFn z).getD j false = z ⟨j, hj⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_ofFn]

lemma V_mono {N : ℕ} (gs : List Gate) (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (j : ℕ) (x y : Fin N → Bool) (hle : ∀ w, x w = true → y w = true) (h : V gs j x = true) :
    V gs j y = true := by
  refine wiresFrom_mono gs hmono (List.ofFn x) (List.ofFn y) (by simp) ?_ j h
  intro i hi
  by_cases hiN : i < N
  · rw [ofFn_getD x i hiN] at hi
    rw [ofFn_getD y i hiN]
    exact hle _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact Bool.noConfusion hi

def good {N : ℕ} (P : Finset (Fin N)) (gs : List Gate) (j : ℕ) : Prop :=
  1 < (Finset.univ.filter (fun l : Fin N => V gs (N + j) (fun m => decide (m = l)) = true)).card ∧
  ∀ l : Fin N, V gs (N + j) (fun m => decide (m = l)) = true → l ∈ P

noncomputable def G {N : ℕ} (P : Finset (Fin N)) (gs : List Gate) : Finset ℕ := by
  classical exact (Finset.range gs.length).filter (fun j => good P gs j)

lemma mem_G {N : ℕ} (P : Finset (Fin N)) (gs : List Gate) (j : ℕ) :
    j ∈ G P gs ↔ j < gs.length ∧ good P gs j := by
  classical
  simp [G]

lemma good_snoc {N : ℕ} (P : Finset (Fin N)) (gs : List Gate) (g : Gate) {j : ℕ}
    (hj : j < gs.length) : good P (gs ++ [g]) j ↔ good P gs j := by
  have hne : N + j ≠ N + gs.length := by omega
  unfold good
  simp only [V_snoc_ne gs g hne]

lemma G_sub {N : ℕ} (P : Finset (Fin N)) (gs : List Gate) (g : Gate) :
    G P gs ⊆ G P (gs ++ [g]) := by
  intro j hj
  rw [mem_G] at hj ⊢
  refine ⟨?_, (good_snoc P gs g hj.1).mpr hj.2⟩
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

lemma G_card_succ {N : ℕ} (P : Finset (Fin N)) (gs : List Gate) (g : Gate)
    (h : good P (gs ++ [g]) gs.length) : (G P gs).card + 1 ≤ (G P (gs ++ [g])).card := by
  have hnot : gs.length ∉ G P gs := by
    rw [mem_G]
    intro h'
    omega
  have hsub : insert gs.length (G P gs) ⊆ G P (gs ++ [g]) := by
    intro j hj
    rcases Finset.mem_insert.mp hj with hj | hj
    · rw [hj, mem_G]
      refine ⟨?_, h⟩
      simp
    · exact G_sub P gs g hj
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at h2
  exact h2

theorem key {N : ℕ} (P : Finset (Fin N)) : ∀ gs : List Gate,
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
    ∀ S : Finset ℕ, ∃ Z U : Finset (Fin N), (∀ z ∈ Z, z ∉ P) ∧
      (∀ u ∈ S, V gs u (fun m : Fin N => decide (m ∈ Z)) = false →
        ∀ l ∈ P, V gs u (fun m : Fin N => decide (m = l)) = true → l ∈ U) ∧
      Z.card + U.card ≤ S.card + (G P gs).card := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S
    refine ⟨∅, P.filter (fun l : Fin N => l.val ∈ S), by simp, ?_, ?_⟩
    · intro u hu _ l hl htrue
      rw [Finset.mem_filter]
      refine ⟨hl, ?_⟩
      by_cases huN : u < N
      · have hv : V ([] : List Gate) u (fun m : Fin N => decide (m = l))
            = decide ((⟨u, huN⟩ : Fin N) = l) := by
          unfold V wiresFrom
          simp only [List.foldl_nil]
          exact ofFn_getD _ u huN
        rw [hv] at htrue
        have h := of_decide_eq_true htrue
        rw [← h]
        exact hu
      · have hv : V ([] : List Gate) u (fun m : Fin N => decide (m = l)) = false :=
          V_big [] u _ (by simp only [List.length_nil]; omega)
        rw [hv] at htrue
        exact Bool.noConfusion htrue
    · have hcard : (P.filter (fun l : Fin N => l.val ∈ S)).card ≤ S.card :=
        Finset.card_le_card_of_injOn (fun l : Fin N => l.val)
          (by intro l hl; simp at hl ⊢; exact hl.2) (Fin.val_injective.injOn)
      simp only [Finset.card_empty, zero_add]
      omega
  | append_singleton gs g ih =>
    intro hg S
    have hgs : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2 :=
      fun g' h' => hg g' (List.mem_append_left _ h')
    have hgg := hg g (by simp)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hgg.2
    have ih' := ih hgs
    have hGsub : (G P gs).card ≤ (G P (gs ++ [g])).card := Finset.card_le_card (G_sub P gs g)
    by_cases hw : N + gs.length ∈ S
    · have hpos : 0 < S.card := Finset.card_pos.mpr ⟨_, hw⟩
      have herase := Finset.card_erase_of_mem hw
      by_cases hgood : good P (gs ++ [g]) gs.length
      · have hG1 := G_card_succ P gs g hgood
        obtain ⟨Z, U, hZ, hU, hc⟩ := ih' (insert a (insert b (S.erase (N + gs.length))))
        refine ⟨Z, U, hZ, ?_, ?_⟩
        · intro u hu hfalse l hl htrue
          by_cases hue : u = N + gs.length
          · subst hue
            rcases hgg.1 with hop | hop
            · rw [V_and gs g a b hab hop] at hfalse htrue
              have hta : V gs a (fun m : Fin N => decide (m = l)) = true ∧
                  V gs b (fun m : Fin N => decide (m = l)) = true := by
                simpa using htrue
              cases h1 : V gs a (fun m : Fin N => decide (m ∈ Z))
              · exact hU a (by simp) h1 l hl hta.1
              · rw [h1] at hfalse
                have h2 : V gs b (fun m : Fin N => decide (m ∈ Z)) = false := by
                  simpa using hfalse
                exact hU b (by simp) h2 l hl hta.2
            · rw [V_or gs g a b hab hop] at hfalse htrue
              have hfa : V gs a (fun m : Fin N => decide (m ∈ Z)) = false ∧
                  V gs b (fun m : Fin N => decide (m ∈ Z)) = false := by
                simpa using hfalse
              have hto : V gs a (fun m : Fin N => decide (m = l)) = true ∨
                  V gs b (fun m : Fin N => decide (m = l)) = true := by
                simpa using htrue
              rcases hto with h | h
              · exact hU a (by simp) hfa.1 l hl h
              · exact hU b (by simp) hfa.2 l hl h
          · rw [V_snoc_ne gs g hue] at hfalse htrue
            exact hU u (by simp [hue, hu]) hfalse l hl htrue
        · have h1 := Finset.card_insert_le a (insert b (S.erase (N + gs.length)))
          have h2 := Finset.card_insert_le b (S.erase (N + gs.length))
          omega
      · obtain ⟨Z, U, hZ, hU, hc⟩ := ih' (S.erase (N + gs.length))
        unfold good at hgood
        rw [not_and_or] at hgood
        rcases hgood with h1 | h2
        · refine ⟨Z, U ∪ (Finset.univ.filter (fun l : Fin N =>
              V (gs ++ [g]) (N + gs.length) (fun m => decide (m = l)) = true)), hZ, ?_, ?_⟩
          · intro u hu hfalse l hl htrue
            by_cases hue : u = N + gs.length
            · subst hue
              exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htrue⟩)
            · rw [V_snoc_ne gs g hue] at hfalse htrue
              exact Finset.mem_union_left _ (hU u (by simp [hue, hu]) hfalse l hl htrue)
          · have h3 := Finset.card_union_le U (Finset.univ.filter (fun l : Fin N =>
              V (gs ++ [g]) (N + gs.length) (fun m => decide (m = l)) = true))
            omega
        · obtain ⟨z, hz⟩ := not_forall.mp h2
          obtain ⟨hz1, hz2⟩ := not_imp.mp hz
          refine ⟨insert z Z, U, ?_, ?_, ?_⟩
          · intro z' hz'
            rcases Finset.mem_insert.mp hz' with h | h
            · rw [h]; exact hz2
            · exact hZ _ h
          · intro u hu hfalse l hl htrue
            by_cases hue : u = N + gs.length
            · subst hue
              exfalso
              have ht := V_mono (gs ++ [g]) (fun g' h' => (hg g' h').1) (N + gs.length)
                (fun m : Fin N => decide (m = z)) (fun m : Fin N => decide (m ∈ insert z Z))
                (by
                  intro m hm
                  have hm' := of_decide_eq_true hm
                  exact decide_eq_true (Finset.mem_insert.mpr (Or.inl hm'))) hz1
              rw [ht] at hfalse
              exact Bool.noConfusion hfalse
            · rw [V_snoc_ne gs g hue] at hfalse htrue
              refine hU u (by simp [hue, hu]) ?_ l hl htrue
              cases hcase : V gs u (fun m : Fin N => decide (m ∈ Z))
              · rfl
              · exfalso
                have ht := V_mono gs (fun g' h' => (hgs g' h').1) u
                  (fun m : Fin N => decide (m ∈ Z)) (fun m : Fin N => decide (m ∈ insert z Z))
                  (by
                    intro m hm
                    have hm' := of_decide_eq_true hm
                    exact decide_eq_true (Finset.mem_insert.mpr (Or.inr hm'))) hcase
                rw [ht] at hfalse
                exact Bool.noConfusion hfalse
          · have h3 := Finset.card_insert_le z Z
            omega
    · obtain ⟨Z, U, hZ, hU, hc⟩ := ih' S
      refine ⟨Z, U, hZ, ?_, by omega⟩
      intro u hu hfalse l hl htrue
      have hue : u ≠ N + gs.length := fun h => hw (h ▸ hu)
      rw [V_snoc_ne gs g hue] at hfalse htrue
      exact hU u hu hfalse l hl htrue

theorem main (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (c : Fin N → ℕ)
    (hdeg : ∀ p : Fin N, (Finset.univ.filter (fun l : Fin N => I p l)).card = q + 1)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hinc : ∀ p l : Fin N, V C.gates (c p) (fun m : Fin N => decide (m = l)) = true ↔ I p l)
    (hsound : ∀ (p : Fin N) (y : Fin N → Bool),
      (Finset.univ.filter (fun m : Fin N => y m = true)).card ≤ q →
      (∀ l : Fin N, I p l → y l = false) → V C.gates (c p) y = false) :
    N * q ≤ C.size := by
  have hq : ∀ p : Fin N, q ≤ (G (Finset.univ.filter (fun l : Fin N => I p l)) C.gates).card := by
    intro p
    obtain ⟨Z, U, hZ, hU, hc⟩ :=
      key (Finset.univ.filter (fun l : Fin N => I p l)) C.gates hgates {c p}
    rw [Finset.card_singleton] at hc
    cases hv : V C.gates (c p) (fun m : Fin N => decide (m ∈ Z))
    · have hsub : Finset.univ.filter (fun l : Fin N => I p l) ⊆ U := by
        intro l hl
        refine hU (c p) (Finset.mem_singleton_self _) hv l hl ((hinc p l).mpr ?_)
        exact (Finset.mem_filter.mp hl).2
      have h1 := Finset.card_le_card hsub
      have h2 := hdeg p
      omega
    · have hnot : ¬ Z.card ≤ q := by
        intro hle
        have hfil : (Finset.univ.filter (fun m : Fin N => decide (m ∈ Z) = true)) = Z := by
          ext m
          simp
        have h3 := hsound p (fun m : Fin N => decide (m ∈ Z)) (by rw [hfil]; exact hle) (by
          intro l hl
          apply decide_eq_false
          intro hz
          exact hZ l hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩))
        rw [h3] at hv
        exact Bool.noConfusion hv
      omega
  have hdisj : ∀ p p' : Fin N, p ≠ p' →
      Disjoint (G (Finset.univ.filter (fun l : Fin N => I p l)) C.gates)
        (G (Finset.univ.filter (fun l : Fin N => I p' l)) C.gates) := by
    intro p p' hne
    rw [Finset.disjoint_left]
    intro j hj hj'
    rw [mem_G] at hj hj'
    obtain ⟨l1, hl1, l2, hl2, hl12⟩ := Finset.one_lt_card.mp hj.2.1
    have hl1' := (Finset.mem_filter.mp hl1).2
    have hl2' := (Finset.mem_filter.mp hl2).2
    have a1 := (Finset.mem_filter.mp (hj.2.2 l1 hl1')).2
    have a2 := (Finset.mem_filter.mp (hj.2.2 l2 hl2')).2
    have b1 := (Finset.mem_filter.mp (hj'.2.2 l1 hl1')).2
    have b2 := (Finset.mem_filter.mp (hj'.2.2 l2 hl2')).2
    obtain ⟨l, _, hl⟩ := huniq p p' hne
    exact hl12 ((hl l1 ⟨a1, b1⟩).trans (hl l2 ⟨a2, b2⟩).symm)
  have hunion : (Finset.univ.biUnion
      (fun p : Fin N => G (Finset.univ.filter (fun l : Fin N => I p l)) C.gates)).card
      = ∑ p : Fin N, (G (Finset.univ.filter (fun l : Fin N => I p l)) C.gates).card :=
    Finset.card_biUnion (fun p _ p' _ h => hdisj p p' h)
  have hsubset : Finset.univ.biUnion
      (fun p : Fin N => G (Finset.univ.filter (fun l : Fin N => I p l)) C.gates)
      ⊆ Finset.range C.gates.length := by
    intro j hj
    rw [Finset.mem_biUnion] at hj
    obtain ⟨p, _, hp⟩ := hj
    exact Finset.mem_range.mpr ((mem_G _ _ _).mp hp).1
  have h1 := Finset.card_le_card hsubset
  rw [hunion, Finset.card_range] at h1
  have h2 : N * q ≤
      ∑ p : Fin N, (G (Finset.univ.filter (fun l : Fin N => I p l)) C.gates).card := by
    calc N * q = ∑ _p : Fin N, q := by simp
      _ ≤ _ := Finset.sum_le_sum (fun p _ => hq p)
  exact le_trans h2 h1

end PEqualNP.Outside.L_meta_1696

theorem PEqualNP.Outside.L_meta_1696 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (c : Fin N → ℕ), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ p : Fin N, (Finset.univ.filter (fun l : Fin N => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ p l : Fin N, (C.wires (List.ofFn (fun m : Fin N => decide (m = l)))).getD (c p) false = true ↔ I p l) → (∀ (p : Fin N) (y : Fin N → Bool), (Finset.univ.filter (fun m : Fin N => y m = true)).card ≤ q → (∀ l : Fin N, I p l → y l = false) → (C.wires (List.ofFn y)).getD (c p) false = false) → N * q ≤ C.size := by
  intro q N I _ C c _ _ hdeg huniq hgates hinc hsound
  exact PEqualNP.Outside.L_meta_1696.main q N I C c hdeg huniq hgates hinc hsound
