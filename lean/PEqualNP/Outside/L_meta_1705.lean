import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1705

def pand (K : ℕ) : List ℕ → ℕ
  | [] => 2 ^ K - 1
  | a :: l => a &&& pand K l

def por : List ℕ → ℕ
  | [] => 0
  | a :: l => a ||| por l

def pop (K : ℕ) : GateOp → List ℕ → ℕ
  | GateOp.and, l => pand K l
  | GateOp.or, l => por l
  | _, _ => 0

def isAO : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

def pval (K : ℕ) (W : List ℕ) (g : Gate) : ℕ :=
  pop K g.op (g.inputs.map fun i => W.getD i 0)

def pstep (K : ℕ) (W : List ℕ) (g : Gate) : List ℕ :=
  W ++ [pval K W g]

def run (K : ℕ) : List Gate → List ℕ → List ℕ
  | [], W => W
  | g :: gs, W =>
    bif Nat.beq (pval K W g) 0 then run K gs (pstep K W g) else run K gs (pstep K W g)

lemma run_eq (K : ℕ) (gs : List Gate) (W : List ℕ) : run K gs W = gs.foldl (pstep K) W := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    simp only [run, Bool.cond_self, List.foldl_cons]
    exact ih _

def bstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def bits : List ℕ → ℕ
  | [] => 0
  | p :: l => (1 <<< p) ||| bits l

def pinL (i : ℕ) : List ℕ := (List.range 43).flatMap (fun c => [i * 43 + c, c * 43 + i])

def W0 : List ℕ := (List.range 42).map (fun i => bits (pinL i))

def expL (incL : List (ℕ × ℕ)) : List ℕ := incL.flatMap (fun e => [e.1 * 43 + (21 + e.2), (21 + e.2) * 43 + e.1])

lemma pand_tb (K k : ℕ) (hk : k < K) (ms : List ℕ) :
    (pand K ms).testBit k = (ms.map (fun m => m.testBit k)).all id := by
  induction ms with
  | nil => simp [pand, Nat.testBit_two_pow_sub_one, hk]
  | cons a l ih => simp [pand, Nat.testBit_and, ih]

lemma por_tb (k : ℕ) (ms : List ℕ) :
    (por ms).testBit k = (ms.map (fun m => m.testBit k)).any id := by
  induction ms with
  | nil => simp [por]
  | cons a l ih => simp [por, Nat.testBit_or, ih]

lemma getD_map_tb (W : List ℕ) (k i : ℕ) :
    (W.map (fun m => m.testBit k)).getD i false = (W.getD i 0).testBit k := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> simp

lemma step_tb (K k : ℕ) (hk : k < K) (W : List ℕ) (g : Gate) (hg : isAO g.op = true) :
    bstep (W.map (fun m => m.testBit k)) g = (pstep K W g).map (fun m => m.testBit k) := by
  unfold bstep pstep pval
  rw [List.map_append]
  have e : (g.inputs.map fun i => (W.map (fun m => m.testBit k)).getD i false) =
      ((g.inputs.map fun i => W.getD i 0).map (fun m => m.testBit k)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact getD_map_tb W k i
  rw [e]
  generalize g.inputs.map (fun i => W.getD i 0) = ms
  have key : g.op.eval (ms.map (fun m => m.testBit k)) = (pop K g.op ms).testBit k := by
    cases hop : g.op with
    | and => simp [GateOp.eval, pop, pand_tb K k hk]
    | or => simp [GateOp.eval, pop, por_tb]
    | not => rw [hop] at hg; simp [isAO] at hg
    | mod m => rw [hop] at hg; simp [isAO] at hg
    | maj => rw [hop] at hg; simp [isAO] at hg
  rw [key]
  rfl

lemma fold_tb (K k : ℕ) (hk : k < K) (gs : List Gate) (hgs : ∀ g ∈ gs, isAO g.op = true)
    (W : List ℕ) :
    gs.foldl bstep (W.map (fun m => m.testBit k)) =
      (gs.foldl (pstep K) W).map (fun m => m.testBit k) := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [step_tb K k hk W g (hgs g (by simp))]
    exact ih (fun g' hg' => hgs g' (by simp [hg'])) _

lemma eval_tb (K k : ℕ) (hk : k < K) (C : Circuit) (hC : ∀ g ∈ C.gates, isAO g.op = true)
    (W : List ℕ) :
    C.eval (W.map (fun m => m.testBit k)) =
      ((C.gates.foldl (pstep K) W).getD C.output 0).testBit k := by
  have h := fold_tb K k hk C.gates hC W
  show (C.gates.foldl bstep (W.map (fun m => m.testBit k))).getD C.output false = _
  rw [h, getD_map_tb]

lemma bits_tb (l : List ℕ) (k : ℕ) : (bits l).testBit k = decide (k ∈ l) := by
  induction l with
  | nil => simp [bits]
  | cons p l ih =>
    simp only [bits, Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow, List.mem_cons]
    by_cases h : p = k
    · subst h; simp
    · have h' : ¬ k = p := fun e => h e.symm
      simp [h, h']

lemma pin_tb (i a b : ℕ) (hi : i < 42) (ha : a ≤ 42) (hb : b ≤ 42) :
    (bits (pinL i)).testBit (a * 43 + b) = decide (i = a ∨ i = b) := by
  rw [bits_tb]
  apply decide_eq_decide.mpr
  unfold pinL
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨c, hc, h | h⟩ <;> omega
  · rintro (h | h)
    · exact ⟨b, by omega, Or.inl (by rw [h])⟩
    · exact ⟨a, by omega, Or.inr (by rw [h])⟩

lemma W0_tb (a b : ℕ) (ha : a ≤ 42) (hb : b ≤ 42) :
    W0.map (fun m => m.testBit (a * 43 + b)) =
      (List.range 42).map (fun i => decide (i = a ∨ i = b)) := by
  unfold W0
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  exact pin_tb i a b (List.mem_range.mp hi) ha hb

lemma supp2 (S : Finset ℕ) (hS : S.card ≤ 2) (hlt : ∀ i ∈ S, i < 42) :
    ∃ a b : ℕ, a ≤ 42 ∧ b ≤ 42 ∧ ∀ i, i < 42 → (i ∈ S ↔ (i = a ∨ i = b)) := by
  have h3 : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases h3 with h | h | h
  · rw [Finset.card_eq_zero] at h
    subst h
    refine ⟨42, 42, le_refl _, le_refl _, fun i hi => ?_⟩
    simp only [Finset.notMem_empty, false_iff]
    omega
  · rw [Finset.card_eq_one] at h
    obtain ⟨a, rfl⟩ := h
    have := hlt a (by simp)
    exact ⟨a, a, by omega, by omega, fun i _ => by simp⟩
  · rw [Finset.card_eq_two] at h
    obtain ⟨a, b, _, rfl⟩ := h
    have h1 := hlt a (by simp)
    have h2 := hlt b (by simp)
    exact ⟨a, b, by omega, by omega, fun i _ => by simp⟩

lemma xy_ab (x y : Fin 21 → Bool)
    (h : (Finset.univ.filter (fun p : Fin 21 => x p = true)).card +
      (Finset.univ.filter (fun l : Fin 21 => y l = true)).card ≤ 2) :
    ∃ a b : ℕ, a ≤ 42 ∧ b ≤ 42 ∧
      (∀ p : Fin 21, x p = decide ((p : ℕ) = a ∨ (p : ℕ) = b)) ∧
      (∀ l : Fin 21, y l = decide (21 + (l : ℕ) = a ∨ 21 + (l : ℕ) = b)) := by
  obtain ⟨S, hSdef⟩ : ∃ S : Finset ℕ, S =
      (Finset.univ.filter (fun p : Fin 21 => x p = true)).image (fun p : Fin 21 => (p : ℕ)) ∪
      (Finset.univ.filter (fun l : Fin 21 => y l = true)).image (fun l : Fin 21 => 21 + (l : ℕ)) :=
    ⟨_, rfl⟩
  have hS : S.card ≤ 2 := by
    rw [hSdef]
    exact le_trans (Finset.card_union_le _ _)
      (le_trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le) h)
  have hmem : ∀ i : ℕ, i ∈ S ↔ ((∃ p : Fin 21, x p = true ∧ (p : ℕ) = i) ∨
      (∃ l : Fin 21, y l = true ∧ 21 + (l : ℕ) = i)) := by
    intro i
    rw [hSdef]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  have hlt : ∀ i ∈ S, i < 42 := by
    intro i hi
    rcases (hmem i).mp hi with ⟨p, _, e⟩ | ⟨l, _, e⟩
    · have := p.isLt
      omega
    · have := l.isLt
      omega
  obtain ⟨a, b, ha, hb, hab⟩ := supp2 S hS hlt
  refine ⟨a, b, ha, hb, fun p => ?_, fun l => ?_⟩
  · have hpl := p.isLt
    have hp := hab p.val (by omega)
    have e : (p : ℕ) ∈ S ↔ x p = true := by
      rw [hmem]
      constructor
      · rintro (⟨p', hp', e⟩ | ⟨l, _, e⟩)
        · have : p' = p := Fin.ext e
          rw [← this]
          exact hp'
        · omega
      · intro hx
        exact Or.inl ⟨p, hx, rfl⟩
    rw [Bool.eq_iff_iff, decide_eq_true_eq, ← e]
    exact hp
  · have hll := l.isLt
    have hp := hab (21 + l.val) (by omega)
    have e : 21 + (l : ℕ) ∈ S ↔ y l = true := by
      rw [hmem]
      constructor
      · rintro (⟨p, _, e⟩ | ⟨l', hl', e⟩)
        · have := p.isLt
          omega
        · have : l' = l := Fin.ext (by omega)
          rw [← this]
          exact hl'
      · intro hy
        exact Or.inr ⟨l, hy, rfl⟩
    rw [Bool.eq_iff_iff, decide_eq_true_eq, ← e]
    exact hp

lemma inp_eq (x y : Fin 21 → Bool) (a b : ℕ)
    (hx : ∀ p : Fin 21, x p = decide ((p : ℕ) = a ∨ (p : ℕ) = b))
    (hy : ∀ l : Fin 21, y l = decide (21 + (l : ℕ) = a ∨ 21 + (l : ℕ) = b)) :
    List.ofFn x ++ List.ofFn y = (List.range 42).map (fun i => decide (i = a ∨ i = b)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    by_cases hi : i < 21
    · rw [List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, hx]
    · have hi2 : i < 42 := by simpa using h2
      rw [List.getElem_append_right (by simpa using hi)]
      simp only [List.getElem_ofFn, List.length_ofFn, List.getElem_map, List.getElem_range, hy]
      have e : 21 + (i - 21) = i := by omega
      rw [e]

lemma rhs_eq (incL : List (ℕ × ℕ)) (hinc : ∀ e ∈ incL, e.1 < 21 ∧ e.2 < 21) (x y : Fin 21 → Bool) (a b : ℕ)
    (ha : a ≤ 42) (hb : b ≤ 42)
    (hx : ∀ p : Fin 21, x p = decide ((p : ℕ) = a ∨ (p : ℕ) = b))
    (hy : ∀ l : Fin 21, y l = decide (21 + (l : ℕ) = a ∨ 21 + (l : ℕ) = b)) :
    decide (∃ p : Fin 21, ∃ l : Fin 21, ((p : ℕ), (l : ℕ)) ∈ incL ∧ x p = true ∧ y l = true) =
      (bits (expL incL)).testBit (a * 43 + b) := by
  rw [bits_tb]
  apply decide_eq_decide.mpr
  unfold expL
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨p, l, hm, hxp, hyl⟩
    rw [hx] at hxp
    rw [hy] at hyl
    simp only [decide_eq_true_eq] at hxp hyl
    refine ⟨((p : ℕ), (l : ℕ)), hm, ?_⟩
    have := p.isLt
    have := l.isLt
    show a * 43 + b = (p : ℕ) * 43 + (21 + (l : ℕ)) ∨ a * 43 + b = (21 + (l : ℕ)) * 43 + (p : ℕ)
    omega
  · rintro ⟨e, hm, he⟩
    obtain ⟨h1, h2⟩ := hinc e hm
    refine ⟨⟨e.1, h1⟩, ⟨e.2, h2⟩, hm, ?_, ?_⟩
    · rw [hx]
      simp only [decide_eq_true_eq]
      show e.1 = a ∨ e.1 = b
      omega
    · rw [hy]
      simp only [decide_eq_true_eq]
      show 21 + e.2 = a ∨ 21 + e.2 = b
      omega

lemma main3 (C : Circuit) (incL : List (ℕ × ℕ))
    (hAO : ∀ g ∈ C.gates, isAO g.op = true)
    (hinc : ∀ e ∈ incL, e.1 < 21 ∧ e.2 < 21)
    (hout : (run 1849 C.gates W0).getD C.output 0 = bits (expL incL))
    (x y : Fin 21 → Bool)
    (h : (Finset.univ.filter (fun p : Fin 21 => x p = true)).card +
      (Finset.univ.filter (fun l : Fin 21 => y l = true)).card ≤ 2) :
    C.eval (List.ofFn x ++ List.ofFn y) =
      decide (∃ p : Fin 21, ∃ l : Fin 21, ((p : ℕ), (l : ℕ)) ∈ incL ∧ x p = true ∧ y l = true) := by
  obtain ⟨a, b, ha, hb, hx, hy⟩ := xy_ab x y h
  have hk : a * 43 + b < 1849 := by omega
  rw [inp_eq x y a b hx hy, ← W0_tb a b ha hb, eval_tb 1849 (a * 43 + b) hk C hAO W0, ← run_eq,
    hout, rhs_eq incL hinc x y a b ha hb hx hy]

end PEqualNP.Outside.L_meta_1705

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_1705 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [46, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [51, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [52, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [54, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [55, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [57, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [58, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [61, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [63, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [65, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [66, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [69, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [70, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [72, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [73, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [75, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [76, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [78, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [79, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [80, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [82, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [84, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [85, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [87, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [88, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [91, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [93, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [37, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [96, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [97, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [99, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [100, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [101, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [102, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [103, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [104, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [105, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [106, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [107, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [109, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [110, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [111, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [112, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [114, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [115, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [116, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [25, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [119, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [120, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [121, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [122, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [125, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [126, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [128, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [129, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [131, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [132, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [133, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [22, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [135, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [136, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [137, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [138, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [140, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [141, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [142, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [144, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [145, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [146, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 113] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [45, 149] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [60, 149] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [64, 149] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [71, 149] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [74, 149] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [77, 149] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [81, 149] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [86, 149] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [90, 149] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [94, 149] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [98, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [113, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [117, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [124, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [127, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [130, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [134, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [139, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [143, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [147, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [150, 151] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [152, 154] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 155] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [152, 153] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [154, 155] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [156, 158] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [157, 159] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [156, 157] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 159] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [160, 161] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [162, 164] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 165] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [162, 163] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [164, 165] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [166, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [167, 169] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [166, 167] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [168, 169] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [150, 160] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [151, 161] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [150, 179] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [170, 160] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [190, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [170, 179] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [188, 193] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [189, 193] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [192, 193] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [171, 180] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [172, 181] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [194, 197] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [195, 198] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [199, 200] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [194, 198] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [195, 197] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [202, 203] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [171, 182] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [172, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [196, 205] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [196, 206] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [173, 180] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [174, 181] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [207, 209] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [208, 210] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [211, 212] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [207, 210] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [208, 209] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [214, 215] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [173, 182] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [174, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [201, 217] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [204, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [219, 220] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [201, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [204, 217] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [222, 223] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [213, 217] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [216, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [225, 226] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [213, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [216, 217] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [228, 229] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [175, 184] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [176, 185] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [221, 231] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [224, 232] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [233, 234] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [221, 232] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [224, 231] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [236, 237] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [175, 186] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [176, 187] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [227, 239] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [230, 240] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [241, 242] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [227, 240] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [230, 239] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [244, 245] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [177, 184] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [178, 185] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [243, 247] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [246, 248] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [249, 250] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [243, 248] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [246, 247] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [252, 253] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [177, 186] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [178, 187] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [235, 255] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [238, 256] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [257, 258] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [235, 256] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [238, 255] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [260, 261] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [251, 255] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [254, 256] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [263, 264] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [251, 256] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [254, 255] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [266, 267] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [259, 265] }], output := 269 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 228 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (21 + 21) C ∧
  ∀ (x y : Fin 21 → Bool), (Finset.univ.filter (fun p : Fin 21 => x p = true)).card + (Finset.univ.filter (fun l : Fin 21 => y l = true)).card ≤ 2 →
    C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 21, ∃ l : Fin 21, ((p : ℕ), (l : ℕ)) ∈ ([(16, 0), (17, 0), (18, 0), (19, 0), (20, 0), (1, 1), (5, 1), (9, 1), (13, 1), (16, 1), (3, 2), (7, 2), (11, 2), (15, 2), (16, 2), (2, 3), (6, 3), (10, 3), (14, 3), (16, 3), (4, 4), (5, 4), (6, 4), (7, 4), (20, 4), (1, 5), (4, 5), (11, 5), (14, 5), (17, 5), (3, 6), (4, 6), (10, 6), (13, 6), (19, 6), (2, 7), (4, 7), (9, 7), (15, 7), (18, 7), (12, 8), (13, 8), (14, 8), (15, 8), (20, 8), (1, 9), (7, 9), (10, 9), (12, 9), (18, 9), (3, 10), (6, 10), (9, 10), (12, 10), (17, 10), (2, 11), (5, 11), (11, 11), (12, 11), (19, 11), (8, 12), (9, 12), (10, 12), (11, 12), (20, 12), (1, 13), (6, 13), (8, 13), (15, 13), (19, 13), (3, 14), (5, 14), (8, 14), (14, 14), (18, 14), (2, 15), (7, 15), (8, 15), (13, 15), (17, 15), (0, 16), (1, 16), (2, 16), (3, 16), (20, 16), (0, 17), (5, 17), (10, 17), (15, 17), (17, 17), (0, 18), (7, 18), (9, 18), (14, 18), (19, 18), (0, 19), (6, 19), (11, 19), (13, 19), (18, 19), (0, 20), (4, 20), (8, 20), (12, 20), (16, 20)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) := by
  intro C hC
  subst hC
  refine ⟨by decide +kernel, by decide +kernel, fun x y h => ?_⟩
  exact PEqualNP.Outside.L_meta_1705.main3 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) x y h
