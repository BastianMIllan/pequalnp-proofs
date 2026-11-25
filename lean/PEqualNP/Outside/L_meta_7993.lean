import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7993
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem take_eq (A B : List Gate) (L : ℕ) (h : ∀ i < L, A[i]? = B[i]?) :
    A.take L = B.take L := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_take]
  split_ifs with hi
  · exact h i hi
  · rfl

theorem erase_len (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (PEqualNP.CircuitMoves.eraseGate n C m p).gates.length = C.gates.length - 1 := by
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [if_pos hm]
  simp
  omega

theorem erase_out (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (PEqualNP.CircuitMoves.eraseGate n C m p).output
      = PEqualNP.CircuitMoves.eraseRedirect n m p C.output := by
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [if_pos hm]

theorem erase_lo (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) {i : ℕ}
    (hi : i < m) :
    (PEqualNP.CircuitMoves.eraseGate n C m p).gates[i]? = C.gates[i]? := by
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [if_pos hm]
  dsimp only
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take, if_pos hi]

theorem erase_hi (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) {q : ℕ}
    (hq : m ≤ q) :
    (PEqualNP.CircuitMoves.eraseGate n C m p).gates[q]?
      = (C.gates[q + 1]?).map
          (fun g => (⟨g.op, g.inputs.map (PEqualNP.CircuitMoves.eraseRedirect n m p)⟩ : Gate)) := by
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [if_pos hm]
  dsimp only
  have hlt : (C.gates.take m).length = m := by simp; omega
  rw [List.getElem?_append_right (by omega), hlt, List.getElem?_map, List.getElem?_drop,
    show m + 1 + (q - m) = q + 1 by omega]

def Dseq (n : ℕ) (C : Circuit) (m p : ℕ → ℕ) : ℕ → Circuit
  | 0 => C
  | k + 1 => PEqualNP.CircuitMoves.eraseGate n (Dseq n C m p k) (m k) (p k)

def Sec (n : ℕ) (C : Circuit) (m p : ℕ → ℕ) (j : ℕ) : Prop :=
  C.output ≠ n + m j ∧ (∀ b < j, p b ≠ n + m j) ∧
    ∀ (q : ℕ) (g : Gate), m j < q → C.gates[q]? = some g → n + m j ∈ g.inputs → ∃ i < j, m i = q

def W (n : ℕ) (S : Set (Fin n → Bool)) (m p : ℕ → ℕ) (C : Circuit) (k : ℕ) : Prop :=
  ∀ x ∈ S, (C.wires (List.ofFn x)).getD (n + m k) false = (C.wires (List.ofFn x)).getD (p k) false

theorem mbound (N : ℕ) (m : ℕ → ℕ) (hdec : ∀ a < N, ∀ b < a, m a < m b) :
    ∀ k < N, m k + k ≤ m 0 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := hdec (k + 1) hk k (by omega)
    omega

theorem inv (n N : ℕ) (C : Circuit) (m p : ℕ → ℕ)
    (hlen : ∀ k < N, m k + k < C.gates.length) (hdec : ∀ a < N, ∀ b < a, m a < m b) :
    ∀ k ≤ N, (Dseq n C m p k).gates.length + k = C.gates.length ∧
      (∀ i, (∀ j < k, i < m j) → (Dseq n C m p k).gates[i]? = C.gates[i]?) ∧
      (∀ j, k ≤ j → j < N → Sec n C m p j → (Dseq n C m p k).output ≠ n + m j) ∧
      (∀ j, k ≤ j → j < N → Sec n C m p j → ∀ (q : ℕ) (g : Gate), m j < q →
        (Dseq n C m p k).gates[q]? = some g → n + m j ∈ g.inputs →
          ∃ i, k ≤ i ∧ i < j ∧ m i = q) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨rfl, fun i _ => rfl, ?_, ?_⟩
    · intro j _ _ hs
      exact hs.1
    · intro j _ _ hs q g hq hg hin
      obtain ⟨i, hi, hmi⟩ := hs.2.2 q g hq hg hin
      exact ⟨i, Nat.zero_le _, hi, hmi⟩
  | succ k ih =>
    intro hk
    obtain ⟨hL, hP, hO, hR⟩ := ih (by omega)
    have hmk : m k < (Dseq n C m p k).gates.length := by
      have := hlen k (by omega)
      omega
    have hD : Dseq n C m p (k + 1)
        = PEqualNP.CircuitMoves.eraseGate n (Dseq n C m p k) (m k) (p k) := rfl
    rw [hD]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [erase_len _ _ _ _ hmk]
      omega
    · intro i hi
      rw [erase_lo _ _ _ _ hmk (hi k (by omega))]
      exact hP i (fun j hj => hi j (by omega))
    · intro j hj1 hj2 hs
      rw [erase_out _ _ _ _ hmk]
      have hmj : m j < m k := hdec j hj2 k (by omega)
      have hpk : p k ≠ n + m j := hs.2.1 k (by omega)
      have ho := hO j (by omega) hj2 hs
      unfold PEqualNP.CircuitMoves.eraseRedirect
      split_ifs <;> omega
    · intro j hj1 hj2 hs q g hq hg hin
      have hmj : m j < m k := hdec j hj2 k (by omega)
      have hpk : p k ≠ n + m j := hs.2.1 k (by omega)
      by_cases hqk : q < m k
      · rw [erase_lo _ _ _ _ hmk hqk] at hg
        obtain ⟨i, hi1, hi2, hi3⟩ := hR j (by omega) hj2 hs q g hq hg hin
        refine ⟨i, ?_, hi2, hi3⟩
        rcases Nat.eq_or_lt_of_le hi1 with h | h
        · subst h
          omega
        · omega
      · rw [erase_hi _ _ _ _ hmk (by omega)] at hg
        rcases hg' : (Dseq n C m p k).gates[q + 1]? with _ | g'
        · rw [hg'] at hg
          simp at hg
        · rw [hg'] at hg
          have hgeq : (⟨g'.op, g'.inputs.map (PEqualNP.CircuitMoves.eraseRedirect n (m k) (p k))⟩
              : Gate) = g := Option.some.inj hg
          rw [← hgeq] at hin
          dsimp only at hin
          rw [List.mem_map] at hin
          obtain ⟨u, hu, hue⟩ := hin
          unfold PEqualNP.CircuitMoves.eraseRedirect at hue
          split_ifs at hue with h1 h2
          · exact absurd hue hpk
          · omega
          · rw [hue] at hu
            obtain ⟨i, hi1, hi2, hi3⟩ := hR j (by omega) hj2 hs (q + 1) g' (by omega) hg' hu
            exfalso
            rcases Nat.eq_or_lt_of_le hi1 with h | h
            · subst h
              omega
            · have := hdec i (by omega) k h
              omega

theorem main (n N : ℕ) (C : Circuit) (S : Set (Fin n → Bool)) (m p : ℕ → ℕ)
    (hyp : ∀ k < N, m k < C.size ∧ p k < n + m k ∧ (∀ b < k, m k < m b) ∧
      (W n S m p C k ∨ C.output ≠ n + m k ∧ (∀ b < k, p b ≠ n + m k) ∧
        ∀ (q : ℕ) (g : Gate), m k < q → C.gates[q]? = some g → n + m k ∈ g.inputs →
          ∃ i < k, m i = q)) :
    ∃ D : ℕ → Circuit, D 0 = C ∧ ∀ k < N, m k < (D k).size ∧
      D (k + 1) = PEqualNP.CircuitMoves.eraseGate n (D k) (m k) (p k) ∧
      (W n S m p (D k) k ∨ (D k).output ≠ n + m k ∧
        ∀ g ∈ List.drop (m k + 1) (D k).gates, n + m k ∉ g.inputs) := by
  have hdec : ∀ a < N, ∀ b < a, m a < m b := fun a ha => (hyp a ha).2.2.1
  have hlen : ∀ k < N, m k + k < C.gates.length := by
    intro k hk
    have h0 := mbound N m hdec k hk
    have h1 := (hyp 0 (by omega)).1
    unfold Circuit.size at h1
    omega
  refine ⟨Dseq n C m p, rfl, ?_⟩
  intro k hk
  obtain ⟨hL, hP, hO, hR⟩ := inv n N C m p hlen hdec k (by omega)
  obtain ⟨_, hpk, _, hcase⟩ := hyp k hk
  have hmk : m k < (Dseq n C m p k).gates.length := by
    have := hlen k hk
    omega
  refine ⟨hmk, rfl, ?_⟩
  rcases hcase with hW | hS
  · left
    intro x hx
    have h := hW x hx
    have hlenC : m k + 1 ≤ C.gates.length := by
      have := hlen k hk
      omega
    have hpre : ∀ i < m k + 1, (Dseq n C m p k).gates[i]? = C.gates[i]? := by
      intro i hi
      apply hP i
      intro j hj
      have := hdec k hk j hj
      omega
    have key : ∀ i < n + (m k + 1), ((Dseq n C m p k).wires (List.ofFn x)).getD i false
        = (C.wires (List.ofFn x)).getD i false := by
      intro i hi
      show (wf (Dseq n C m p k).gates (List.ofFn x)).getD i false
        = (wf C.gates (List.ofFn x)).getD i false
      rw [wire_take _ _ (m k + 1) i (by simp; omega) (by omega),
        wire_take C.gates _ (m k + 1) i (by simp; omega) hlenC, take_eq _ _ _ hpre]
    rw [key _ (by omega), key _ (by omega)]
    exact h
  · right
    have hs : Sec n C m p k := hS
    refine ⟨hO k le_rfl hk hs, ?_⟩
    intro g hg hin
    obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hg
    rw [List.getElem?_drop] at hidx
    obtain ⟨i, hi1, hi2, _⟩ := hR k le_rfl hk hs _ g (by omega) hidx hin
    omega

end PEqualNP.Outside.L_meta_7993

theorem PEqualNP.Outside.L_meta_7993 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Set (Fin x1 → Bool)) (x5 x6 : ℕ → ℕ),   have x7 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : ℕ) =>     ∀ x9 ∈ x4,       have x11 : List Bool := x7.wires (List.ofFn x9);       x11.getD (x1 + x5 x8) Bool.false = x11.getD (x6 x8) Bool.false;   (∀ x8 < x2, x5 x8 < x3.size ∧ x6 x8 < x1 + x5 x8 ∧ (∀ x10 < x8, x5 x8 < x5 x10) ∧ (x7 x3 x8 ∨ x3.output ≠ x1 + x5 x8 ∧ (∀ x10 < x8, x6 x10 ≠ x1 + x5 x8) ∧ ∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x5 x8 < x10 → x3.gates[x10]? = Option.some x11 → x1 + x5 x8 ∈ x11.inputs → ∃ x15 < x8, x5 x15 = x10)) → ∃ (x9 : ℕ → PEqualNP.CircuitLowerBounds.Circuit), x9 (0 : ℕ) = x3 ∧ ∀ x10 < x2, x5 x10 < (x9 x10).size ∧ x9 (x10 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x9 x10) (x5 x10) (x6 x10) ∧ (x7 (x9 x10) x10 ∨ (x9 x10).output ≠ x1 + x5 x10 ∧ ∀ x12 ∈ List.drop (x5 x10 + (1 : ℕ)) (x9 x10).gates, x1 + x5 x10 ∉ x12.inputs) := by
  intro n N C S m p
  dsimp only
  intro hyp
  exact PEqualNP.Outside.L_meta_7993.main n N C S m p hyp
