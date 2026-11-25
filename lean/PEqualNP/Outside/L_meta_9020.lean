import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9020

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

inductive Lit where
  | const (b : Bool)
  | wire (k : ℕ)

def readL (W : List Bool) : Lit → Bool
  | Lit.const b => b
  | Lit.wire k => W.getD k false

def evalG (W : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => W.getD i false)

def one : Lit → Gate
  | Lit.const true => ⟨GateOp.and, []⟩
  | Lit.const false => ⟨GateOp.or, []⟩
  | Lit.wire a => ⟨GateOp.and, [a]⟩

def andL : Lit → Lit → Gate
  | Lit.const false, _ => ⟨GateOp.or, []⟩
  | Lit.const true, y => one y
  | Lit.wire a, Lit.const false => ⟨GateOp.or, []⟩
  | Lit.wire a, Lit.const true => ⟨GateOp.and, [a]⟩
  | Lit.wire a, Lit.wire b => ⟨GateOp.and, [a, b]⟩

def orL : Lit → Lit → Gate
  | Lit.const true, _ => ⟨GateOp.and, []⟩
  | Lit.const false, y => one y
  | Lit.wire a, Lit.const true => ⟨GateOp.and, []⟩
  | Lit.wire a, Lit.const false => ⟨GateOp.and, [a]⟩
  | Lit.wire a, Lit.wire b => ⟨GateOp.or, [a, b]⟩

theorem evalG_one (W : List Bool) (l : Lit) : evalG W (one l) = readL W l := by
  rcases l with b | a
  · cases b <;> simp [one, evalG, readL, GateOp.eval]
  · simp [one, evalG, readL, GateOp.eval]

theorem evalG_andL (W : List Bool) (x y : Lit) :
    evalG W (andL x y) = (readL W x && readL W y) := by
  rcases x with b | a
  · cases b
    · simp [andL, evalG, readL, GateOp.eval]
    · simp [andL, evalG_one, readL]
  · rcases y with c | b
    · cases c <;> simp [andL, evalG, readL, GateOp.eval]
    · simp [andL, evalG, readL, GateOp.eval]

theorem evalG_orL (W : List Bool) (x y : Lit) :
    evalG W (orL x y) = (readL W x || readL W y) := by
  rcases x with b | a
  · cases b
    · simp [orL, evalG_one, readL]
    · simp [orL, evalG, readL, GateOp.eval]
  · rcases y with c | b
    · cases c <;> simp [orL, evalG, readL, GateOp.eval]
    · simp [orL, evalG, readL, GateOp.eval]

def posG (P Q : ℕ → Lit) (g : Gate) : Gate :=
  match g.op, g.inputs with
  | GateOp.and, [] => one (Lit.const true)
  | GateOp.and, [a] => one (P a)
  | GateOp.and, [a, b] => andL (P a) (P b)
  | GateOp.or, [] => one (Lit.const false)
  | GateOp.or, [a] => one (P a)
  | GateOp.or, [a, b] => orL (P a) (P b)
  | GateOp.not, [] => one (Lit.const true)
  | GateOp.not, a :: _ => one (Q a)
  | _, _ => one (Lit.const false)

def negG (P Q : ℕ → Lit) (g : Gate) : Gate :=
  match g.op, g.inputs with
  | GateOp.and, [] => one (Lit.const false)
  | GateOp.and, [a] => one (Q a)
  | GateOp.and, [a, b] => orL (Q a) (Q b)
  | GateOp.or, [] => one (Lit.const true)
  | GateOp.or, [a] => one (Q a)
  | GateOp.or, [a, b] => andL (Q a) (Q b)
  | GateOp.not, [] => one (Lit.const false)
  | GateOp.not, a :: _ => one (P a)
  | _, _ => one (Lit.const false)

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem sem (P Q : ℕ → Lit) (V W : List Bool)
    (hp : ∀ i, readL W (P i) = V.getD i false) (hq : ∀ i, readL W (Q i) = !V.getD i false)
    (g : Gate) (hg : Ok g) :
    evalG W (posG P Q g) = evalG V g ∧ evalG W (negG P Q g) = !evalG V g := by
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp only [posG, negG, evalG_one]; simp [readL, evalG, GateOp.eval]
    · simp only [posG, negG, evalG_one, hp, hq]; simp [evalG, GateOp.eval]
    · simp only [posG, negG, evalG_andL, evalG_orL, hp, hq]; simp [evalG, GateOp.eval]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp only [posG, negG, evalG_one]; simp [readL, evalG, GateOp.eval]
    · simp only [posG, negG, evalG_one, hp, hq]; simp [evalG, GateOp.eval]
    · simp only [posG, negG, evalG_andL, evalG_orL, hp, hq]; simp [evalG, GateOp.eval]
    · simp at hlen
  · rcases ins with _ | ⟨a, rest⟩
    · simp only [posG, negG, evalG_one]; simp [readL, evalG, GateOp.eval]
    · simp only [posG, negG, evalG_one, hp, hq]; simp [evalG, GateOp.eval]

theorem mono_one (l : Lit) : (one l).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
    (one l).inputs.length ≤ 2 := by
  rcases l with b | a
  · cases b <;> simp [one]
  · simp [one]

theorem mono_andL (x y : Lit) : (andL x y).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
    (andL x y).inputs.length ≤ 2 := by
  rcases x with b | a
  · cases b
    · simp [andL]
    · simpa [andL] using mono_one y
  · rcases y with c | b
    · cases c <;> simp [andL]
    · simp [andL]

theorem mono_orL (x y : Lit) : (orL x y).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
    (orL x y).inputs.length ≤ 2 := by
  rcases x with b | a
  · cases b
    · simpa [orL] using mono_one y
    · simp [orL]
  · rcases y with c | b
    · cases c <;> simp [orL]
    · simp [orL]

theorem mono_posG (P Q : ℕ → Lit) (g : Gate) :
    (posG P Q g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
    (posG P Q g).inputs.length ≤ 2 := by
  rcases g with ⟨op, ins⟩
  unfold posG
  split
  all_goals first | exact mono_one _ | exact mono_andL _ _ | exact mono_orL _ _

theorem mono_negG (P Q : ℕ → Lit) (g : Gate) :
    (negG P Q g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
    (negG P Q g).inputs.length ≤ 2 := by
  rcases g with ⟨op, ins⟩
  unfold negG
  split
  all_goals first | exact mono_one _ | exact mono_andL _ _ | exact mono_orL _ _

def PL (n j i : ℕ) : Lit :=
  if i < n then Lit.wire i else if i < n + j then Lit.wire (2 * n + 2 * (i - n)) else Lit.const false

def QL (n j i : ℕ) : Lit :=
  if i < n then Lit.wire (n + i) else if i < n + j then Lit.wire (2 * n + 2 * (i - n) + 1)
  else Lit.const true

def trans (n : ℕ) : ℕ → List Gate → List Gate
  | _, [] => []
  | j, g :: rest => posG (PL n j) (QL n j) g :: negG (PL n j) (QL n j) g :: trans n (j + 1) rest

theorem length_trans (n : ℕ) : ∀ (j : ℕ) (gs : List Gate), (trans n j gs).length = 2 * gs.length
  | _, [] => rfl
  | j, g :: rest => by
    simp only [trans, List.length_cons, length_trans n (j + 1) rest]
    ring

theorem mono_trans (n : ℕ) : ∀ (j : ℕ) (gs : List Gate), ∀ g ∈ trans n j gs,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
  | _, [] => by simp [trans]
  | j, g :: rest => by
    intro h hh
    simp only [trans, List.mem_cons] at hh
    rcases hh with rfl | rfl | hh
    · exact mono_posG _ _ _
    · exact mono_negG _ _ _
    · exact mono_trans n (j + 1) rest h hh

def stepC (w : List Bool) (g : Gate) : List Bool := w ++ [evalG w g]

theorem readL_append (W X : List Bool) (l : Lit) (hl : ∀ k, l = Lit.wire k → k < W.length) :
    readL (W ++ X) l = readL W l := by
  rcases l with b | k
  · rfl
  · have := hl k rfl
    simp only [readL]
    exact List.getD_append W X false k this

theorem PL_bound (n j i k : ℕ) (h : PL n j i = Lit.wire k) : k < 2 * n + 2 * j := by
  unfold PL at h
  split_ifs at h with h1 h2
  · cases h; omega
  · cases h; omega

theorem QL_bound (n j i k : ℕ) (h : QL n j i = Lit.wire k) : k < 2 * n + 2 * j := by
  unfold QL at h
  split_ifs at h with h1 h2
  · cases h; omega
  · cases h; omega

theorem main (n : ℕ) : ∀ (gs : List Gate) (j : ℕ) (V W : List Bool), (∀ g ∈ gs, Ok g) →
    V.length = n + j → W.length = 2 * n + 2 * j →
    (∀ i, readL W (PL n j i) = V.getD i false) → (∀ i, readL W (QL n j i) = !V.getD i false) →
    ∀ i, readL ((trans n j gs).foldl stepC W) (PL n (j + gs.length) i) =
      (gs.foldl stepC V).getD i false
  | [], j, V, W, _, _, _, hp, _ => by simpa [trans] using hp
  | g :: rest, j, V, W, hok, hV, hW, hp, hq => by
    have hg : Ok g := hok g (by simp)
    have hrest : ∀ g ∈ rest, Ok g := fun g' h' => hok g' (by simp [h'])
    have hs := sem (PL n j) (QL n j) V W hp hq g hg
    set W1 := stepC W (posG (PL n j) (QL n j) g) with hW1
    set W2 := stepC W1 (negG (PL n j) (QL n j) g) with hW2
    set V1 := stepC V g with hV1
    have hp1 : ∀ i, readL W1 (PL n j i) = V.getD i false := by
      intro i
      rw [hW1, stepC, readL_append]
      · exact hp i
      · intro k hk; rw [hW]; exact PL_bound n j i k hk
    have hq1 : ∀ i, readL W1 (QL n j i) = !V.getD i false := by
      intro i
      rw [hW1, stepC, readL_append]
      · exact hq i
      · intro k hk; rw [hW]; exact QL_bound n j i k hk
    have hs1 := sem (PL n j) (QL n j) V W1 hp1 hq1 g hg
    have hW1l : W1.length = 2 * n + 2 * j + 1 := by simp [hW1, stepC, hW]
    have hW2l : W2.length = 2 * n + 2 * (j + 1) := by simp [hW2, stepC, hW1l]; ring
    have hV1l : V1.length = n + (j + 1) := by simp [hV1, stepC, hV]; ring
    have key : (∀ i, readL W2 (PL n (j + 1) i) = V1.getD i false) ∧
        (∀ i, readL W2 (QL n (j + 1) i) = !V1.getD i false) := by
      constructor
      · intro i
        rcases lt_trichotomy i (n + j) with h | h | h
        · have e : PL n (j + 1) i = PL n j i := by
            unfold PL; split_ifs <;> first | rfl | omega | (congr 1; omega)
          rw [e, hW2, stepC, readL_append, hp1 i, hV1, stepC, List.getD_append V _ false i (by omega)]
          intro k hk; rw [hW1l]; have := PL_bound n j i k hk; omega
        · subst h
          have e : PL n (j + 1) (n + j) = Lit.wire (2 * n + 2 * j) := by
            unfold PL; split_ifs <;> first | rfl | omega | (congr 1; omega)
          rw [e, hW2, stepC, hV1, stepC]
          simp only [readL]
          rw [List.getD_append W1 _ false (2 * n + 2 * j) (by omega), hW1, stepC,
            List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          simp [hW, hV, hs.1]
        · have e : PL n (j + 1) i = Lit.const false := by
            unfold PL; split_ifs <;> first | rfl | omega | (congr 1; omega)
          rw [e]
          simp only [readL]
          rw [List.getD_eq_default _ _ (by omega)]
      · intro i
        rcases lt_trichotomy i (n + j) with h | h | h
        · have e : QL n (j + 1) i = QL n j i := by
            unfold QL; split_ifs <;> first | rfl | omega | (congr 1; omega)
          rw [e, hW2, stepC, readL_append, hq1 i, hV1, stepC, List.getD_append V _ false i (by omega)]
          intro k hk; rw [hW1l]; have := QL_bound n j i k hk; omega
        · subst h
          have e : QL n (j + 1) (n + j) = Lit.wire (2 * n + 2 * j + 1) := by
            unfold QL; split_ifs <;> first | rfl | omega | (congr 1; omega)
          rw [e, hW2, stepC, hV1, stepC]
          simp only [readL]
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          simp [hW1l, hV, hs1.2]
        · have e : QL n (j + 1) i = Lit.const true := by
            unfold QL; split_ifs <;> first | rfl | omega | (congr 1; omega)
          rw [e]
          simp only [readL]
          rw [List.getD_eq_default _ _ (by omega)]
          rfl
    have ih := main n rest (j + 1) V1 W2 hrest hV1l hW2l key.1 key.2
    intro i
    have e2 : j + (g :: rest).length = j + 1 + rest.length := by simp; ring
    rw [e2]
    simpa [trans, List.foldl_cons, hW1, hW2, hV1] using ih i

theorem dual (n s : ℕ) (f : (Fin n → Bool) → Bool) (h : HasCircuitSize n f s) :
    PEqualNP.Represents.HasLitSize n f (2 * s) := by
  obtain ⟨C, hfan, hsize, heval⟩ := h
  let o : ℕ := match PL n C.gates.length C.output with
    | Lit.wire k => k
    | Lit.const _ => 2 * n + 2 * C.gates.length
  refine ⟨⟨trans n 0 C.gates, o⟩, ?_, ?_, ?_⟩
  · intro g hg
    exact mono_trans n 0 C.gates g hg
  · show (trans n 0 C.gates).length ≤ 2 * s
    rw [length_trans]
    have : C.gates.length ≤ s := hsize
    omega
  · intro x
    rw [← heval x]
    have hok : ∀ g ∈ C.gates, Ok g := hfan
    have hV : (List.ofFn x).length = n + 0 := by simp
    have hW : (List.ofFn x ++ List.ofFn fun i => !x i).length = 2 * n + 2 * 0 := by simp; ring
    have hp : ∀ i, readL (List.ofFn x ++ List.ofFn fun i => !x i) (PL n 0 i) =
        (List.ofFn x).getD i false := by
      intro i
      unfold PL
      split_ifs with h1 h2
      · simp only [readL]
        rw [List.getD_append (List.ofFn x) _ false i (by simpa using h1)]
      · omega
      · simp only [readL]
        rw [List.getD_eq_default _ _ (by simp; omega)]
    have hq : ∀ i, readL (List.ofFn x ++ List.ofFn fun i => !x i) (QL n 0 i) =
        !(List.ofFn x).getD i false := by
      intro i
      unfold QL
      split_ifs with h1 h2
      · simp only [readL]
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp [h1]
      · omega
      · simp only [readL]
        rw [List.getD_eq_default _ _ (by simp; omega)]
        rfl
    have hm := main n C.gates 0 _ _ hok hV hW hp hq C.output
    simp only [Nat.zero_add] at hm
    unfold Circuit.eval Circuit.wires
    have ew : ∀ (gs : List Gate) (w : List Bool),
        gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w =
        gs.foldl stepC w := fun _ _ => rfl
    simp only [ew]
    rw [← hm]
    show (List.foldl stepC _ (trans n 0 C.gates)).getD o false = _
    have hlen : (List.foldl stepC (List.ofFn x ++ List.ofFn fun i => !x i)
        (trans n 0 C.gates)).length = 2 * n + 2 * C.gates.length := by
      have : ∀ (gs : List Gate) (w : List Bool), (gs.foldl stepC w).length = w.length + gs.length := by
        intro gs
        induction gs with
        | nil => intro w; simp
        | cons g rest ih => intro w; simp [ih, stepC]; ring
      rw [this, length_trans]; simp; ring
    simp only [o]
    split
    · next k hk => rw [hk]; rfl
    · next b hb =>
      rw [hb]
      have : b = false := by
        unfold PL at hb; split_ifs at hb; cases hb; rfl
      subst this
      simp only [readL]
      exact List.getD_eq_default _ _ (by omega)

end PEqualNP.Outside.L_meta_9020

theorem PEqualNP.Outside.L_meta_9020 : ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.HasCircuitSize n f s → PEqualNP.Represents.HasLitSize n f (2 * s) := by
  intro n s f h
  exact PEqualNP.Outside.L_meta_9020.dual n s f h
