import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8125

open PEqualNP.CircuitLowerBounds

-- order a list of at most two wires strictly, dropping a repeat
def sort2 : List ℕ → List ℕ
  | [] => []
  | [a] => [a]
  | [a, b] => if a < b then [a, b] else if b < a then [b, a] else [a]
  | a :: b :: c :: l => a :: b :: c :: l

def normIn : GateOp → List ℕ → List ℕ
  | GateOp.not, l => l.take 1
  | GateOp.and, l => sort2 l
  | GateOp.or, l => sort2 l
  | GateOp.mod _, l => l
  | GateOp.maj, l => l

def gnorm (g : Gate) : Gate := ⟨g.op, normIn g.op g.inputs⟩

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem sort2_len (l : List ℕ) : (sort2 l).length ≤ l.length := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp [sort2]
  · simp [sort2]
  · simp only [sort2]
    split_ifs <;> simp
  · simp [sort2]

theorem sort2_mem (l : List ℕ) (x : ℕ) (h : x ∈ sort2 l) : x ∈ l := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simpa [sort2] using h
  · simpa [sort2] using h
  · simp only [sort2] at h
    split_ifs at h <;> simp at h ⊢ <;> omega
  · simpa [sort2] using h

theorem sort2_pw (l : List ℕ) (h : l.length ≤ 2) :
    List.Pairwise (fun (x y : ℕ) => x < y) (sort2 l) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp [sort2]
  · simp [sort2]
  · simp only [sort2]
    split_ifs with h1 h2
    · simp [h1]
    · simp [h2]
    · simp
  · simp only [List.length_cons] at h
    omega

theorem normIn_len (op : GateOp) (l : List ℕ) : (normIn op l).length ≤ l.length := by
  cases op with
  | not => simp [normIn]
  | and => exact sort2_len l
  | or => exact sort2_len l
  | mod m => simp [normIn]
  | maj => simp [normIn]

theorem normIn_mem (op : GateOp) (l : List ℕ) (x : ℕ) (h : x ∈ normIn op l) : x ∈ l := by
  cases op with
  | not => exact List.mem_of_mem_take h
  | and => exact sort2_mem l x h
  | or => exact sort2_mem l x h
  | mod m => exact h
  | maj => exact h

theorem evalNorm (op : GateOp) (l : List ℕ) (h : l.length ≤ 2) (f : ℕ → Bool) :
    op.eval ((normIn op l).map f) = op.eval (l.map f) := by
  cases op with
  | not =>
    rcases l with _ | ⟨a, l⟩
    · rfl
    · rfl
  | and =>
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · rfl
    · rfl
    · simp only [normIn, sort2]
      split_ifs with h1 h2
      · rfl
      · simp only [GateOp.eval, List.map_cons, List.map_nil]
        cases f a <;> cases f b <;> rfl
      · have e : a = b := by omega
        subst e
        simp only [GateOp.eval, List.map_cons, List.map_nil]
        cases f a <;> rfl
    · simp only [List.length_cons] at h
      omega
  | or =>
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · rfl
    · rfl
    · simp only [normIn, sort2]
      split_ifs with h1 h2
      · rfl
      · simp only [GateOp.eval, List.map_cons, List.map_nil]
        cases f a <;> cases f b <;> rfl
      · have e : a = b := by omega
        subst e
        simp only [GateOp.eval, List.map_cons, List.map_nil]
        cases f a <;> rfl
    · simp only [List.length_cons] at h
      omega
  | mod m => rfl
  | maj => rfl

theorem wstep_gnorm (w : List Bool) (g : Gate) (h : g.inputs.length ≤ 2) :
    wstep w (gnorm g) = wstep w g := by
  unfold wstep gnorm
  dsimp only
  rw [evalNorm g.op g.inputs h]

theorem foldNorm (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ w : List Bool, (gs.map gnorm).foldl wstep w = gs.foldl wstep w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    simp only [List.map_cons, List.foldl_cons]
    rw [wstep_gnorm w g (h g (by simp))]
    exact ih (fun g' hg' => h g' (by simp [hg'])) _

end PEqualNP.Outside.L_meta_8125

open PEqualNP.Outside.L_meta_8125 in
theorem PEqualNP.Outside.L_meta_8125 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x3 ∈ x1.gates, ∀ x5 ∈ x3.inputs, x5 ≤ (29 : ℕ)) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ x4.size = x1.size ∧ x4.output = x1.output ∧ (∀ x5 ∈ x4.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (29 : ℕ)) ∧ (∀ x5 ∈ x4.gates, List.Pairwise (fun (x7 x8 : ℕ) => x7 < x8) x5.inputs ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length ≤ (1 : ℕ))) ∧ ∀ (x5 : List Bool), x4.eval x5 = x1.eval x5 := by
  intro C hF hB
  unfold PEqualNP.MetaComplexity.FanInTwo at hF
  refine ⟨⟨C.gates.map gnorm, C.output⟩, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · unfold PEqualNP.MetaComplexity.FanInTwo
    intro g' hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
    obtain ⟨hop, hlen⟩ := hF g hg
    exact ⟨hop, (normIn_len g.op g.inputs).trans hlen⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro g' hg' x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
    exact hB g hg x (normIn_mem g.op g.inputs x hx)
  · intro g' hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
    obtain ⟨hop, hlen⟩ := hF g hg
    rcases g with ⟨op, l⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    dsimp only at hlen
    rcases hop with rfl | rfl | rfl
    · refine ⟨sort2_pw l hlen, ?_⟩
      intro h
      simp [gnorm] at h
    · refine ⟨sort2_pw l hlen, ?_⟩
      intro h
      simp [gnorm] at h
    · refine ⟨?_, ?_⟩
      · show List.Pairwise (fun (x7 x8 : ℕ) => x7 < x8) (l.take 1)
        rcases l with _ | ⟨a, l⟩ <;> simp
      · intro _
        show (l.take 1).length ≤ 1
        simp
  · intro x
    show (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.gates.map gnorm, C.output⟩ x).getD C.output false
      = (C.wires x).getD C.output false
    congr 1
    exact foldNorm C.gates (fun g hg => (hF g hg).2) x
