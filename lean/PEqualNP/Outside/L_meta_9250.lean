import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9250

open PEqualNP.ProofComplexity PEqualNP.Search

abbrev V : Type := Fin (4 + 1) × Fin 4
abbrev Lit : Type := Literal V

def pig (i : Fin (4 + 1)) : List Lit := (List.finRange 4).map (fun j => ((i, j), true))

def hole (i i' : Fin (4 + 1)) (j : Fin 4) : List Lit := [((i, j), false), ((i', j), false)]

def baseL : List (List Lit) :=
  (List.finRange (4 + 1)).map pig ++
  (List.finRange (4 + 1)).flatMap (fun i => (List.finRange (4 + 1)).flatMap (fun i' =>
    if i < i' then (List.finRange 4).map (fun j => hole i i' j) else []))

def fires (S : List Lit) (D : List Lit) : Option Lit :=
  D.find? (fun l => decide (l ∉ S) && D.all (fun l' => decide (l' = l) || decide (negLit l' ∈ S)))

def stepF (S : List Lit) (D : List Lit) : List Lit :=
  match fires S D with
  | some l => l :: S
  | none => S

def sat : ℕ → List (List Lit) → List Lit → List Lit
  | 0, _, S => S
  | n + 1, G, S => sat n G (G.foldl stepF S)

def conflict (G : List (List Lit)) (S : List Lit) : Bool :=
  G.any (fun D => D.all (fun l => decide (negLit l ∈ S)))

def checkOne (rest : List (List Lit)) (C : List Lit) : Bool :=
  conflict (baseL ++ rest) (sat 6 (baseL ++ rest) (C.map negLit))

def checkAll : List (List Lit) → Bool
  | [] => true
  | C :: rest => checkOne rest C && checkAll rest

def N (i : Fin (4 + 1)) (j : Fin 4) : Lit := ((i, j), false)

def branch (h o1 o2 o3 : Fin 4) : List (List Lit) :=
  [[N 4 h, N 3 o1, N 2 o2], [N 4 h, N 3 o1], [N 4 h, N 3 o2, N 2 o1], [N 4 h, N 3 o2],
   [N 4 h, N 3 o3, N 2 o1]]

def oldest : List (List Lit) :=
  branch 0 1 2 3 ++ [[N 4 0]] ++ branch 1 0 2 3 ++ [[N 4 1]] ++ branch 2 0 1 3 ++ [[N 4 2]] ++
  branch 3 0 1 2 ++ [[]]

def learnedL : List (List Lit) := oldest.reverse

set_option maxRecDepth 100000 in
theorem check_ok : checkAll learnedL = true := by
  decide +kernel

theorem fires_sound {S D : List Lit} {l : Lit} (h : fires S D = some l) :
    l ∈ D ∧ ∀ l' ∈ D, l' ≠ l → negLit l' ∈ S := by
  unfold fires at h
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at hp
  intro l' hl' hne
  rcases hp.2 l' hl' with h1 | h1
  · exact absurd h1 hne
  · exact h1

theorem fold_sound (G : Set (Clause V)) (A : Set Lit) :
    ∀ (Γ : List (List Lit)), (∀ D ∈ Γ, D.toFinset ∈ G) → ∀ S : List Lit,
      (∀ l ∈ S, UPForces G A l) → ∀ l ∈ Γ.foldl stepF S, UPForces G A l := by
  intro Γ
  induction Γ with
  | nil => intro _ S hS; simpa using hS
  | cons D rest ih =>
    intro hΓ S hS
    rw [List.foldl_cons]
    apply ih (fun D' hD' => hΓ D' (List.mem_cons_of_mem _ hD'))
    unfold stepF
    cases hf : fires S D with
    | none => simpa using hS
    | some l =>
      obtain ⟨hl, hother⟩ := fires_sound hf
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact UPForces.unit (hΓ D (List.mem_cons_self ..)) (List.mem_toFinset.mpr hl)
          (fun l' hl' hne => hS _ (hother l' (List.mem_toFinset.mp hl') hne))
      · exact hS x hx

theorem sat_sound (G : Set (Clause V)) (A : Set Lit) (Γ : List (List Lit))
    (hΓ : ∀ D ∈ Γ, D.toFinset ∈ G) :
    ∀ (n : ℕ) (S : List Lit), (∀ l ∈ S, UPForces G A l) → ∀ l ∈ sat n Γ S, UPForces G A l := by
  intro n
  induction n with
  | zero => intro S hS; simpa [sat] using hS
  | succ n ih =>
    intro S hS
    exact ih _ (fold_sound G A Γ hΓ S hS)

theorem base_mem : ∀ D ∈ baseL, D.toFinset ∈ PHP (4 + 1) 4 := by
  intro D hD
  simp only [baseL, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_finRange,
    true_and] at hD
  rcases hD with ⟨i, rfl⟩ | ⟨i, i', hD⟩
  · refine Or.inl ⟨i, ?_⟩
    ext x
    simp [pig]
  · split_ifs at hD with hlt
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hD
      exact Or.inr ⟨i, i', j, ne_of_lt hlt, by simp [hole]⟩
    · simp at hD

theorem checkOne_sound (rest : List (List Lit)) (C : List Lit) (h : checkOne rest C = true) :
    IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ rest.map List.toFinset}) C.toFinset := by
  set G : Set (Clause V) := PHP (4 + 1) 4 ∪ {D | D ∈ rest.map List.toFinset} with hG
  set A : Set Lit := negLit '' (↑C.toFinset : Set Lit) with hA
  have hΓ : ∀ D ∈ baseL ++ rest, D.toFinset ∈ G := by
    intro D hD
    rcases List.mem_append.mp hD with hb | hr
    · exact Or.inl (base_mem D hb)
    · exact Or.inr (List.mem_map_of_mem hr)
  have h0 : ∀ l ∈ C.map negLit, UPForces G A l := by
    intro l hl
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
    exact UPForces.hyp ⟨c, by simpa using hc, rfl⟩
  have hS := sat_sound G A (baseL ++ rest) hΓ 6 (C.map negLit) h0
  unfold checkOne conflict at h
  obtain ⟨D, hD, hall⟩ := List.any_eq_true.mp h
  refine ⟨D.toFinset, hΓ D hD, ?_⟩
  intro l hl
  have := (List.all_eq_true.mp hall) l (List.mem_toFinset.mp hl)
  exact hS _ (of_decide_eq_true this)

theorem checkAll_sound : ∀ (ls : List (List Lit)), checkAll ls = true →
    IsRUPRun (PHP (4 + 1) 4) (ls.map List.toFinset) := by
  intro ls
  induction ls with
  | nil => intro _; exact IsRUPRun.nil
  | cons C rest ih =>
    intro h
    simp only [checkAll, Bool.and_eq_true] at h
    exact IsRUPRun.learn (ih h.2) (checkOne_sound rest C h.1)

end PEqualNP.Outside.L_meta_9250

theorem PEqualNP.Outside.L_meta_9250 : ∃ ρ : List (PEqualNP.ProofComplexity.Clause (Fin (4 + 1) × Fin 4)), PEqualNP.Search.IsRUPRun (PEqualNP.ProofComplexity.PHP (4 + 1) 4) ρ ∧ (∅ : PEqualNP.ProofComplexity.Clause (Fin (4 + 1) × Fin 4)) ∈ ρ ∧ ρ.length ≤ 24 := by
  refine ⟨PEqualNP.Outside.L_meta_9250.learnedL.map List.toFinset,
    PEqualNP.Outside.L_meta_9250.checkAll_sound _ PEqualNP.Outside.L_meta_9250.check_ok, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨[], by decide +kernel, rfl⟩
  · simp only [List.length_map]
    decide +kernel
