import Lax461425.Permanent
import Mathlib.Tactic

/-!
The cycle-cover calculation for the paper's bouquet. A degree-`d b` monomial has
`d b + 1` private vertices, so constant monomials give two-cycles without padding.
-/

namespace Lax461425Proofs.PermanentBouquet

open scoped BigOperators Classical
open Equiv Finset

variable {B R : Type*} [Fintype B] [DecidableEq B] [CommSemiring R]

abbrev Vertex (B : Type*) (d : B → ℕ) := Option (Σ b, Fin (d b + 1))

/-- The successor on a branch, returning to the common vertex after its last vertex. -/
def advance {d : B → ℕ} (b : B) (j : Fin (d b + 1)) : Vertex B d :=
  if h : j.val < d b then some ⟨b, ⟨j.val + 1, by omega⟩⟩ else none

lemma advance_ne_self {d : B → ℕ} (b : B) (j : Fin (d b + 1)) :
    advance b j ≠ some ⟨b, j⟩ := by
  unfold advance
  split_ifs with h
  · intro he
    have := congrArg (fun v : Vertex B d => v.map (fun p => p.2.val)) he
    simp at this
  · simp

/-- Follow the selected branch and fix all other private vertices. -/
def step {d : B → ℕ} (b : B) : Vertex B d → Vertex B d
  | none => some ⟨b, 0⟩
  | some ⟨s, j⟩ => if s = b then advance s j else some ⟨s, j⟩

def previous {d : B → ℕ} (b : B) : Vertex B d → Vertex B d
  | none => some ⟨b, Fin.last (d b)⟩
  | some ⟨s, j⟩ => if s = b then
      if h : j.val = 0 then none else some ⟨s, ⟨j.val - 1, by omega⟩⟩
    else some ⟨s, j⟩

lemma previous_step {d : B → ℕ} (b : B) : Function.LeftInverse (previous b) (step (d := d) b) := by
  intro v
  cases v with
  | none => simp [step, previous]
  | some v =>
    rcases v with ⟨s, j⟩
    by_cases hs : s = b
    · subst s
      rw [step, if_pos rfl]
      by_cases hj : j.val < d b
      · rw [advance, dif_pos hj]
        have hn : j.val + 1 ≠ 0 := by omega
        simp only [previous, ↓reduceIte, dif_neg hn]
        apply congrArg (fun k : Fin (d b + 1) => (some ⟨b, k⟩ : Vertex B d))
        apply Fin.ext
        simp
      · rw [advance, dif_neg hj]
        change (some ⟨b, Fin.last (d b)⟩ : Vertex B d) = some ⟨b, j⟩
        apply congrArg (fun k : Fin (d b + 1) => (some ⟨b, k⟩ : Vertex B d))
        apply Fin.ext
        simp
        omega
    · simp [step, previous, hs]

lemma step_injective {d : B → ℕ} (b : B) : Function.Injective (step (d := d) b) :=
  (previous_step b).injective
noncomputable def cycle {d : B → ℕ} (b : B) : Equiv.Perm (Vertex B d) :=
  Equiv.ofBijective (step b) ⟨step_injective b, Finite.surjective_of_injective (step_injective b)⟩

@[simp] lemma cycle_apply {d : B → ℕ} (b : B) (v : Vertex B d) : cycle b v = step b v := by
  unfold cycle; rfl

lemma cycle_injective {d : B → ℕ} : Function.Injective (cycle (B := B) (d := d)) := by
  intro b c he
  have h := congrArg (fun σ : Equiv.Perm (Vertex B d) => (σ none).map Sigma.fst) he
  simpa [step] using h

/-- The weighted adjacency matrix: outgoing weights of each branch are `c` followed by `a`.
Every private vertex also has a loop of weight one; the common vertex has no loop. -/
def matrix {d : B → ℕ} (c : B → R) (a : ∀ b, Fin (d b + 1) → R) :
    Matrix (Vertex B d) (Vertex B d) R := fun target source =>
  match source with
  | none => match target with
    | none => 0
    | some ⟨b, j⟩ => if j = 0 then c b else 0
  | some ⟨b, j⟩ => if target = some ⟨b, j⟩ then 1
    else if target = advance b j then a b j else 0

lemma matrix_head {d : B → ℕ} (c : B → R) (a : ∀ b, Fin (d b + 1) → R) (b : B) :
    matrix c a (cycle b none) none = c b := by simp [matrix, step]

lemma matrix_private {d : B → ℕ} (c : B → R) (a : ∀ b, Fin (d b + 1) → R)
    (b s : B) (j : Fin (d s + 1)) :
    matrix c a (cycle b (some ⟨s, j⟩)) (some ⟨s, j⟩) = if s = b then a s j else 1 := by
  by_cases hs : s = b
  · simp [matrix, step, hs, advance_ne_self]
  · simp [matrix, step, hs]

lemma cycle_weight {d : B → ℕ} (c : B → R) (a : ∀ b, Fin (d b + 1) → R) (b : B) :
    (∏ v, matrix c a (cycle b v) v) = c b * ∏ j, a b j := by
  rw [Fintype.prod_option, matrix_head]
  simp_rw [Fintype.prod_sigma, matrix_private]
  simp

/-- On an unselected branch, surjectivity forces every vertex to use its loop. -/
lemma fixes_other_branch {d : B → ℕ} (σ : Equiv.Perm (Vertex B d)) (b : B)
    (hhead : σ none = some ⟨b, 0⟩)
    (hfollow : ∀ s j, σ (some ⟨s, j⟩) = some ⟨s, j⟩ ∨
      σ (some ⟨s, j⟩) = advance s j) (s : B) (hs : s ≠ b) (j : Fin (d s + 1)) :
    σ (some ⟨s, j⟩) = some ⟨s, j⟩ := by
  induction hj : j.val using Nat.strong_induction_on generalizing j with
  | h k ih =>
    obtain ⟨v, hv⟩ := σ.surjective (some ⟨s, j⟩)
    cases v with
    | none =>
      rw [hhead] at hv
      have hb := congrArg (fun v : Vertex B d => v.map Sigma.fst) hv
      simp at hb
      exact (hs hb.symm).elim
    | some v =>
      rcases v with ⟨t, i⟩
      rcases hfollow t i with hf | ha
      · rw [hf] at hv
        cases hv
        exact hf
      · rw [ha] at hv
        unfold advance at hv
        split_ifs at hv with hi
        · have ht := congrArg (fun v : Vertex B d => v.map Sigma.fst) hv
          have hij := congrArg (fun v : Vertex B d => v.map (fun p => p.2.val)) hv
          simp at ht hij
          subst t
          have hfix := ih i.val (by omega) i rfl
          rw [hfix] at ha
          have hi' := advance_ne_self s i
          exact (hi' ha.symm).elim

/-- The selected branch must be traversed completely, since no vertex can have two
predecessors in a permutation. -/
lemma follows_selected_branch {d : B → ℕ} (σ : Equiv.Perm (Vertex B d)) (b : B)
    (hhead : σ none = some ⟨b, 0⟩)
    (hfollow : ∀ s j, σ (some ⟨s, j⟩) = some ⟨s, j⟩ ∨
      σ (some ⟨s, j⟩) = advance s j) (j : Fin (d b + 1)) :
    σ (some ⟨b, j⟩) = advance b j := by
  induction j using Fin.induction with
  | zero =>
    rcases hfollow b 0 with h | h
    · have := σ.injective (hhead.trans h.symm)
      simp at this
    · exact h
  | succ j ih =>
    rcases hfollow b j.succ with h | h
    · have ha : advance b j.castSucc = some ⟨b, j.succ⟩ := by
        simp [advance, j.isLt, Fin.ext_iff]
      have hprev := ih.trans ha
      have he := σ.injective (hprev.trans h.symm)
      have hv := congrArg (fun v : Vertex B d => v.map (fun p => p.2.val)) he
      simp at hv
    · exact h

lemma eq_cycle_of_follows {d : B → ℕ} (σ : Equiv.Perm (Vertex B d)) (b : B)
    (hhead : σ none = some ⟨b, 0⟩)
    (hfollow : ∀ s j, σ (some ⟨s, j⟩) = some ⟨s, j⟩ ∨
      σ (some ⟨s, j⟩) = advance s j) : σ = cycle b := by
  apply Equiv.ext
  intro v
  cases v with
  | none => exact hhead
  | some v =>
    rcases v with ⟨s, j⟩
    by_cases hs : s = b
    · subst s
      simpa [step] using follows_selected_branch σ b hhead hfollow j
    · simpa [step, hs] using fixes_other_branch σ b hhead hfollow s hs j

lemma eq_cycle_of_weight_ne_zero {d : B → ℕ} (c : B → R) (a : ∀ b, Fin (d b + 1) → R)
    (σ : Equiv.Perm (Vertex B d)) (h : (∏ v, matrix c a (σ v) v) ≠ 0) :
    ∃ b, σ = cycle b := by
  have he (v : Vertex B d) : matrix c a (σ v) v ≠ 0 := by
    intro hz
    exact h (Finset.prod_eq_zero (Finset.mem_univ v) hz)
  have hh := he none
  cases hv : σ none with
  | none => simp [matrix, hv] at hh
  | some v =>
    rcases v with ⟨b, j⟩
    have hj : j = 0 := by
      by_contra hj
      simp [matrix, hv, hj] at hh
    subst j
    refine ⟨b, eq_cycle_of_follows σ b hv ?_⟩
    intro s j
    by_cases hs : σ (some ⟨s, j⟩) = some ⟨s, j⟩
    · exact Or.inl hs
    · right
      by_contra ha
      exact he (some ⟨s, j⟩) (by simp [matrix, hs, ha])

/-- Every cycle cover is exactly one branch cycle and loops on the other branches. -/
theorem permanent_matrix {d : B → ℕ} (c : B → R) (a : ∀ b, Fin (d b + 1) → R) :
    Matrix.permanent (matrix c a) = ∑ b, c b * ∏ j, a b j := by
  unfold Matrix.permanent
  calc
    _ = ∑ σ ∈ Finset.univ.image (cycle (B := B) (d := d)), ∏ v, matrix c a (σ v) v := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro σ _ hσ
      by_contra hne
      obtain ⟨b, hb⟩ := eq_cycle_of_weight_ne_zero c a σ hne
      exact hσ (by simp [hb])
    _ = ∑ b, ∏ v, matrix c a (cycle b v) v := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => cycle_injective h
    _ = _ := Finset.sum_congr rfl fun b _ => cycle_weight c a b

end Lax461425Proofs.PermanentBouquet
