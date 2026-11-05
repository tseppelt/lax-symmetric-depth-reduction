import Lax461425Proofs.TreeFormulaCircuit

/-!
Concrete private-leaf trees and unbounded addition/product nodes. Their finite gate types
are disjoint unions, so identical subexpressions retain distinct occurrences.
-/

namespace Lax461425Proofs.TreeFormulaOperations

open Lax461425.Circuits TreeFormulaCircuit
open scoped Classical

variable {V K : Type*}

/-- A private occurrence of a variable input. -/
def varInput (x : V) : Tree V K where
  Gate := Unit
  label _ := .var x
  parent _ := none
  out := ()
  rank _ := 0
  parent_out := rfl
  parent_exists g hg := False.elim (hg (Subsingleton.elim _ _))
  rank_parent _ _ h := by cases h
  input_leaf _ _ _ h := by cases h

/-- A private occurrence of a constant input. -/
def constant (c : K) : Tree V K where
  Gate := Unit
  label _ := .const c
  parent _ := none
  out := ()
  rank _ := 0
  parent_out := rfl
  parent_exists g hg := False.elim (hg (Subsingleton.elim _ _))
  rank_parent _ _ h := by cases h
  input_leaf _ _ _ h := by cases h

variable {I : Type} [Fintype I] (T : I → Tree V K)

/-- Distinct occurrences of all child gates, together with one new operation root. -/
abbrev JoinGate := Unit ⊕ (Σ i : I, (T i).Gate)

private noncomputable def maxRank : ℕ :=
  Finset.univ.sup fun i => Finset.univ.sup (T i).rank

private theorem rank_le_maxRank (i : I) (g : (T i).Gate) :
    (T i).rank g ≤ maxRank T := by
  exact (Finset.le_sup (f := (T i).rank) (Finset.mem_univ g)).trans
    (Finset.le_sup (f := fun j => Finset.univ.sup (T j).rank) (Finset.mem_univ i))

/-- Parent map: the old roots become children of the new operation root. -/
noncomputable def joinParent : JoinGate T → Option (JoinGate T)
  | .inl _ => none
  | .inr ⟨i, g⟩ =>
      match (T i).parent g with
      | none => some (.inl ())
      | some p => some (.inr ⟨i, p⟩)

/-- An unbounded operation root, addition for `false`, multiplication for `true`. -/
@[reducible] noncomputable def join (mul : Bool) : Tree V K where
  Gate := JoinGate T
  label
    | .inl _ => if mul then .mul else .add
    | .inr ⟨i, g⟩ => (T i).label g
  parent := joinParent T
  out := .inl ()
  rank
    | .inl _ => maxRank T + 1
    | .inr ⟨i, g⟩ => (T i).rank g
  parent_out := rfl
  parent_exists g hg := by
    cases g with
    | inl u => exact False.elim (hg (by cases u; rfl))
    | inr p =>
      rcases p with ⟨i, g⟩
      cases hp : (T i).parent g with
      | none => exact ⟨.inl (), by simp [joinParent, hp]⟩
      | some p => exact ⟨.inr ⟨i, p⟩, by simp [joinParent, hp]⟩
  rank_parent g p hgp := by
    cases g with
    | inl u => cases hgp
    | inr q =>
      rcases q with ⟨i, g⟩
      cases hp : (T i).parent g with
      | none =>
        simp only [joinParent, hp, Option.some.injEq] at hgp
        subst p
        exact Nat.lt_succ_of_le (rank_le_maxRank T i g)
      | some p' =>
        simp only [joinParent, hp, Option.some.injEq] at hgp
        subst p
        exact (T i).rank_parent g p' hp
  input_leaf g h hg := by
    cases g with
    | inl u => cases mul <;> exact False.elim hg
    | inr q =>
      rcases q with ⟨i, g⟩
      cases h with
      | inl u => intro hh; cases hh
      | inr q =>
        rcases q with ⟨j, h⟩
        cases hp : (T j).parent h with
        | none => simp [joinParent, hp]
        | some p =>
          intro hh
          simp only [joinParent, hp, Option.some.injEq, Sum.inr.injEq] at hh
          cases hh
          exact (T i).input_leaf g h hg hp

end Lax461425Proofs.TreeFormulaOperations
