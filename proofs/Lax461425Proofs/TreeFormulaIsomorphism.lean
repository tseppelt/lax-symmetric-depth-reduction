import Lax461425Proofs.TreeFormulaOperations

/-!
Isomorphisms of private-leaf formula trees. Reindexing the children of an unbounded sum or
product gives an isomorphism, allowing row and column permutations to act on the witness.
-/

namespace Lax461425Proofs.TreeFormulaIsomorphism

open Lax461425.Circuits Lax461425.MatrixSymmetry TreeFormulaCircuit TreeFormulaOperations
open scoped Classical

variable {V K : Type*}

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A parent-preserving formula-tree equivalence with variable renaming. -/
structure Iso (π : V → V) (T S : Tree V K) where
  equiv : T.Gate ≃ S.Gate
  label_eq : ∀ g, S.label (equiv g) = (T.label g).map π
  parent_eq : ∀ g, S.parent (equiv g) = (T.parent g).map equiv

/-- A tree self-isomorphism extends its variable renaming on the existing circuit model. -/
theorem extends_circuit {π : V → V} {T : Tree V K} (e : Iso π T T) :
    Extends (circuit T) e.equiv π := by
  change (∀ g : T.Gate, T.label (e.equiv g) = (T.label g).map π) ∧
    ∀ g h : T.Gate, (if T.parent (e.equiv h) = some (e.equiv g) then 1 else 0) =
      if T.parent h = some g then 1 else 0
  refine ⟨e.label_eq, ?_⟩
  intro g h
  rw [e.parent_eq]
  cases hp : T.parent h with
  | none => simp
  | some p => simp [e.equiv.injective.eq_iff]

/-- Variable leaves transform by the specified variable renaming. -/
def varIso (π : V → V) (x : V) : Iso π (varInput (K := K) x) (varInput (π x)) where
  equiv := Equiv.refl _
  label_eq _ := rfl
  parent_eq _ := rfl

/-- Constant leaves are unchanged. -/
def constIso (π : V → V) (c : K) : Iso π (constant (V := V) c) (constant c) where
  equiv := Equiv.refl _
  label_eq _ := rfl
  parent_eq _ := rfl

/-- A reindexing of isomorphic child formulas extends to the whole operation tree. -/
noncomputable def joinIso {I J : Type} [Fintype I] [Fintype J]
    (π : V → V) (T : I → Tree V K) (S : J → Tree V K)
    (e : I ≃ J) (h : ∀ i, Iso π (T i) (S (e i))) (mul : Bool) :
    Iso π (join T mul) (join S mul) where
  equiv := Equiv.sumCongr (Equiv.refl Unit) (Equiv.sigmaCongr e (fun i => (h i).equiv))
  label_eq g := by
    cases g with
    | inl u => cases mul <;> rfl
    | inr q => exact (h q.1).label_eq q.2
  parent_eq g := by
    cases g with
    | inl u => rfl
    | inr q =>
      rcases q with ⟨i, g⟩
      change joinParent S (.inr ⟨e i, (h i).equiv g⟩) =
        Option.map (Equiv.sumCongr (Equiv.refl Unit)
          (Equiv.sigmaCongr e (fun i => (h i).equiv))) (joinParent T (.inr ⟨i, g⟩))
      simp only [joinParent, (h i).parent_eq]
      cases (T i).parent g <;> rfl

end Lax461425Proofs.TreeFormulaIsomorphism
