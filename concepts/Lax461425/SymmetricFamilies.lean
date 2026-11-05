import Lax461425.MatrixSymmetry
import Mathlib.Algebra.MvPolynomial.Rename

/-!
---
title: Symmetric polynomial families
type: definition
---
Families of polynomials in square matrix variables, their invariance under independent
row and column permutations, the joint action on matrix and auxiliary variables, and
Boolean sums over auxiliary variables.
-/

namespace Lax461425.SymmetricFamilies

open MatrixSymmetry
open scoped Classical

/-- A one-parameter family of polynomials in square matrix variables. -/
abbrev MatrixFamily (K : Type*) [CommSemiring K] :=
  ∀ n : ℕ, MvPolynomial (Fin n × Fin n) K

/-- Invariance under independent row and column permutations. -/
def MatrixInvariant {K : Type*} [CommSemiring K] {n : ℕ}
    (p : MvPolynomial (Fin n × Fin n) K) : Prop :=
  ∀ γ : Γ n, MvPolynomial.rename (actVar γ) p = p

/-- The permutation action on matrix variables. -/
def matrixAction (n : ℕ) : Γ n →* Equiv.Perm (Fin n × Fin n) where
  toFun γ := Equiv.prodCongr γ.1 γ.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The joint action on matrix and auxiliary variables. -/
def jointAction {n : ℕ} {Y : Type*} (ρ : Γ n →* Equiv.Perm Y) :
    Γ n →* Equiv.Perm ((Fin n × Fin n) ⊕ Y) where
  toFun γ := Equiv.sumCongr (matrixAction n γ) (ρ γ)
  map_one' := by ext x; cases x <;> simp [matrixAction]
  map_mul' γ δ := by ext x; cases x <;> simp [matrixAction]

/-- Sum over Boolean auxiliary assignments; distinct Booleans are counted separately even
in positive characteristic. -/
noncomputable def boolSum {X Y K : Type*} [Fintype Y] [CommSemiring K]
    (g : MvPolynomial (X ⊕ Y) K) : MvPolynomial X K :=
  ∑ e : Y → Bool, MvPolynomial.eval₂ MvPolynomial.C
    (Sum.elim MvPolynomial.X (fun y => MvPolynomial.C (if e y then 1 else 0))) g

end Lax461425.SymmetricFamilies
