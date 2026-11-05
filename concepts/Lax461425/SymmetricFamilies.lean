import Lax461425.MatrixSymmetry
import Mathlib.Algebra.MvPolynomial.Rename

/-!
---
title: Symmetric polynomial families
type: definition
---
Polynomials and families of polynomials in square matrix variables, and their invariance
under independent row and column permutations.
-/

namespace Lax461425.SymmetricFamilies

open MatrixSymmetry

/-- Polynomials in the variables of an `n × n` matrix. -/
abbrev MatrixPolynomial (n : ℕ) (K : Type*) [CommSemiring K] :=
  MvPolynomial (Fin n × Fin n) K

/-- A one-parameter family of polynomials in square matrix variables. -/
abbrev MatrixFamily (K : Type*) [CommSemiring K] :=
  ∀ n : ℕ, MatrixPolynomial n K

/-- Invariance under independent row and column permutations. -/
def MatrixInvariant {K : Type*} [CommSemiring K] {n : ℕ} (p : MatrixPolynomial n K) : Prop :=
  ∀ γ : Γ n, MvPolynomial.rename (actVar γ) p = p

end Lax461425.SymmetricFamilies
