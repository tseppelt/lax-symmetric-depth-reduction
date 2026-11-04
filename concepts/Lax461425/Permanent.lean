import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.MvPolynomial.Rename
import Lax461425.MatrixSymmetry

/-!
---
title: Permanent polynomials and symmetric projections
type: definition
---
The permanent polynomial and the symmetric affine projections of Section 7.3. The order of
the source permanent is deliberately unrestricted: no polynomial size bound is asserted.
-/

namespace Lax461425.Permanent

open MatrixSymmetry

/-- The permanent polynomial on an `n × n` variable matrix. -/
noncomputable def polynomial (K : Type*) [CommSemiring K] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) K :=
  Matrix.permanent (fun i j => MvPolynomial.X (i, j))

/-- An affine linear polynomial, given by a constant and finitely many variable coefficients. -/
def IsAffine {V K : Type*} [CommSemiring K] (p : MvPolynomial V K) : Prop :=
  ∃ (c : K) (s : Finset V) (a : V → K),
    p = MvPolynomial.C c + ∑ v ∈ s, MvPolynomial.C (a v) * MvPolynomial.X v

/-- A symmetric affine projection of a permanent, with no restriction on the source order.
The finite index type is nonempty, corresponding to source order at least one. -/
def IsSymmetricProjection {V G K : Type*} [Group G] [CommSemiring K]
    (ρ : G →* Equiv.Perm V) (p : MvPolynomial V K) : Prop :=
  ∃ (A : Type) (_ : Fintype A) (_ : DecidableEq A) (_ : Nonempty A)
      (M : Matrix A A (MvPolynomial V K)),
    p = Matrix.permanent M ∧ (∀ i j, IsAffine (M i j)) ∧
      ∀ γ, ∃ α β : Equiv.Perm A,
        ∀ i j, M (α i) (β j) = MvPolynomial.rename (ρ γ) (M i j)

end Lax461425.Permanent
