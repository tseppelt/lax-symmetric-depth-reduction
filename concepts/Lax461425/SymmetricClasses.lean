import Lax461425.CircuitProperties
import Lax461425.MatrixSymmetry
import Lax461425.SymmetricFamilies

open Lax461425.CircuitProperties

/-!
---
title: Symmetric complexity classes
type: definition
---
Families computed by matrix-symmetric circuits with polynomially bounded gate orbits.
Polynomial bounds allow a constant factor and use `n + 1`, including the zero-size matrix.
-/

namespace Lax461425.SymmetricClasses

open Circuits MatrixSymmetry SymmetricFamilies

/-- A polynomial bound, including finitely many exceptional indices. -/
def PolynomiallyBounded (q : ℕ → ℕ) : Prop :=
  ∃ c d : ℕ, ∀ n, q n ≤ c * (n + 1) ^ d

/-- Polynomial gate-orbit witnesses satisfying an additional circuit property. -/
def InSymClass {K : Type*} [CommSemiring K]
    (P : ∀ n, Circuit (Fin n × Fin n) K → Prop) (f : MatrixFamily K) : Prop :=
  ∃ b : ℕ → ℕ, PolynomiallyBounded b ∧ ∀ n, ∃ C : Circuit (Fin n × Fin n) K,
    C.Computes (f n) ∧ IsMatrixSymmetric C ∧ MatrixSymmetry.orbitSize C ≤ b n ∧ P n C

/-- Symmetric polynomial-orbit circuits. No degree or total-size bound is imposed. -/
def InSymVP {K : Type*} [CommSemiring K] (f : MatrixFamily K) : Prop :=
  InSymClass (fun _ _ => True) f

/-- Symmetric polynomial-orbit skew circuits. -/
def InSymVS {K : Type*} [CommSemiring K] (f : MatrixFamily K) : Prop :=
  InSymClass (fun _ C => IsSkew C) f

/-- Symmetric polynomial-orbit formulas. -/
def InSymVF {K : Type*} [CommSemiring K] (f : MatrixFamily K) : Prop :=
  InSymClass (fun _ C => IsFormula C) f

end Lax461425.SymmetricClasses
