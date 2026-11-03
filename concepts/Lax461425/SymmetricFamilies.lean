import Lax461425.CircuitProperties
import Lax461425.MatrixSymmetry
import Lax461425.InputSharing
import Mathlib.Algebra.MvPolynomial.Rename

open Lax461425.CircuitProperties

/-!
---
title: Symmetric polynomial families
type: definition
---
Matrix-symmetric polynomial families and polynomial gate-orbit bounds. Orbits use every
extending circuit automorphism. Polynomial bounds allow a constant factor and use
`n + 1`, including the zero-size matrix.
-/

namespace Lax461425.SymmetricFamilies

open Circuits MatrixSymmetry
open scoped Classical

/-- A polynomial bound, including finitely many exceptional indices. -/
def PolynomiallyBounded (q : ℕ → ℕ) : Prop :=
  ∃ c d : ℕ, ∀ n, q n ≤ c * (n + 1) ^ d

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

/-- Every element of the acting group extends to a circuit automorphism. -/
def Symmetric {G V K : Type*} [Group G] (ρ : G →* Equiv.Perm V)
    (C : Circuit V K) : Prop :=
  ∀ γ : G, ∃ σ : C.Gate ≃ C.Gate, Extends C σ (ρ γ)

/-- Orbit under all automorphisms extending some element of the acting group. -/
def orbit {G V K : Type*} [Group G] (ρ : G →* Equiv.Perm V)
    (C : Circuit V K) (g : C.Gate) : Set C.Gate :=
  {g' | ∃ (γ : G) (σ : C.Gate ≃ C.Gate), Extends C σ (ρ γ) ∧ σ g = g'}

/-- The largest gate orbit for a specified variable action. -/
noncomputable def orbitSize {G V K : Type*} [Group G] (ρ : G →* Equiv.Perm V)
    (C : Circuit V K) : ℕ :=
  Finset.univ.sup fun g => (orbit ρ C g).ncard

/-- Polynomial gate-orbit witnesses satisfying an additional circuit property. -/
def InSymClass {K : Type*} [CommSemiring K]
    (P : ∀ n, Circuit (Fin n × Fin n) K → Prop) (f : MatrixFamily K) : Prop :=
  ∃ b : ℕ → ℕ, PolynomiallyBounded b ∧ ∀ n, ∃ C : Circuit (Fin n × Fin n) K,
    C.Computes (f n) ∧ IsMatrixSymmetric C ∧ MatrixSymmetry.orbitSize C ≤ b n ∧ P n C

/-- Symmetric polynomial-orbit skew circuits. -/
def InSymVS {K : Type*} [CommSemiring K] (f : MatrixFamily K) : Prop :=
  InSymClass (fun _ C => (IsSkew C) ∧ (InputsIdentified C)) f

end Lax461425.SymmetricFamilies
