import Lax461425.CircuitProperties
import Lax461425.MatrixSymmetry
import Lax461425.SymmetricFamilies

open Lax461425.CircuitProperties

/-!
---
title: Symmetric complexity classes and Boolean witnesses
type: definition
---
The symmetry and orbit definitions below allow a group to act jointly on matrix variables
and auxiliary variables. Orbits use every extending circuit automorphism. Polynomial
bounds allow a constant factor and use `n + 1`, including the zero-size matrix.
-/

namespace Lax461425.SymmetricClasses

open Circuits MatrixSymmetry SymmetricFamilies
open scoped Classical

/-- A polynomial bound, including finitely many exceptional indices. -/
def PolynomiallyBounded (q : ℕ → ℕ) : Prop :=
  ∃ c d : ℕ, ∀ n, q n ≤ c * (n + 1) ^ d

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

/-- Symmetric polynomial-orbit circuits. No degree or total-size bound is imposed. -/
def InSymVP {K : Type*} [CommSemiring K] (f : MatrixFamily K) : Prop :=
  InSymClass (fun _ _ => True) f

/-- Symmetric polynomial-orbit skew circuits. -/
def InSymVS {K : Type*} [CommSemiring K] (f : MatrixFamily K) : Prop :=
  InSymClass (fun _ C => IsSkew C) f

/-- Symmetric polynomial-orbit formulas. -/
def InSymVF {K : Type*} [CommSemiring K] (f : MatrixFamily K) : Prop :=
  InSymClass (fun _ C => IsFormula C) f

/-- Boolean-sum witnesses with polynomially many auxiliary variables and polynomial gate
orbits for the joint action. -/
def InBooleanClass {K : Type*} [CommSemiring K]
    (P : ∀ {V : Type}, Circuit V K → Prop) (f : MatrixFamily K) : Prop :=
  ∃ q b : ℕ → ℕ, PolynomiallyBounded q ∧ PolynomiallyBounded b ∧ ∀ n,
    ∃ (ρ : Γ n →* Equiv.Perm (Fin (q n)))
      (g : MvPolynomial ((Fin n × Fin n) ⊕ Fin (q n)) K)
      (C : Circuit ((Fin n × Fin n) ⊕ Fin (q n)) K),
      C.Computes g ∧ Symmetric (jointAction ρ) C ∧
      orbitSize (jointAction ρ) C ≤ b n ∧ P C ∧ boolSum g = f n

/-- The symmetric analogue of VNP. -/
def InSymVNP {K : Type*} [CommSemiring K] (f : MatrixFamily K) : Prop :=
  InBooleanClass (fun _ => True) f

/-- The formula-witness variant of symmetric VNP. -/
def InSymVNPFormula {K : Type*} [CommSemiring K] (f : MatrixFamily K) : Prop :=
  InBooleanClass (fun C => IsFormula C) f

end Lax461425.SymmetricClasses
