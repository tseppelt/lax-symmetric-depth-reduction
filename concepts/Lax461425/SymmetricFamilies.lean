import Lax461425.CircuitProperties
import Lax461425.MatrixSymmetry
import Mathlib.Algebra.MvPolynomial.Rename

open Lax461425.CircuitProperties

/-!
---
title: Symmetric polynomial families and Boolean witnesses
type: definition
---
The symmetry and orbit definitions below allow a group to act jointly on matrix variables
and auxiliary variables. Orbits use every extending circuit automorphism. Polynomial
bounds allow a constant factor and use `n + 1`, including the zero-size matrix.
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

/-- The joint action on matrix and auxiliary variables. -/
def jointAction {n : ℕ} {Y : Type*} (ρ : Γ n →* Equiv.Perm Y) :
    Γ n →* Equiv.Perm ((Fin n × Fin n) ⊕ Y) where
  toFun γ := Equiv.sumCongr (matrixAction n γ) (ρ γ)
  map_one' := by ext x; cases x <;> simp [matrixAction]
  map_mul' γ δ := by ext x; cases x <;> simp [matrixAction]

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

/-- Sum over Boolean auxiliary assignments; distinct Booleans are counted separately even
in positive characteristic. -/
noncomputable def boolSum {X Y K : Type*} [Fintype Y] [CommSemiring K]
    (g : MvPolynomial (X ⊕ Y) K) : MvPolynomial X K :=
  ∑ e : Y → Bool, MvPolynomial.eval₂ MvPolynomial.C
    (Sum.elim MvPolynomial.X (fun y => MvPolynomial.C (if e y then 1 else 0))) g

/-- Polynomial gate-orbit witnesses satisfying an additional circuit property. -/
def InSymClass {K : Type*} [CommSemiring K]
    (P : ∀ n, Circuit (Fin n × Fin n) K → Prop) (f : MatrixFamily K) : Prop :=
  ∃ b : ℕ → ℕ, PolynomiallyBounded b ∧ ∀ n, ∃ C : Circuit (Fin n × Fin n) K,
    C.Computes (f n) ∧ IsMatrixSymmetric C ∧ MatrixSymmetry.orbitSize C ≤ b n ∧ P n C

/-- Symmetric polynomial-orbit circuits. No degree or total-size bound is imposed. -/
def InSymVP {K : Type*} [CommSemiring K] (f : MatrixFamily K) : Prop :=
  InSymClass (fun _ C => (InputsIdentified C)) f

/-- Symmetric polynomial-orbit skew circuits. -/
def InSymVS {K : Type*} [CommSemiring K] (f : MatrixFamily K) : Prop :=
  InSymClass (fun _ C => (IsSkew C) ∧ (InputsIdentified C)) f

/-- Symmetric polynomial-orbit formulas with shared input gates. -/
def InSymVF {K : Type*} [CommSemiring K] (f : MatrixFamily K) : Prop :=
  InSymClass (fun _ C => (IsFormula C) ∧ (InputsIdentified C)) f

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
  InBooleanClass CircuitProperties.InputsIdentified f

/-- The formula-witness variant of symmetric VNP. -/
def InSymVNPFormula {K : Type*} [CommSemiring K] (f : MatrixFamily K) : Prop :=
  InBooleanClass (fun C => (IsFormula C) ∧ (InputsIdentified C)) f

end Lax461425.SymmetricFamilies
