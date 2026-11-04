import Lax461425.CircuitProperties
import Lax461425Proofs.Section6Characterisation
import Lax461425Proofs.PermanentProjection
import Lax461425Proofs.PatternBooleanWitness
import Lax461425Proofs.Section7Assembly
import Lax461425Proofs.Section7FormulaConstruction
import Mathlib.Data.ZMod.Basic

open Lax461425.CircuitProperties

/-!
Small mathematical scenarios for Sections 6 and 7: positive characteristic, constants,
an isolated pattern vertex, parallel edges, and the zero-size Boolean formula witness.
These checks instantiate the independently proved theorems, never the concept axioms.
-/

namespace Lax461425Proofs.Sections67Examples

open Lax461425.HomomorphismPolynomials Lax461425.SymmetricABPs
open Lax461425.SymmetricFamilies Lax461425.Permanent
open scoped Classical

example : InSymVNP (polynomial (ZMod 2)) := Permanent.permanent_membership (ZMod 2)

example (n : ℕ) (c : ℚ) :
    IsSymmetricProjection (matrixAction n) (MvPolynomial.C c) :=
  Permanent.constant_projection (matrixAction n) c

example (n : ℕ) : IsSymmetricProjection (matrixAction n)
    (0 : MvPolynomial (Fin n × Fin n) ℚ) := by
  simpa using Permanent.constant_projection (matrixAction n) (0 : ℚ)

example (f : MatrixFamily ℚ) : InSymVBP f ↔ InSymVS f :=
  Section6Characterisation.equivalence f

/-- Off the Boolean cube, duplicating the paper's pair factor would give `125`. -/
example (v : PatternFormulaBlocks.Vertex 2) :
    MvPolynomial.eval
      (Sum.elim (fun _ => 0) (fun y => if y.2 = 0 then (2 : ℚ) else 3))
      (ComputedFormula.polynomial (PatternFormulaBlocks.selector 2 v)) = -25 := by
  rw [PatternFormulaBlocks.polynomial_selector]
  norm_num [Fin.sum_univ_two, Fin.prod_univ_two, Finset.prod_filter]

/-- One isolated left vertex and no right vertices. -/
def isolated : Pattern where
  A := Unit
  B := Empty
  mult _ b := Empty.elim b

/-- Its one-vertex full bag has width zero. -/
noncomputable def isolatedDecomposition : PaddedPathDecomposition isolated 0 :=
  { SymmetricPathDecomposition.fullBag isolated with
    card_bag_le := by
      intro i
      change (if i.val = 1 then (Finset.univ : Finset (Unit ⊕ Empty)) else ∅).card ≤ 1
      split_ifs <;> simp }

example : ∃ G : ABP (Fin 1 × Fin 1) ℕ,
    G.Computes (hom ℕ isolated 1) ∧ G.IsMatrixSymmetric ∧ G.orbitSize ≤ 1 := by
  obtain ⟨_, hpad⟩ := Section6ABPForPatterns.exists_abp (K := ℕ) (n := 1) (k := 0)
    (by decide) isolated
    (SymmetricPathDecomposition.pathwidthLE_iff.2 ⟨isolatedDecomposition⟩)
  obtain ⟨G, hcomp, hsym, hbound, _⟩ := hpad 0
  exact ⟨G, hcomp, hsym, by simpa using hbound⟩

example : boolSum (PatternBooleanWitness.witness (K := ℚ) isolated 2) =
    MvPolynomial.C (2 : ℚ) := by
  rw [PatternBooleanWitness.boolSum_witness]
  change (∑ hA : Unit → Fin 2, ∑ hB : Empty → Fin 2,
    ∏ a : Unit, ∏ b : Empty,
      (MvPolynomial.X (hA a, hB b) : MvPolynomial (Fin 2 × Fin 2) ℚ) ^
        (Empty.elim b)) = _
  simp
  exact (MvPolynomial.C_eq_coe_nat 2).symm

/-- Three parallel edges at the first left vertex, and a second isolated left vertex. -/
def parallelWithIsolate : Pattern where
  A := Fin 2
  B := Unit
  mult a _ := if a = 0 then 3 else 0

example :
    boolSum (PatternBooleanWitness.witness (K := ℚ) parallelWithIsolate 1) =
      (MvPolynomial.X (0, 0) : MvPolynomial (Fin 1 × Fin 1) ℚ) ^ 3 := by
  rw [PatternBooleanWitness.boolSum_witness]
  change (∑ hA : Fin 2 → Fin 1, ∑ hB : Unit → Fin 1,
    ∏ a : Fin 2, ∏ b : Unit,
      (MvPolynomial.X (hA a, hB b) : MvPolynomial (Fin 1 × Fin 1) ℚ) ^
        (if a = 0 then 3 else 0)) = _
  simp

example : ∃ (ρ : Lax461425.MatrixSymmetry.Γ 0 →* Equiv.Perm (Fin 0))
    (g : MvPolynomial ((Fin 0 × Fin 0) ⊕ Fin 0) ℚ)
    (C : Lax461425.Circuits.Circuit ((Fin 0 × Fin 0) ⊕ Fin 0) ℚ),
    C.Computes g ∧ Symmetric (jointAction ρ) C ∧
      orbitSize (jointAction ρ) C ≤ 1 ∧ (IsFormula C) ∧ (InputsIdentified C) ∧ boolSum g = 0 :=
  Section7Assembly.zero_formula_witness ℚ 0

example (p : MvPolynomial (Fin 1 × Fin 1) ℚ) :
    ∃ (ρ : Lax461425.MatrixSymmetry.Γ 1 →* Equiv.Perm (Fin 2))
      (g : MvPolynomial ((Fin 1 × Fin 1) ⊕ Fin 2) ℚ)
      (C : Lax461425.Circuits.Circuit ((Fin 1 × Fin 1) ⊕ Fin 2) ℚ),
      C.Computes g ∧ Symmetric (jointAction ρ) C ∧
      orbitSize (jointAction ρ) C ≤ 4 ∧ (IsFormula C) ∧ (InputsIdentified C) ∧ boolSum g = p := by
  have hp : MatrixInvariant p := by
    intro γ
    have he : Lax461425.MatrixSymmetry.actVar γ = id := by
      funext x
      exact @Subsingleton.elim (Fin 1 × Fin 1) inferInstance _ _
    simp [he]
  simpa using Section7FormulaConstruction.formula_witness (by decide : 1 ≤ 1) p hp

end Lax461425Proofs.Sections67Examples
