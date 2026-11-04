import Lax461425.SymmetricFamilies
import Lax461425.BooleanSumSymmetry
import Lax461425Proofs.CircuitFacts

/-!
Boolean-cube summation and the matrix-symmetry observation of Section 7. Auxiliary
assignments are reindexed by a genuine equivalence of Boolean functions.
-/

namespace Lax461425Proofs.BooleanWitnesses

universe u

open Lax461425.SymmetricFamilies Lax461425.MatrixSymmetry Lax461425.Circuits
open scoped Classical

variable {X Y K : Type*} [Fintype Y] [CommSemiring K]

/-- Precomposition by a permutation reindexes Boolean assignments bijectively. -/
def assignmentEquiv (τ : Equiv.Perm Y) : (Y → Bool) ≃ (Y → Bool) where
  toFun e y := e (τ y)
  invFun e y := e (τ.symm y)
  left_inv e := by funext y; simp
  right_inv e := by funext y; simp

/-- Simultaneous permutation of the free and Boolean variables commutes with Boolean
summation, with only the free-variable permutation remaining. -/
theorem boolSum_rename (π : Equiv.Perm X) (τ : Equiv.Perm Y)
    (g : MvPolynomial (X ⊕ Y) K) :
    boolSum (MvPolynomial.rename (Equiv.sumCongr π τ) g) =
      MvPolynomial.rename π (boolSum g) := by
  let a (e : Y → Bool) : X ⊕ Y → MvPolynomial X K :=
    Sum.elim MvPolynomial.X (fun y => MvPolynomial.C (if e y then 1 else 0))
  have hterm (e : Y → Bool) :
      MvPolynomial.eval₂ MvPolynomial.C (a e)
          (MvPolynomial.rename (Equiv.sumCongr π τ) g) =
        MvPolynomial.rename π (MvPolynomial.eval₂ MvPolynomial.C
          (a (assignmentEquiv τ e)) g) := by
    rw [MvPolynomial.eval₂_rename]
    change _ = (MvPolynomial.rename π).toRingHom
      (MvPolynomial.eval₂ MvPolynomial.C (a (assignmentEquiv τ e)) g)
    rw [MvPolynomial.eval₂_comp_left]
    congr 1
    · ext c
      simp
    · funext z
      cases z <;> simp [a, assignmentEquiv]
  simp only [boolSum, map_sum]
  change (∑ e : Y → Bool, MvPolynomial.eval₂ MvPolynomial.C (a e)
    (MvPolynomial.rename (Equiv.sumCongr π τ) g)) = _
  simp_rw [hterm]
  exact Equiv.sum_comp (assignmentEquiv τ)
    (fun e => MvPolynomial.rename π (MvPolynomial.eval₂ MvPolynomial.C (a e) g))

/-- Boolean summation is independent of the chosen finite indexing type of the auxiliary
variables. This permits witnesses to use `Fin q` in the family definition. -/
theorem boolSum_rename_auxEquiv {Z : Type*} [Fintype Z] (τ : Y ≃ Z)
    (g : MvPolynomial (X ⊕ Y) K) :
    boolSum (MvPolynomial.rename (Equiv.sumCongr (Equiv.refl X) τ) g) = boolSum g := by
  let reindex : (Z → Bool) ≃ (Y → Bool) :=
    { toFun := fun e y => e (τ y)
      invFun := fun e z => e (τ.symm z)
      left_inv := by intro e; funext z; simp
      right_inv := by intro e; funext y; simp }
  have hterm (e : Z → Bool) :
      MvPolynomial.eval₂ MvPolynomial.C
        (Sum.elim MvPolynomial.X (fun z => MvPolynomial.C (if e z then 1 else 0)))
        (MvPolynomial.rename (Equiv.sumCongr (Equiv.refl X) τ) g) =
      MvPolynomial.eval₂ MvPolynomial.C
        (Sum.elim MvPolynomial.X (fun y => MvPolynomial.C (if reindex e y then 1 else 0))) g := by
    rw [MvPolynomial.eval₂_rename]
    congr 1
    funext v
    cases v <;> rfl
  simp only [boolSum]
  simp_rw [hterm]
  exact Equiv.sum_comp reindex
    (fun e => MvPolynomial.eval₂ MvPolynomial.C
      (Sum.elim MvPolynomial.X (fun y => MvPolynomial.C (if e y then 1 else 0))) g)

/-- A joint invariant polynomial has a matrix-invariant Boolean sum. -/
theorem matrixInvariant_boolSum {n : ℕ} (ρ : Γ n →* Equiv.Perm Y)
    (g : MvPolynomial ((Fin n × Fin n) ⊕ Y) K)
    (hg : ∀ γ : Γ n, MvPolynomial.rename (jointAction ρ γ) g = g) :
    MatrixInvariant (boolSum g) := by
  intro γ
  have h := boolSum_rename (matrixAction n γ) (ρ γ) g
  change boolSum (MvPolynomial.rename (jointAction ρ γ) g) =
    MvPolynomial.rename (actVar γ) (boolSum g) at h
  rw [hg γ] at h
  exact h.symm

/-- Observation 7.2: a jointly symmetric circuit witness has a matrix-invariant Boolean
sum. -/
theorem invariant_of_symmetric_witness {n : ℕ} (ρ : Γ n →* Equiv.Perm Y)
    (C : Circuit ((Fin n × Fin n) ⊕ Y) K)
    (g : MvPolynomial ((Fin n × Fin n) ⊕ Y) K) (hg : C.Computes g)
    (hC : Symmetric (jointAction ρ) C) : MatrixInvariant (boolSum g) := by
  apply matrixInvariant_boolSum ρ g
  intro γ
  obtain ⟨σ, hσ⟩ := hC γ
  exact CircuitFacts.rename_eq_of_computes_of_extends hg hσ

/--
---
conclusion: Lax461425.BooleanSumSymmetry.matrixInvariant_of_mem
---
Every polynomial in a symmetric VNP family is matrix-invariant.
-/
theorem matrixInvariant_of_mem {K : Type u} [CommSemiring K]
    (f : MatrixFamily K) (hf : InSymVNP f) (n : ℕ) :
    MatrixInvariant (f n) := by
  obtain ⟨q, b, hq, hb, hw⟩ := hf
  obtain ⟨ρ, g, C, hcomp, hsym, horbit, htrue, heq⟩ := hw n
  rw [← heq]
  exact invariant_of_symmetric_witness ρ C g hcomp hsym

/-- The easy inclusion in Corollary 7.4: formula witnesses are circuit witnesses. -/
theorem mem_of_formula_witnesses (f : MatrixFamily K) (hf : InSymVNPFormula f) :
    InSymVNP f := by
  obtain ⟨q, b, hq, hb, hw⟩ := hf
  refine ⟨q, b, hq, hb, ?_⟩
  intro n
  obtain ⟨ρ, g, C, hcomp, hsym, horbit, _, heq⟩ := hw n
  exact ⟨ρ, g, C, hcomp, hsym, horbit, trivial, heq⟩

end Lax461425Proofs.BooleanWitnesses
