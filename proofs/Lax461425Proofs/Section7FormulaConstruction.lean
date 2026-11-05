import Lax461425.SymmetricVNPCharacterisation
import Lax461425.FormulaWitnessEquivalence
import Lax461425.CircuitProperties
import Lax461425Proofs.TaggedPatternFormula
import Lax461425Proofs.PatternFormulaCard
import Lax461425Proofs.FormulaTags
import Lax461425Proofs.ComputedFormulaOrbit
import Lax461425Proofs.Section7Padding
import Mathlib.Algebra.CharZero.Infinite

open Lax461425.CircuitProperties

/-!
The complete formula construction for Section 7.1. Homomorphism spanning and the internally
proved isolated-vertex padding enter through `Section7Padding`; every formula
gate, automorphism and orbit bound is constructed and proved in the new proof modules.
-/

namespace Lax461425Proofs.Section7FormulaConstruction

universe u

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies
open Lax461425.SymmetricClasses
open TreeFormulaCircuit TreeFormulaOperations TreeFormulaOrbit ComputedFormula
open PatternFormulaBlocks TaggedPatternFormula FormulaTags
open scoped Classical

variable {K : Type*} [Field K] {n : ℕ}

theorem tagged_block_orbitSize_le (hn : 1 ≤ n) (m : Fin n → Fin n → ℕ)
    (b : BlockIndex m) (t : K) :
    orbitSize (jointAction (auxAction n)) (circuit (tag t (block (K := K) m b)).tree) ≤ 4 * n ^ 2 := by
  apply TreeFormulaOrbit.orbitSize_le_of_kind_bound
  intro q
  cases b with
  | inl v => exact PatternFormulaCard.tagged_selector_kind_bound n hn v t q
  | inr e => exact PatternFormulaCard.tagged_edge_kind_bound n hn e.1 e.2.1 t q

theorem pattern_orbitSize_le (hn : 1 ≤ n) (m : Fin n → Fin n → ℕ)
    (t : BlockIndex m → K) (ht : GoodTags (block (K := K) m) t) :
    orbitSize (jointAction (auxAction n)) (circuit (patternFormula m t).tree) ≤ 4 * n ^ 2 := by
  apply FormulaTags.orbit_bound (jointAction (auxAction n)) (block m) t ht true (4 * n ^ 2)
  · have hsq : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
    omega
  · intro b
    exact tagged_block_orbitSize_le hn m b (t b)

theorem pattern_root_noninput (m : Fin n → Fin n → ℕ) (t : BlockIndex m → K) :
    ¬ ((patternFormula m t).tree.label (patternFormula m t).tree.out).IsInput := by
  change ¬ (GateLabel.mul : GateLabel (Variables n) K).IsInput
  simp [GateLabel.IsInput]

theorem combination_orbitSize_le {R : Type} [Fintype R] (hn : 1 ≤ n)
    (c : R → K) (m : R → Fin n → Fin n → ℕ) (t : ∀ r, BlockIndex (m r) → K)
    (s : R → K) (ht : ∀ r, GoodTags (block (K := K) (m r)) (t r))
    (hs : GoodTags (fun r => mul (const (c r)) (patternFormula (m r) (t r))) s) :
    orbitSize (jointAction (auxAction n)) (circuit (combinationFormula c m t s).tree) ≤ 4 * n ^ 2 := by
  have hB : 1 ≤ 4 * n ^ 2 := by
    have hsq : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
    omega
  apply FormulaTags.orbit_bound (jointAction (auxAction n))
    (fun r => mul (const (c r)) (patternFormula (m r) (t r))) s hs false (4 * n ^ 2) hB
  intro r
  apply ComputedFormulaOrbit.tag_orbitSize_le (jointAction (auxAction n)) (s r)
    (mul (const (c r)) (patternFormula (m r) (t r)))
  · change ¬ (GateLabel.mul : GateLabel (Variables n) K).IsInput
    simp [GateLabel.IsInput]
  · exact hB
  · exact ComputedFormulaOrbit.mul_const_orbitSize_le (jointAction (auxAction n)) (c r)
      (patternFormula (m r) (t r)) (pattern_root_noninput _ _) (4 * n ^ 2) hB
      (pattern_orbitSize_le hn (m r) (t r) (ht r))

variable [CharZero K]

/-- Positive-order matrix-invariant polynomials have an actual formula witness with the
paper's exact gate-orbit bound and the common square auxiliary-variable set. -/
theorem square_formula_witness (hn : 1 ≤ n) (p : MvPolynomial (Fin n × Fin n) K)
    (hp : MatrixInvariant p) :
    ∃ (ρ : Γ n →* Equiv.Perm (Aux n))
      (g : MvPolynomial (Variables n) K) (C : Circuit (Variables n) K),
      C.Computes g ∧ Symmetric (jointAction ρ) C ∧
      orbitSize (jointAction ρ) C ≤ 4 * n ^ 2 ∧ IsFormula C ∧ boolSum g = p := by
  obtain ⟨r, c, m, hpcomb⟩ := Section7Padding.finite_square_combination hn p hp
  choose t ht using (fun i : Fin r => FormulaTags.exists_goodTags (block (K := K) (m i)))
  obtain ⟨s, hs⟩ := FormulaTags.exists_goodTags
    (fun i : Fin r => mul (const (c i)) (patternFormula (m i) (t i)))
  let F := combinationFormula c m t s
  refine ⟨auxAction n, polynomial F, circuit F.tree, ComputedFormula.computes F,
    symmetric_combinationFormula c m t s, combination_orbitSize_le hn c m t s ht hs,
    ComputedFormula.isFormula F, ?_⟩
  exact (boolSum_combinationFormula c m t s (fun i => (ht i).nonzero) hs.nonzero).trans hpcomb.symm

/--
---
conclusion: Lax461425.SymmetricFormulaWitness.formula_witness
---
The same witness with auxiliary variables indexed by exactly `Fin (2n²)`.
-/
theorem formula_witness {K : Type u} [Field K] [CharZero K] {n : ℕ}
    (hn : 1 ≤ n) (p : MvPolynomial (Fin n × Fin n) K)
    (hp : MatrixInvariant p) :
    ∃ (ρ : Γ n →* Equiv.Perm (Fin (2 * n ^ 2)))
      (g : MvPolynomial ((Fin n × Fin n) ⊕ Fin (2 * n ^ 2)) K)
      (C : Circuit ((Fin n × Fin n) ⊕ Fin (2 * n ^ 2)) K),
      C.Computes g ∧ Symmetric (jointAction ρ) C ∧
      orbitSize (jointAction ρ) C ≤ 4 * n ^ 2 ∧ IsFormula C ∧ boolSum g = p :=
  Section7Assembly.positive_witness_reindex p (square_formula_witness hn p hp)

/--
---
conclusion: Lax461425.SymmetricVNPCharacterisation.all_matrix_symmetric_iff
---
Theorem 7.3, including the zero-order matrix case in the family classes.
-/
theorem all_matrix_symmetric_iff (f : MatrixFamily K) :
    InSymVNP f ↔ ∀ n, MatrixInvariant (f n) := by
  constructor
  · exact Lax461425.BooleanSumSymmetry.matrixInvariant_of_mem f
  · intro hf
    apply BooleanWitnesses.mem_of_formula_witnesses f
    exact Section7Assembly.family_of_positive f
      (fun n hn => Lax461425.SymmetricFormulaWitness.formula_witness hn (f n) (hf n))

/--
---
conclusion: Lax461425.FormulaWitnessEquivalence.formula_witnesses_iff
---
Corollary 7.4: circuit and formula witnesses give exactly the same class.
-/
theorem formula_witnesses_iff (f : MatrixFamily K) : InSymVNP f ↔ InSymVNPFormula f := by
  constructor
  · intro hf
    exact Section7Assembly.family_of_positive f
      (fun n hn => Lax461425.SymmetricFormulaWitness.formula_witness hn (f n)
        (Lax461425.BooleanSumSymmetry.matrixInvariant_of_mem f hf n))
  · exact BooleanWitnesses.mem_of_formula_witnesses f

end Lax461425Proofs.Section7FormulaConstruction
