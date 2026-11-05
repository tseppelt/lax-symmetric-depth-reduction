import Lax461425Proofs.PatternFormulaSymmetry
import Lax461425Proofs.Section7Assembly

/-!
An actual tagged private-leaf formula for a homomorphism-polynomial Boolean witness. Each
edge occurrence and each pattern vertex receives its own tagged block. All blocks use the
same `2n²` auxiliary variables, and parallel edges retain separate formula occurrences.
-/

namespace Lax461425Proofs.TaggedPatternFormula

open Lax461425.HomomorphismPolynomials Lax461425Proofs.PatternPadding
open Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies Lax461425.SymmetricClasses
open Lax461425.SymmetricVNP
open ComputedFormula PatternFormulaBlocks PatternFormulaSymmetry TreeFormulaIsomorphism
open BooleanSelectors
open scoped Classical

variable {K : Type*} [Field K] {n : ℕ}

abbrev EdgeIndex (m : Fin n → Fin n → ℕ) := Σ a : Fin n, Σ b : Fin n, Fin (m a b)
abbrev BlockIndex (m : Fin n → Fin n → ℕ) := Vertex n ⊕ EdgeIndex m

/-- The untagged core at each fixed pattern vertex or edge occurrence. -/
noncomputable def block (m : Fin n → Fin n → ℕ) : BlockIndex m → Formula (Variables n) K
  | .inl v => selector n v
  | .inr ⟨a, b, _⟩ => edge n a b

/-- One product root combines all individually tagged blocks. -/
noncomputable def patternFormula (m : Fin n → Fin n → ℕ) (t : BlockIndex m → K) :
    Formula (Variables n) K := op true (fun b => tag (t b) (block m b))

theorem polynomial_patternFormula (m : Fin n → Fin n → ℕ) (t : BlockIndex m → K)
    (ht : ∀ b, t b ≠ 0) :
    polynomial (patternFormula m t) =
      (∏ v : Vertex n, polynomial (selector (K := K) n v)) *
        ∏ a, ∏ b, polynomial (edge (K := K) n a b) ^ m a b := by
  simp only [patternFormula, polynomial_op, ↓reduceIte]
  simp_rw [polynomial_tag _ (ht _) _]
  rw [Fintype.prod_sum_type]
  simp only [block, Fintype.prod_sigma, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The tagged formula computes exactly the paper's explicit witness polynomial. -/
theorem polynomial_patternFormula_eq_witness (m : Fin n → Fin n → ℕ)
    (t : BlockIndex m → K) (ht : ∀ b, t b ≠ 0) :
    polynomial (patternFormula m t) =
      PatternBooleanWitness.witness (K := K) (squarePattern n m) n := by
  rw [polynomial_patternFormula m t ht]
  simp only [polynomial_selector, polynomial_edge, PatternBooleanWitness.witness,
    PatternBooleanWitness.vertexSelector, PatternBooleanWitness.auxVar,
    PatternBooleanWitness.edgeFactor]
  rfl

/-- The formula's polynomial Boolean-sums to the desired homomorphism polynomial. -/
theorem boolSum_patternFormula (m : Fin n → Fin n → ℕ) (t : BlockIndex m → K)
    (ht : ∀ b, t b ≠ 0) :
    boolSum (polynomial (patternFormula m t)) = hom K (squarePattern n m) n := by
  rw [polynomial_patternFormula_eq_witness m t ht]
  exact PatternBooleanWitness.boolSum_witness _ _

/-- Every joint row and column permutation extends to the concrete product formula. -/
noncomputable def patternIso (m : Fin n → Fin n → ℕ) (t : BlockIndex m → K) (γ : Γ n) :
    Iso (jointAction (auxAction n) γ) (patternFormula m t).tree (patternFormula m t).tree := by
  apply TreeFormulaIsomorphism.joinIso _ _ _ (Equiv.refl _) _ true
  intro b
  apply tagIso
  cases b with
  | inl v => exact selectorIso γ v
  | inr e => exact edgeIso γ e.1 e.2.1

section Combination

variable {R : Type} [Fintype R]

/-- A finite linear combination of pattern witnesses, with separate tagged summands. -/
noncomputable def combinationFormula (c : R → K) (m : R → Fin n → Fin n → ℕ)
    (t : ∀ r, BlockIndex (m r) → K) (s : R → K) : Formula (Variables n) K :=
  op false (fun r => tag (s r) (mul (const (c r)) (patternFormula (m r) (t r))))

theorem polynomial_combinationFormula (c : R → K) (m : R → Fin n → Fin n → ℕ)
    (t : ∀ r, BlockIndex (m r) → K) (s : R → K) (hs : ∀ r, s r ≠ 0) :
    polynomial (combinationFormula c m t s) =
      ∑ r, MvPolynomial.C (c r) * polynomial (patternFormula (m r) (t r)) := by
  simp only [combinationFormula, polynomial_op, ↓reduceIte]
  simp_rw [polynomial_tag _ (hs _) _, polynomial_mul, polynomial_const]
  simp

/-- The finite-sum circuit computes the desired linear combination after Boolean summing. -/
theorem boolSum_combinationFormula (c : R → K) (m : R → Fin n → Fin n → ℕ)
    (t : ∀ r, BlockIndex (m r) → K) (s : R → K)
    (ht : ∀ r b, t r b ≠ 0) (hs : ∀ r, s r ≠ 0) :
    boolSum (polynomial (combinationFormula c m t s)) =
      ∑ r, MvPolynomial.C (c r) * hom K (squarePattern n (m r)) n := by
  rw [polynomial_combinationFormula c m t s hs, Section7Assembly.boolSum_linearCombination]
  apply Finset.sum_congr rfl
  intro r hr
  rw [boolSum_patternFormula (m r) (t r) (ht r)]

/-- The explicit tree isomorphism for the whole finite combination. -/
noncomputable def combinationIso (c : R → K) (m : R → Fin n → Fin n → ℕ)
    (t : ∀ r, BlockIndex (m r) → K) (s : R → K) (γ : Γ n) :
    Iso (jointAction (auxAction n) γ) (combinationFormula c m t s).tree
      (combinationFormula c m t s).tree := by
  apply TreeFormulaIsomorphism.joinIso _ _ _ (Equiv.refl _) _ false
  intro r
  apply tagIso
  exact mulIso _ _ _ _ _ (constIso _ _) (patternIso (m r) (t r) γ)

theorem symmetric_combinationFormula (c : R → K) (m : R → Fin n → Fin n → ℕ)
    (t : ∀ r, BlockIndex (m r) → K) (s : R → K) :
    Symmetric (jointAction (auxAction n))
      (TreeFormulaCircuit.circuit (combinationFormula c m t s).tree) := by
  intro γ
  exact ⟨(combinationIso c m t s γ).equiv,
    TreeFormulaIsomorphism.extends_circuit (combinationIso c m t s γ)⟩

end Combination

end Lax461425Proofs.TaggedPatternFormula
