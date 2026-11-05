import Lax461425.CircuitProperties
import Lax461425Proofs.BooleanWitnesses
import Lax461425Proofs.CircuitFamilyFacts
import Lax461425Proofs.Section7Padding
import Lax461425Proofs.CircuitReindex

open Lax461425.CircuitProperties

/-! Linearity and the zero-order case for assembling the Section 7 formula witnesses. -/

namespace Lax461425Proofs.Section7Assembly

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies Lax461425.SymmetricVNP
open Lax461425.SymmetricClasses
open Lax461425Proofs.CircuitConstants
open scoped Classical BigOperators

variable {X Y K : Type*} [Fintype Y] [CommSemiring K]

/-- All summands use the same auxiliary variables, so Boolean summation is linear. -/
theorem boolSum_linearCombination {I : Type*} [Fintype I]
    (c : I → K) (g : I → MvPolynomial (X ⊕ Y) K) :
    boolSum (∑ i, MvPolynomial.C (c i) * g i) =
      ∑ i, MvPolynomial.C (c i) * boolSum (g i) := by
  simp only [boolSum, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact (Finset.mul_sum _ _ _).symm

/-- The zero-size variable matrix has only constant polynomials. A one-gate constant
formula supplies the family witness; the positive-order bound `4n²` is not asserted here. -/
theorem zero_formula_witness (K : Type*) [CommSemiring K]
    (p : MvPolynomial (Fin 0 × Fin 0) K) :
    ∃ (ρ : Γ 0 →* Equiv.Perm (Fin 0))
      (g : MvPolynomial ((Fin 0 × Fin 0) ⊕ Fin 0) K)
      (C : Circuit ((Fin 0 × Fin 0) ⊕ Fin 0) K),
      C.Computes g ∧ Symmetric (jointAction ρ) C ∧
      orbitSize (jointAction ρ) C ≤ 1 ∧ IsFormula C ∧ boolSum g = p := by
  let ρ : Γ 0 →* Equiv.Perm (Fin 0) := 1
  refine ⟨ρ, MvPolynomial.C (p.coeff 0),
    constant ((Fin 0 × Fin 0) ⊕ Fin 0) (p.coeff 0),
    CircuitFacts.constant_computes _, CircuitFamilyFacts.constant_symmetric _ _,
    CircuitFamilyFacts.constant_orbitSize_le_one _ _,
    CircuitFamilyFacts.constant_isFormula _, ?_⟩
  calc
    _ = MvPolynomial.C (p.coeff 0) := by simp [boolSum]
    _ = p := p.eq_C_of_isEmpty.symm

/-- Reindex a formula witness without changing its Boolean sum or any gate orbit. -/
theorem reindex_formula_witness {n b : ℕ} {Y Z : Type} [Fintype Y] [Fintype Z]
    (e : Y ≃ Z) (p : MvPolynomial (Fin n × Fin n) K)
    (h : ∃ (ρ : Γ n →* Equiv.Perm Y)
      (g : MvPolynomial ((Fin n × Fin n) ⊕ Y) K)
      (C : Circuit ((Fin n × Fin n) ⊕ Y) K),
      C.Computes g ∧ Symmetric (jointAction ρ) C ∧
      orbitSize (jointAction ρ) C ≤ b ∧ IsFormula C ∧ boolSum g = p) :
    ∃ (ρ : Γ n →* Equiv.Perm Z)
      (g : MvPolynomial ((Fin n × Fin n) ⊕ Z) K)
      (C : Circuit ((Fin n × Fin n) ⊕ Z) K),
      C.Computes g ∧ Symmetric (jointAction ρ) C ∧
      orbitSize (jointAction ρ) C ≤ b ∧ IsFormula C ∧ boolSum g = p := by
  obtain ⟨ρ, g, C, hc, hs, ho, hf, hp⟩ := h
  let E := Equiv.sumCongr (Equiv.refl (Fin n × Fin n)) e
  refine ⟨CircuitReindex.action e ρ, MvPolynomial.rename E g,
    CircuitReindex.rename E C, CircuitReindex.computes E C hc, ?_, ?_,
    CircuitReindex.isFormula E C hf, ?_⟩
  · rw [← CircuitReindex.action_joint e ρ]
    exact CircuitReindex.symmetric E (jointAction ρ) C hs
  · rw [← CircuitReindex.action_joint e ρ, CircuitReindex.orbitSize_eq]
    exact ho
  · exact (BooleanWitnesses.boolSum_rename_auxEquiv e g).trans hp

/-- The common square-pattern auxiliary variables have exactly `2n²` coordinates. -/
theorem square_aux_card (n : ℕ) :
    Fintype.card ((Fin n ⊕ Fin n) × Fin n) = 2 * n ^ 2 := by
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  ring

/-- Put a square-pattern witness on `Fin (2n²)`, preserving the quantitative bound. -/
theorem positive_witness_reindex {n b : ℕ} (p : MvPolynomial (Fin n × Fin n) K)
    (h : ∃ (ρ : Γ n →* Equiv.Perm ((Fin n ⊕ Fin n) × Fin n))
      (g : MvPolynomial ((Fin n × Fin n) ⊕ ((Fin n ⊕ Fin n) × Fin n)) K)
      (C : Circuit ((Fin n × Fin n) ⊕ ((Fin n ⊕ Fin n) × Fin n)) K),
      C.Computes g ∧ Symmetric (jointAction ρ) C ∧
      orbitSize (jointAction ρ) C ≤ b ∧ IsFormula C ∧ boolSum g = p) :
    ∃ (ρ : Γ n →* Equiv.Perm (Fin (2 * n ^ 2)))
      (g : MvPolynomial ((Fin n × Fin n) ⊕ Fin (2 * n ^ 2)) K)
      (C : Circuit ((Fin n × Fin n) ⊕ Fin (2 * n ^ 2)) K),
      C.Computes g ∧ Symmetric (jointAction ρ) C ∧
      orbitSize (jointAction ρ) C ≤ b ∧ IsFormula C ∧ boolSum g = p :=
  reindex_formula_witness (Fintype.equivFinOfCardEq (square_aux_card n)) p h

/-- The positive-order construction and the constant zero-order case give a family
with exactly `2n²` Boolean variables and polynomially bounded formula orbits. -/
theorem family_of_positive (f : MatrixFamily K)
    (hpos : ∀ n : ℕ, 1 ≤ n →
      ∃ (ρ : Γ n →* Equiv.Perm (Fin (2 * n ^ 2)))
        (g : MvPolynomial ((Fin n × Fin n) ⊕ Fin (2 * n ^ 2)) K)
        (C : Circuit ((Fin n × Fin n) ⊕ Fin (2 * n ^ 2)) K),
        C.Computes g ∧ Symmetric (jointAction ρ) C ∧
        orbitSize (jointAction ρ) C ≤ 4 * n ^ 2 ∧ IsFormula C ∧ boolSum g = f n) :
    InSymVNPFormula f := by
  refine ⟨fun n => 2 * n ^ 2, fun n => 4 * (n + 1) ^ 2, ?_, ?_, ?_⟩
  · refine ⟨2, 2, ?_⟩
    intro n
    change 2 * n ^ 2 ≤ 2 * (n + 1) ^ 2
    simp only [pow_two]
    exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n))
  · exact ⟨4, 2, fun _ => le_rfl⟩
  · intro n
    by_cases hn : n = 0
    · subst n
      obtain ⟨ρ, g, C, hc, hs, ho, hf, hp⟩ := zero_formula_witness K (f 0)
      refine ⟨ρ, g, C, hc, hs, ?_, hf, hp⟩
      exact ho.trans (by decide)
    · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      obtain ⟨ρ, g, C, hc, hs, ho, hf, hp⟩ := hpos n hn'
      refine ⟨ρ, g, C, hc, hs, ?_, hf, hp⟩
      apply ho.trans
      change 4 * n ^ 2 ≤ 4 * (n + 1) ^ 2
      simp only [pow_two]
      exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n))

end Lax461425Proofs.Section7Assembly
