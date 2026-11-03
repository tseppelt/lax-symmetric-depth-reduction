import Lax461425.HomomorphismSpanning
import Lax461425Proofs.HomSpanningOrbits

/-! Independent proof of general homomorphism spanning with bounded pattern vertex sets. -/
namespace Lax461425Proofs.HomomorphismSpanning

open Lax461425.HomomorphismPolynomials Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies
open HomSpanningQuotient HomSpanningInjective HomSpanningOrbits
open scoped Classical

theorem orbit_sum_mem {K : Type*} [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n × Fin n) K) :
    (∑ γ : Γ n, MvPolynomial.rename (actVar γ) p) ∈ homSpan K n := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have he : MvPolynomial.monomial d c = c • (MvPolynomial.monomial d 1 : MvPolynomial (Fin n × Fin n) K) := by
      simp [MvPolynomial.smul_monomial]
    have hm : ∀ γ : Γ n,
        MvPolynomial.rename (actVar γ) (MvPolynomial.monomial d c) =
          c • MvPolynomial.rename (actVar γ) (MvPolynomial.monomial d (1 : K)) := by
      intro γ
      rw [he]
      simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.rename_C]
    simp_rw [hm]
    rw [← Finset.smul_sum]
    exact Submodule.smul_mem _ c (orbit_monomial_mem d)
  | add p q hp hq =>
    simp only [map_add, Finset.sum_add_distrib]
    exact Submodule.add_mem _ hp hq

/--
---
conclusion: Lax461425.HomomorphismSpanning.invariant_mem_span_hom
---
Expand into monomials, express each permutation orbit sum by collision inclusion-exclusion
as a linear combination of quotient-pattern homomorphism polynomials, and divide by the
nonzero order of the row/column permutation group. Quotients never increase either vertex set.
-/
theorem invariant_mem_span_hom {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (hn : 1 ≤ n) (p : MvPolynomial (Fin n × Fin n) K) (hp : MatrixInvariant p) :
    p ∈ Submodule.span K {q | ∃ F : Pattern,
      Fintype.card F.A ≤ n ∧ Fintype.card F.B ≤ n ∧ hom K F n = q} := by
  have hsum := orbit_sum_mem p
  have he : (∑ γ : Γ n, MvPolynomial.rename (actVar γ) p) = (Fintype.card (Γ n) : K) • p := by
    calc
      _ = ∑ _γ : Γ n, p := Finset.sum_congr rfl (fun γ _ => hp γ)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ]
        exact (Nat.cast_smul_eq_nsmul K _ _).symm
  have hcard : (Fintype.card (Γ n) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h := Submodule.smul_mem (homSpan K n) (Fintype.card (Γ n) : K)⁻¹ hsum
  rw [he, smul_smul, inv_mul_cancel₀ hcard, one_smul] at h
  exact h

end Lax461425Proofs.HomomorphismSpanning
