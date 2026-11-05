import Lax461425Proofs.Section6ABPSumComputes
import Lax461425Proofs.Section6ABPSumSymmetry
import Lax461425Proofs.Section6ABPSumTags
import Lax461425Proofs.Section6ConstantABP

/-! Combine symmetric ABPs as in Lemma 6.5, keeping branches apart by constant tags. -/

namespace Lax461425Proofs.Section6ABPSum

open Lax461425.SymmetricABPs
open scoped Classical

/-- Attach coefficient and tag edges to the branches and identify endpoints.
The common vertex-orbit bound is unchanged, even when coefficients are zero. -/
theorem exists_linear_combination {I : Type} [Fintype I] {K : Type*} [Field K] [CharZero K]
    {n : ℕ} (coeff : I → K) (G : I → ABP (Fin n × Fin n) K)
    (hsym : ∀ i, (G i).IsMatrixSymmetric) (B : ℕ) (hB : 1 ≤ B)
    (hbound : ∀ i, (G i).orbitSize ≤ B) :
    ∃ H : ABP (Fin n × Fin n) K,
      H.Computes (∑ i, MvPolynomial.C (coeff i) * (G i).polynomial) ∧
      H.IsMatrixSymmetric ∧ H.orbitSize ≤ B := by
  classical
  by_cases hI : Nonempty I
  · letI : Nonempty I := hI
    refine ⟨abp G coeff, computes G coeff, isMatrixSymmetric G coeff hsym, ?_⟩
    exact orbitSize_le G coeff
      (fun σ π hσ => endpoints_fixed_of_tags G coeff σ π hσ) B hB hbound
  · letI : IsEmpty I := not_nonempty_iff.mp hI
    refine ⟨Section6ConstantABP.constant (Fin n × Fin n) (0 : K), ?_,
      Section6ConstantABP.isMatrixSymmetric n 0,
      (Section6ConstantABP.orbitSize_le n 0).trans hB⟩
    simpa using Section6ConstantABP.computes (V := Fin n × Fin n) (0 : K)

end Lax461425Proofs.Section6ABPSum
