import Lax461425Proofs.Section6ABPLengths
import Lax461425Proofs.Section6ABPSumComputes
import Lax461425Proofs.Section6ABPSumSymmetry
import Lax461425Proofs.Section6ConstantABP

/-! Combine layered symmetric ABPs using the distinct path lengths of Lemma 6.5. -/

namespace Lax461425Proofs.Section6ABPSum

open Lax461425.SymmetricABPs
open scoped Classical

/-- Attach coefficient edges to branches of distinct lengths and identify endpoints.
The common vertex-orbit bound is unchanged, even when coefficients are zero. -/
theorem exists_linear_combination {I : Type} [Fintype I] {K : Type*} [Field K]
    {n : ℕ} (coeff : I → K) (G : I → ABP (Fin n × Fin n) K)
    (L : ∀ i, Section6Layering.Layering (G i))
    (hlength : Function.Injective (fun i => (L i).layer (G i).sink))
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
      (fun σ π hσ => endpoints_fixed_of_lengths G L coeff σ π hσ hlength) B hB hbound
  · letI : IsEmpty I := not_nonempty_iff.mp hI
    refine ⟨Section6ConstantABP.constant (Fin n × Fin n) (0 : K), ?_,
      Section6ConstantABP.isMatrixSymmetric n 0,
      (Section6ConstantABP.orbitSize_le n 0).trans hB⟩
    simpa using Section6ConstantABP.computes (V := Fin n × Fin n) (0 : K)

end Lax461425Proofs.Section6ABPSum
