import Lax461425.HomomorphismPolynomials

/-!
If a pattern `F` has no edges, its homomorphism polynomial `hom K F n` is just the constant
`n ^ |F.A| * n ^ |F.B|`: every exponent `F.mult a b` in the defining product is `0`, so every
term of the defining double sum is `1`.
-/

open Lax461425.SymmetricFamilies (MatrixPolynomial)

namespace Lax461425Proofs

open Lax461425.HomomorphismPolynomials

theorem hom_eq_const_of_no_edge {K : Type*} [CommSemiring K] (F : Pattern) (n : ℕ)
    (hF : ∀ a b, F.mult a b = 0) :
    hom K F n = MvPolynomial.C ((n : K) ^ Fintype.card F.A * (n : K) ^ Fintype.card F.B) := by
  have hone : hom K F n =
      ∑ _hA : F.A → Fin n, ∑ _hB : F.B → Fin n, (1 : MatrixPolynomial n K) := by
    unfold hom
    refine Finset.sum_congr rfl (fun hA _ => Finset.sum_congr rfl (fun hB _ => ?_))
    refine Finset.prod_eq_one (fun a _ => Finset.prod_eq_one (fun b _ => ?_))
    rw [hF a b, pow_zero]
  rw [hone, Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, smul_smul, nsmul_eq_mul, mul_one]
  rw [show ((n ^ Fintype.card F.A * n ^ Fintype.card F.B : ℕ) :
      MatrixPolynomial n K) =
      MvPolynomial.C ((n ^ Fintype.card F.A * n ^ Fintype.card F.B : ℕ) : K) from
    (map_natCast MvPolynomial.C _).symm]
  congr 1
  push_cast
  ring

end Lax461425Proofs
