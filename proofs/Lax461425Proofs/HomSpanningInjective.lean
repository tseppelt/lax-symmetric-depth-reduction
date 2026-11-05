import Lax461425Proofs.HomSpanningConstraints
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.LinearAlgebra.Span.Defs

/-! The paper's embedding-to-homomorphism expansion by partition Möbius inversion. -/
open Lax461425.SymmetricFamilies (MatrixPolynomial)

namespace Lax461425Proofs.HomSpanningInjective

open Lax461425.HomomorphismPolynomials HomSpanningQuotient HomSpanningConstraints
open scoped Classical
noncomputable section
attribute [local instance] setoidFintype
attribute [local instance] Fintype.toLocallyFiniteOrder

/-- The bounded-vertex homomorphism span used by Sections 6 and 7. -/
def homSpan (K : Type*) [Field K] (n : ℕ) : Submodule K (MatrixPolynomial n K) :=
  Submodule.span K {q | ∃ F : Pattern,
    Fintype.card F.A ≤ n ∧ Fintype.card F.B ≤ n ∧ hom K F n = q}

/-- The embedding polynomial `emb` from Appendix A, before automorphism normalisation. -/
def injectiveHom (K : Type*) [CommRing K] (F : Pattern) (n : ℕ) :
    MatrixPolynomial n K :=
  ∑ a : F.A → Fin n, ∑ b : F.B → Fin n,
    if Function.Injective a ∧ Function.Injective b then weight F a b else 0

/-- Corollary A.3 before division by `|Aut(F)|`. The product partition lattice handles
both parts together; no explicit factorial formula for its Möbius function is needed. -/
theorem injectiveHom_eq_moebius {K : Type*} [CommRing K] (F : Pattern) (n : ℕ) :
    injectiveHom K F n = ∑ r : Partitions F,
      MvPolynomial.C (IncidenceAlgebra.mu K (⊥ : Partitions F) r) *
        hom K (quotient F r.1 r.2) n := by
  have hbot : exactSum (K := K) F n ⊥ = injectiveHom K F n := by
    change exactSum (K := K) F n (⊥, ⊥) = injectiveHom K F n
    simp only [exactSum, injectiveHom, Fintype.sum_prod_type, Prod.mk.injEq,
      Setoid.ker_eq_bot_iff]
  rw [← hbot]
  ext d
  have h := IncidenceAlgebra.moebius_inversion_top
    (fun r : Partitions F => (exactSum (K := K) F n r).coeff d)
    (fun r : Partitions F => (upperSum (K := K) F n r).coeff d) ?_ ⊥
  · simpa [upperSum_eq_hom, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul] using h
  · intro r
    rw [upperSum_eq_exact]
    simp only [MvPolynomial.coeff_sum, apply_ite, MvPolynomial.coeff_zero]
    rw [← Finset.sum_filter]
    congr 1
    ext s
    simp

/-- Quotients only identify vertices, so every term preserves the required vertex bounds. -/
theorem injectiveHom_mem {K : Type*} [Field K] (F : Pattern) (n : ℕ)
    (hA : Fintype.card F.A ≤ n) (hB : Fintype.card F.B ≤ n) :
    injectiveHom K F n ∈ homSpan K n := by
  rw [injectiveHom_eq_moebius]
  apply Submodule.sum_mem
  intro r _
  rw [← MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨quotient F r.1 r.2,
    (card_left F _ _).trans hA, (card_right F _ _).trans hB, rfl⟩)

end
end Lax461425Proofs.HomSpanningInjective
