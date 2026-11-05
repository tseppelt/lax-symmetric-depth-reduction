import Lax461425.SymmetricClasses
import Lax461425.SymmetricVNP
import Lax461425.HomomorphismSpanning
import Lax461425Proofs.HomSpanningOrbits

/-! DPS, Lemma 4: distinct monomial orbits, embedding polynomials, and Möbius inversion. -/
namespace Lax461425Proofs.HomomorphismSpanning

open Lax461425.HomomorphismPolynomials Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies
open Lax461425.SymmetricVNP
open Lax461425.SymmetricClasses
open HomSpanningQuotient HomSpanningInjective HomSpanningOrbits
open scoped Classical
noncomputable section
attribute [local instance] exponentAction

abbrev OrbitClass (n : ℕ) := MulAction.orbitRel.Quotient (Γ n) (Exponent n)
def monomialClass {n : ℕ} (d : Exponent n) : OrbitClass n := Quotient.mk _ d

theorem class_eq_iff {n : ℕ} (d : Exponent n) (q : OrbitClass n) :
    monomialClass d = q ↔ d ∈ MulAction.orbit (Γ n) q.out := by
  constructor
  · intro h
    exact MulAction.orbitRel_apply.mp
      (Quotient.exact (h.trans (Quotient.out_eq' q).symm))
  · intro h
    exact (Quotient.sound (MulAction.orbitRel_apply.mpr h)).trans (Quotient.out_eq' q)

section Coefficients

variable {K : Type*} [Field K] {n : ℕ}

/-- Symmetry makes coefficients constant on each monomial orbit. -/
theorem coeff_smul (p : MvPolynomial (Fin n × Fin n) K) (hp : MatrixInvariant p)
    (γ : Γ n) (d : Exponent n) : p.coeff (γ • d) = p.coeff d := by
  have h := MvPolynomial.coeff_rename_mapDomain (actVar γ)
    (show Function.Injective (actVar γ) from (Equiv.prodCongr γ.1 γ.2).injective) p d
  rw [hp γ] at h
  exact h

theorem coeff_of_orbit (p : MvPolynomial (Fin n × Fin n) K) (hp : MatrixInvariant p)
    (d e : Exponent n) (he : e ∈ MulAction.orbit (Γ n) d) : p.coeff e = p.coeff d := by
  obtain ⟨γ, rfl⟩ := he
  exact coeff_smul p hp γ d

/-- Each support fiber is one entire orbit with a common coefficient. -/
theorem fiber_sum (p : MvPolynomial (Fin n × Fin n) K) (hp : MatrixInvariant p)
    (q : OrbitClass n) (hq : q ∈ p.support.image monomialClass) :
    (∑ d ∈ p.support.filter (fun d => monomialClass d = q), MvPolynomial.monomial d (p.coeff d)) =
      p.coeff q.out • orbitSum K q.out := by
  have hc : ∀ e ∈ orbitFinset q.out, p.coeff e = p.coeff q.out :=
    fun e he => coeff_of_orbit p hp _ _ ((mem_orbitFinset _ _).mp he)
  have hrep : p.coeff q.out ≠ 0 := by
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hq
    have hec := coeff_of_orbit p hp q.out e ((class_eq_iff e q).mp heq)
    exact fun hz => (MvPolynomial.mem_support_iff.mp he) (hec.trans hz)
  have hs : p.support.filter (fun d => monomialClass d = q) = orbitFinset q.out := by
    ext e
    rw [Finset.mem_filter, mem_orbitFinset, class_eq_iff]
    constructor
    · exact And.right
    · intro he
      refine ⟨MvPolynomial.mem_support_iff.mpr ?_, he⟩
      rwa [coeff_of_orbit p hp _ _ he]
  rw [hs, orbitSum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [hc e he]
  simp [MvPolynomial.smul_monomial]

end Coefficients

/--
---
conclusion: Lax461425.HomomorphismSpanning.invariant_mem_span_hom
---
Partition the monomial support into distinct orbits. Each orbit sum is an embedding
polynomial divided by its nonzero automorphism factor; partition Möbius inversion
expresses it in the bounded-vertex homomorphism span, as in DPS, Lemma 4 and Corollary A.3.
-/
theorem invariant_mem_span_hom {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (hn : 1 ≤ n) (p : MvPolynomial (Fin n × Fin n) K) (hp : MatrixInvariant p) :
    p ∈ Submodule.span K {q | ∃ F : Pattern,
      Fintype.card F.A ≤ n ∧ Fintype.card F.B ≤ n ∧ hom K F n = q} := by
  change p ∈ homSpan K n
  have hdecomp : p = ∑ q ∈ p.support.image monomialClass,
      ∑ d ∈ p.support.filter (fun d => monomialClass d = q),
        MvPolynomial.monomial d (p.coeff d) := by
    rw [Finset.sum_fiberwise_eq_sum_filter,
      Finset.filter_eq_self.mpr (fun d hd => Finset.mem_image_of_mem monomialClass hd)]
    exact p.as_sum
  rw [hdecomp]
  apply Submodule.sum_mem
  intro q hq
  rw [fiber_sum p hp q hq]
  exact Submodule.smul_mem _ _ (orbit_monomial_mem q.out)

end
end Lax461425Proofs.HomomorphismSpanning
