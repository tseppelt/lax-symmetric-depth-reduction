import Lax461425Proofs.HomSpanningInjective
import Lax461425.SymmetricFamilies

/-! Permutation orbit sums of monomials are injective homomorphism polynomials. -/
namespace Lax461425Proofs.HomSpanningOrbits

open Lax461425.HomomorphismPolynomials Lax461425.MatrixSymmetry
open HomSpanningQuotient HomSpanningInjective
open scoped Classical
noncomputable section

abbrev matrixPattern {n : ℕ} (d : (Fin n × Fin n) →₀ ℕ) : Pattern where
  A := Fin n
  B := Fin n
  mult i j := d (i,j)

theorem weight_id {K : Type*} [CommRing K] {n : ℕ} (d : (Fin n × Fin n) →₀ ℕ) :
    weight (K := K) (matrixPattern d) id id = MvPolynomial.monomial d 1 := by
  rw [MvPolynomial.monomial_eq, map_one, one_mul,
    Finsupp.prod_fintype d _ (fun _ => pow_zero _)]
  exact (Fintype.prod_prod_type (fun x : Fin n × Fin n =>
    (MvPolynomial.X x : MvPolynomial (Fin n × Fin n) K) ^ d x)).symm

theorem weight_perm {K : Type*} [CommRing K] {n : ℕ} (d : (Fin n × Fin n) →₀ ℕ)
    (γ : Γ n) :
    weight (K := K) (matrixPattern d) γ.1 γ.2 =
      MvPolynomial.rename (actVar γ) (MvPolynomial.monomial d 1) := by
  rw [← weight_id d]
  simp [weight, matrixPattern, map_prod, map_pow, MvPolynomial.rename_X, actVar]

theorem sum_injective_self {A R : Type*} [Fintype A] [DecidableEq A] [AddCommMonoid R]
    (f : (A → A) → R) :
    (∑ a : A → A, if Function.Injective a then f a else 0) = ∑ σ : Equiv.Perm A, f σ := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun a ha =>
    Equiv.ofBijective a (Finset.mem_filter.mp ha).2.bijective_of_finite) ?_ ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_univ _
  · intro a ha b hb he
    exact congrArg (fun σ : Equiv.Perm A => (σ : A → A)) he
  · intro σ _
    exact ⟨σ, by simp [σ.injective], by ext x; rfl⟩
  · intro a ha
    rfl

theorem injectiveHom_eq_orbit {K : Type*} [CommRing K] {n : ℕ}
    (d : (Fin n × Fin n) →₀ ℕ) :
    injectiveHom K (matrixPattern d) n =
      ∑ γ : Γ n, MvPolynomial.rename (actVar γ) (MvPolynomial.monomial d 1) := by
  unfold injectiveHom
  change (∑ a : Fin n → Fin n, ∑ b : Fin n → Fin n,
    if Function.Injective a ∧ Function.Injective b then weight (matrixPattern d) a b else 0) = _
  simp_rw [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [sum_injective_self]
  simp_rw [sum_injective_self]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  exact weight_perm d (σ,τ)

theorem orbit_monomial_mem {K : Type*} [Field K] {n : ℕ}
    (d : (Fin n × Fin n) →₀ ℕ) :
    (∑ γ : Γ n, MvPolynomial.rename (actVar γ) (MvPolynomial.monomial d 1)) ∈ homSpan K n := by
  rw [← injectiveHom_eq_orbit]
  apply injectiveHom_mem (matrixPattern d) n
  · change Fintype.card (Fin n) ≤ n
    simp only [Fintype.card_fin, le_refl]
  · change Fintype.card (Fin n) ≤ n
    simp only [Fintype.card_fin, le_refl]

end
end Lax461425Proofs.HomSpanningOrbits
