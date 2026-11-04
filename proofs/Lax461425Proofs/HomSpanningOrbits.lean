import Lax461425Proofs.HomSpanningInjective
import Lax461425.SymmetricFamilies
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Distinct monomial orbits and their embedding-polynomial normalisation (DPS, Lemma 4). -/
namespace Lax461425Proofs.HomSpanningOrbits

open Lax461425.HomomorphismPolynomials Lax461425.MatrixSymmetry
open HomSpanningQuotient HomSpanningInjective
open scoped Classical
noncomputable section

abbrev Exponent (n : ℕ) := (Fin n × Fin n) →₀ ℕ

/-- Independent row and column permutations act on monomial exponents. -/
@[instance_reducible] def exponentAction (n : ℕ) : MulAction (Γ n) (Exponent n) where
  smul γ d := d.mapDomain (actVar γ)
  one_smul d := by change d.mapDomain id = d; exact Finsupp.mapDomain_id
  mul_smul γ δ d := by
    change d.mapDomain (actVar (γ * δ)) = (d.mapDomain (actVar δ)).mapDomain (actVar γ)
    exact Finsupp.mapDomain_comp (v := d) (f := actVar δ) (g := actVar γ)
attribute [local instance] exponentAction

/-- Each monomial in the orbit occurs once, rather than once per group element. -/
def orbitFinset {n : ℕ} (d : Exponent n) : Finset (Exponent n) :=
  Finset.univ.image (fun γ : Γ n => γ • d)

theorem mem_orbitFinset {n : ℕ} (d e : Exponent n) :
    e ∈ orbitFinset d ↔ e ∈ MulAction.orbit (Γ n) d := by
  simp [orbitFinset, MulAction.mem_orbit_iff]

def orbitSum (K : Type*) [CommRing K] {n : ℕ} (d : Exponent n) :
    MvPolynomial (Fin n × Fin n) K := ∑ e ∈ orbitFinset d, MvPolynomial.monomial e 1

/-- Retain isolated matrix indices in the existing pattern encoding. They only alter
its automorphism normalisation; both vertex sets still have size at most `n`. -/
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

/-- Every orbit monomial has equally many embeddings: the size of its stabilizer,
which is the bipartition-preserving automorphism group of `matrixPattern d`. -/
theorem embedding_eq_stabilizer_mul_orbit {K : Type*} [CommRing K] {n : ℕ}
    (d : Exponent n) :
    injectiveHom K (matrixPattern d) n =
      (Fintype.card (MulAction.stabilizer (Γ n) d) : K) • orbitSum K d := by
  rw [injectiveHom_eq_orbit]
  simp only [MvPolynomial.rename_monomial]
  change (∑ γ : Γ n, MvPolynomial.monomial (γ • d) (1 : K)) = _
  let O : MulAction.orbit (Γ n) d ≃ ↥(orbitFinset d) :=
    Equiv.subtypeEquivRight (fun e => (mem_orbitFinset d e).symm)
  let : Fintype (MulAction.orbit (Γ n) d) := Fintype.ofEquiv ↥(orbitFinset d) O.symm
  let E := MulAction.orbitProdStabilizerEquivGroup (Γ n) d
  calc
    _ = ∑ a : MulAction.orbit (Γ n) d × MulAction.stabilizer (Γ n) d,
        MvPolynomial.monomial a.1.val (1 : K) :=
      Fintype.sum_equiv E.symm _ _ (fun _ => rfl)
    _ = (Fintype.card (MulAction.stabilizer (Γ n) d) : K) •
        ∑ e : MulAction.orbit (Γ n) d, MvPolynomial.monomial e.val 1 := by
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
        Nat.cast_smul_eq_nsmul K, Finset.smul_sum]
    _ = _ := by
      congr 1
      exact (Fintype.sum_equiv O
        (fun e => MvPolynomial.monomial e.val (1 : K))
        (fun e => MvPolynomial.monomial e.val (1 : K)) (fun _ => rfl)).trans
          (Finset.sum_coe_sort (orbitFinset d) (fun e => MvPolynomial.monomial e (1 : K)))

/-- Divide by the nonzero automorphism normalisation, as for the paper's subgraph
polynomial. Möbius inversion then places this distinct orbit sum in the hom span. -/
theorem orbit_monomial_mem {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (d : Exponent n) : orbitSum K d ∈ homSpan K n := by
  have h := injectiveHom_mem (K := K) (matrixPattern d) n (by simp) (by simp)
  rw [embedding_eq_stabilizer_mul_orbit] at h
  have hc : (Fintype.card (MulAction.stabilizer (Γ n) d) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hscaled := Submodule.smul_mem (homSpan K n)
    (Fintype.card (MulAction.stabilizer (Γ n) d) : K)⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hscaled

end
end Lax461425Proofs.HomSpanningOrbits
