import Lax461425Proofs.HomSpanningQuotient

/-! The paper's kernel-partition decomposition of vertex maps (Appendix A, Lemma A.2). -/
open Lax461425.SymmetricFamilies (MatrixPolynomial)

namespace Lax461425Proofs.HomSpanningConstraints

open Lax461425.HomomorphismPolynomials HomSpanningQuotient
open scoped Classical
noncomputable section

/-- Equivalence relations on a finite vertex set form a finite partition lattice. -/
@[instance_reducible] def setoidFintype (A : Type*) [Fintype A] : Fintype (Setoid A) :=
  Fintype.ofInjective (fun r : Setoid A => r.r) (fun _ _ h =>
    Setoid.ext (fun x y => Iff.of_eq (congrFun (congrFun h x) y)))
attribute [local instance] setoidFintype

abbrev Partitions (F : Pattern) := Setoid F.A × Setoid F.B
abbrev Maps (F : Pattern) (n : ℕ) := (F.A → Fin n) × (F.B → Fin n)

/-- Maps with precisely this pair of kernel partitions. -/
def exactSum {K : Type*} [CommSemiring K] (F : Pattern) (n : ℕ)
    (r : Partitions F) : MatrixPolynomial n K :=
  ∑ h : Maps F n, if (Setoid.ker h.1, Setoid.ker h.2) = r then weight F h.1 h.2 else 0

/-- Maps constant on each block of the prescribed partitions. -/
def upperSum {K : Type*} [CommSemiring K] (F : Pattern) (n : ℕ)
    (r : Partitions F) : MatrixPolynomial n K :=
  ∑ h : Maps F n, if r ≤ (Setoid.ker h.1, Setoid.ker h.2) then weight F h.1 h.2 else 0

/-- Group maps by their kernels, as in the first identity of Lemma A.2. -/
theorem upperSum_eq_exact {K : Type*} [CommSemiring K] (F : Pattern) (n : ℕ)
    (r : Partitions F) :
    upperSum (K := K) F n r = ∑ s : Partitions F, if r ≤ s then exactSum F n s else 0 := by
  rw [← Finset.sum_filter]
  unfold exactSum upperSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  simp [eq_comm]

/-- A map constant on blocks is uniquely a map from the quotient. -/
theorem sum_lift {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] [AddCommMonoid R] (r : Setoid A) (f : (A → B) → R) :
    (∑ a : A → B, if r ≤ Setoid.ker a then f a else 0) =
      ∑ a : Quotient r → B, f (a ∘ Quotient.mk r) := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype _ (by simp : ∀ a : A → B,
    a ∈ Finset.univ.filter (fun a => r ≤ Setoid.ker a) ↔ r ≤ Setoid.ker a) f]
  exact Fintype.sum_equiv (Setoid.liftEquiv r) _ _ (fun _ => rfl)

/-- The upper sum is the homomorphism polynomial of the quotient pattern. -/
theorem upperSum_eq_hom {K : Type*} [CommSemiring K] (F : Pattern) (n : ℕ)
    (r : Partitions F) :
    upperSum (K := K) F n r = hom K (quotient F r.1 r.2) n := by
  unfold upperSum
  rw [Fintype.sum_prod_type]
  change (∑ a : F.A → Fin n, ∑ b : F.B → Fin n,
    if r.1 ≤ Setoid.ker a ∧ r.2 ≤ Setoid.ker b then weight F a b else 0) = _
  simp_rw [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [sum_lift]
  simp_rw [sum_lift]
  unfold hom
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact (weight_quotient F _ _ a b).symm

end
end Lax461425Proofs.HomSpanningConstraints
