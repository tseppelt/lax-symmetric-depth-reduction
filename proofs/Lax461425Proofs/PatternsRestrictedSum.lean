import Lax461425Proofs.PatternsRestrictedDelete
import Mathlib.Order.Partition.Finpartition

/-!
---
title: The restricted sum ψ_Σ (lem:restricted, Σ-part)
type: theorem
---
Assembling `PatternsRestrictedY` (the all-distinct indicator `δ`) and `PatternsRestrictedDelete`
(deleting labels by summing) to build `ψ_Σ`: given `φ ∈ 𝔗^{Δ,k}_{n,P}(ℓ+ℓ',r+r')` (for `P.card ≤
k`, `ℓ + r ≤ k`), `δ ⊙ φ` (pointwise product, `span𝔗P_mul_mem`) lies in the same span, and
summing it over the deleted labels (`span𝔗P_restrict_sum`) lands in `𝔗^{Δ+1,k}_n(ℓ,r)`. Since
`δ` is the `Y(v,w)`-indicator (`δ_eval`), this sum, for injective `v, w`, collapses to the
restricted sum of `φ` over `Y(v,w)`. Finally, for a partition of `Y(v,w)` into classes of size
`c` on which `φ` is constant, this restricted sum is `c` times the sum of the constant values,
giving `lem:restricted`'s `ψ_Σ`.
-/

namespace Lax461425Proofs.PatternsRestrictedSum

open Lax461425.HomomorphismPolynomials Lax461425Proofs.PatternsLabelledBasic
open Lax461425Proofs.PatternsLabelledOps Lax461425Proofs.PatternsLabelledSpanMul
open Lax461425Proofs.PatternsRestrictedMono Lax461425Proofs.PatternsRestrictedDelta
open Lax461425Proofs.PatternsRestrictedY Lax461425Proofs.PatternsRestrictedDelete
open scoped Classical

variable {ℓ ℓ' r r' : ℕ}

/-- **The restricted sum**: `sumExt` of `δ ⊙ φ`, evaluated at injective `v, w`, collapses to the
sum of `φ` over `Y(v,w)` alone (the non-`Y(v,w)` terms are killed by `δ`'s indicator, `δ_eval`). -/
theorem sumExt_delta_mul_eq_sum_Y (K : Type*) [Field K] (n : ℕ) (v : Fin ℓ → Fin n)
    (w : Fin r → Fin n) (hv : Function.Injective v) (hw : Function.Injective w)
    (φ : (Fin (ℓ + ℓ') → Fin n) → (Fin (r + r') → Fin n) → MvPolynomial (Fin n × Fin n) K) :
    sumExt K n (fun v' w' => δ K ℓ ℓ' r r' n v' w' * φ v' w') v w =
      ∑ yz ∈ Y ℓ' r' n v w, φ (Fin.append v yz.1) (Fin.append w yz.2) := by
  show (∑ y : Fin ℓ' → Fin n, ∑ z : Fin r' → Fin n,
      δ K ℓ ℓ' r r' n (Fin.append v y) (Fin.append w z) *
        φ (Fin.append v y) (Fin.append w z)) =
    ∑ yz ∈ Y ℓ' r' n v w, φ (Fin.append v yz.1) (Fin.append w yz.2)
  simp_rw [δ_eval K n v w hv hw]
  rw [← Fintype.sum_prod_type']
  rw [show (∑ x : (Fin ℓ' → Fin n) × (Fin r' → Fin n),
      (if x ∈ Y ℓ' r' n v w then (1 : MvPolynomial (Fin n × Fin n) K) else 0) *
        φ (Fin.append v x.1) (Fin.append w x.2)) =
      ∑ x : (Fin ℓ' → Fin n) × (Fin r' → Fin n),
        if x ∈ Y ℓ' r' n v w then φ (Fin.append v x.1) (Fin.append w x.2) else 0 from
    Finset.sum_congr rfl (fun x _ => by by_cases h : x ∈ Y ℓ' r' n v w <;> simp [h])]
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp

/-- **`ψ_Σ` (unrestricted form)**: for `φ ∈ 𝔗^{Δ,k}_{n,P}(ℓ+ℓ',r+r')` with `P.card ≤ k`, there is
`ψ_Σ ∈ 𝔗^{Δ+1,k}_n(ℓ,r)` such that, for all injective `v, w`, `ψ_Σ(v,w) = ∑_{(y,z) ∈ Y(v,w)}
φ(vy,wz)`. -/
theorem exists_sum_Y_mem_span (K : Type*) [Field K] (Δ k n : ℕ)
    (P : Finset (Fin (ℓ + ℓ') ⊕ Fin (r + r'))) (hP : P.card ≤ k)
    (φ : (Fin (ℓ + ℓ') → Fin n) → (Fin (r + r') → Fin n) → MvPolynomial (Fin n × Fin n) K)
    (hφ : φ ∈ span𝔗P K Δ k n P) :
    ∃ ψSumFull : (Fin ℓ → Fin n) → (Fin r → Fin n) → MvPolynomial (Fin n × Fin n) K,
      ψSumFull ∈ span𝔗P K (Δ + 1) k n (Finset.univ : Finset (Fin ℓ ⊕ Fin r)) ∧
      ∀ (v : Fin ℓ → Fin n) (w : Fin r → Fin n), Function.Injective v → Function.Injective w →
        ψSumFull v w = ∑ yz ∈ Y ℓ' r' n v w, φ (Fin.append v yz.1) (Fin.append w yz.2) := by
  refine ⟨sumExt K n (fun v' w' => δ K ℓ ℓ' r r' n v' w' * φ v' w'), ?_, ?_⟩
  · exact span𝔗P_restrict_sum K Δ k n P _ (span𝔗P_mul_mem hP (δ_mem_span K Δ k n P hP) hφ)
  · intro v w hv hw
    exact sumExt_delta_mul_eq_sum_Y K n v w hv hw φ

/-- A general fact about `Finpartition`: summing over the partitioned set equals summing the
sums over each part (via the partition's own pairwise disjointness and `biUnion_parts`). -/
theorem Finpartition.sum_parts {α M : Type*} [DecidableEq α] [AddCommMonoid M] {s : Finset α}
    (𝒬 : Finpartition s) (f : α → M) : ∑ x ∈ s, f x = ∑ B ∈ 𝒬.parts, ∑ x ∈ B, f x := by
  conv_lhs => rw [← 𝒬.biUnion_parts]
  exact Finset.sum_biUnion (fun x hx y hy hxy => 𝒬.disjoint hx hy hxy)

/-- **`ψ_Σ` (`lem:restricted`'s Σ-part)**: for `φ ∈ 𝔗^{Δ,k}_{n,P}(ℓ+ℓ',r+r')` with `P.card ≤ k`,
there is `ψ_Σ ∈ 𝔗^{Δ+1,k}_n(ℓ,r)` with the following property. For all injective `v, w` and every
partition `𝒬` of `Y(v,w)` into classes of size exactly `c` (`c ≠ 0`) on which `φ` is constant
(witnessed by `φB`, assigning each part its common value of `φ`), `ψ_Σ(v,w) = ∑_{B ∈ 𝒬} φ_B`. -/
theorem exists_ψSum (K : Type*) [Field K] [CharZero K] (Δ k n : ℕ)
    (P : Finset (Fin (ℓ + ℓ') ⊕ Fin (r + r'))) (hP : P.card ≤ k) (c : ℕ) (hc : c ≠ 0)
    (φ : (Fin (ℓ + ℓ') → Fin n) → (Fin (r + r') → Fin n) → MvPolynomial (Fin n × Fin n) K)
    (hφ : φ ∈ span𝔗P K Δ k n P) :
    ∃ ψSum : (Fin ℓ → Fin n) → (Fin r → Fin n) → MvPolynomial (Fin n × Fin n) K,
      ψSum ∈ span𝔗P K (Δ + 1) k n (Finset.univ : Finset (Fin ℓ ⊕ Fin r)) ∧
      ∀ (v : Fin ℓ → Fin n) (w : Fin r → Fin n), Function.Injective v → Function.Injective w →
      ∀ (𝒬 : Finpartition (Y ℓ' r' n v w)), (∀ B ∈ 𝒬.parts, B.card = c) →
      ∀ (φB : Finset ((Fin ℓ' → Fin n) × (Fin r' → Fin n)) → MvPolynomial (Fin n × Fin n) K),
        (∀ B ∈ 𝒬.parts, ∀ x ∈ B, φ (Fin.append v x.1) (Fin.append w x.2) = φB B) →
        ψSum v w = ∑ B ∈ 𝒬.parts, φB B := by
  obtain ⟨ψSumFull, hmem, hval⟩ := exists_sum_Y_mem_span (ℓ' := ℓ') (r' := r') K Δ k n P hP φ hφ
  refine ⟨(c : K)⁻¹ • ψSumFull, Submodule.smul_mem _ _ hmem, ?_⟩
  intro v w hv hw 𝒬 hsize φB hφB
  have hval' := hval v w hv hw
  show (c : K)⁻¹ • ψSumFull v w = ∑ B ∈ 𝒬.parts, φB B
  rw [hval', Finpartition.sum_parts 𝒬 (fun x => φ (Fin.append v x.1) (Fin.append w x.2))]
  have hterm : ∀ B ∈ 𝒬.parts, ∑ x ∈ B, φ (Fin.append v x.1) (Fin.append w x.2) =
      (c : K) • φB B := by
    intro B hB
    rw [Finset.sum_congr rfl (fun x hx => hφB B hB x hx)]
    rw [Finset.sum_const, hsize B hB, ← Nat.cast_smul_eq_nsmul K]
  rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hc), one_smul]

end Lax461425Proofs.PatternsRestrictedSum
