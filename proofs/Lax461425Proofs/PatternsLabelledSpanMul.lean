import Lax461425Proofs.PatternsLabelledOps
import Lax461425Proofs.PatternsLabelledGlue

/-!
---
title: Closure of span𝔗P under pointwise multiplication (lem:labelled-ops, concluding part)
type: theorem
---
We show the concluding part of `lem:labelled-ops`: $\mathfrak T^{\Delta,k}_{n,P}(\ell,r)$ is
closed under pointwise multiplication of the curried homomorphism-polynomial functions. The
proof is `Submodule.span_induction₂` applied to the two factors simultaneously: on generators
(both factors are `labelledHom K G n`/`labelledHom K G' n` for `G, G' ∈ 𝒯^{Δ,k}_P(ℓ,r)`), the
product is `labelledHom K (glue G G') n` by `labelledHom_glue`, and `glue G G' ∈ 𝒯^{Δ,k}_P(ℓ,r)`
by `inClassP_glue`; the remaining cases (`0`, `+`, scalar `•` on either factor) are routine
bilinearity of pointwise multiplication.
-/

namespace Lax461425Proofs.PatternsLabelledSpanMul

open Lax461425.HomomorphismPolynomials Lax461425Proofs.PatternsLabelledBasic
open Lax461425Proofs.PatternsLabelledOps Lax461425Proofs.PatternsLabelledGlue
open scoped Classical

variable {ℓ r : ℕ}

/-- **The concluding part of `lem:labelled-ops`**: $\mathfrak T^{\Delta,k}_{n,P}(\ell,r)$ is
closed under pointwise multiplication. -/
theorem span𝔗P_mul_mem {K : Type*} [Field K] {Δ k n : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)}
    (hP : P.card ≤ k)
    {x y : (Fin ℓ → Fin n) → (Fin r → Fin n) → MvPolynomial (Fin n × Fin n) K}
    (hx : x ∈ span𝔗P K Δ k n P) (hy : y ∈ span𝔗P K Δ k n P) :
    (fun v w => x v w * y v w) ∈ span𝔗P K Δ k n P := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
      obtain ⟨G, hG, rfl⟩ := hx
      obtain ⟨G', hG', rfl⟩ := hy
      have heq : (fun v w => labelledHom K G n v w * labelledHom K G' n v w) =
          labelledHom K (glue G G') n := by
        funext v w
        rw [labelledHom_glue]
      rw [heq]
      exact Submodule.subset_span ⟨glue G G', inClassP_glue G G' hP hG hG', rfl⟩
  | zero_left y _ =>
      have heq : (fun v w =>
          (0 : (Fin ℓ → Fin n) → (Fin r → Fin n) → MvPolynomial (Fin n × Fin n) K) v w * y v w)
          = 0 := by
        funext v w
        show (0 : MvPolynomial (Fin n × Fin n) K) * y v w = 0
        rw [zero_mul]
      rw [heq]
      exact Submodule.zero_mem _
  | zero_right x _ =>
      have heq : (fun v w => x v w *
          (0 : (Fin ℓ → Fin n) → (Fin r → Fin n) → MvPolynomial (Fin n × Fin n) K) v w) = 0 := by
        funext v w
        show x v w * (0 : MvPolynomial (Fin n × Fin n) K) = 0
        rw [mul_zero]
      rw [heq]
      exact Submodule.zero_mem _
  | add_left x y z _ _ _ ihx ihy =>
      have heq : (fun v w => (x + y) v w * z v w) =
          (fun v w => x v w * z v w) + (fun v w => y v w * z v w) := by
        funext v w
        show (x v w + y v w) * z v w = x v w * z v w + y v w * z v w
        ring
      rw [heq]
      exact Submodule.add_mem _ ihx ihy
  | add_right x y z _ _ _ ihy ihz =>
      have heq : (fun v w => x v w * (y + z) v w) =
          (fun v w => x v w * y v w) + (fun v w => x v w * z v w) := by
        funext v w
        show x v w * (y v w + z v w) = x v w * y v w + x v w * z v w
        ring
      rw [heq]
      exact Submodule.add_mem _ ihy ihz
  | smul_left c x y _ _ ih =>
      have heq : (fun v w => (c • x) v w * y v w) = c • fun v w => x v w * y v w := by
        funext v w
        show (c • x v w) * y v w = c • (x v w * y v w)
        rw [smul_mul_assoc]
      rw [heq]
      exact Submodule.smul_mem _ c ih
  | smul_right c x y _ _ ih =>
      have heq : (fun v w => x v w * (c • y) v w) = c • fun v w => x v w * y v w := by
        funext v w
        show x v w * (c • y v w) = c • (x v w * y v w)
        rw [mul_smul_comm]
      rw [heq]
      exact Submodule.smul_mem _ c ih

end Lax461425Proofs.PatternsLabelledSpanMul
