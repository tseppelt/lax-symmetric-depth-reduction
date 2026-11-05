import Lax461425Proofs.PathRefinementOperations
import Lax461425Proofs.PatternsLabelledSpanMul

/-!
Linear-span closures for the refinement. The bilinearity, padding, and label-summation
proofs reuse Tim's existing homomorphism identities. Multiplication is restricted to
one arbitrary linear factor and one depth-one factor; no unrestricted product closure
is asserted for the path refinement.
-/

open Lax461425.SymmetricFamilies (MatrixPolynomial)

namespace Lax461425Proofs.PathRefinementSpan

open PatternsLabelledBasic PatternsLabelledOps PatternsLabelledGlue
open PatternsInductionReindex PatternsRestrictedDelete PatternsRestrictedMono
open PathRefinementClass PathRefinementOperations
open scoped Classical

variable {ℓ r ℓ' r' ℓ₀ r₀ ℓ₁ r₁ : ℕ}

theorem mul_star {K : Type*} [Field K] {Δ δ k n : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)}
    (hP : P.card ≤ k) (hδ : δ ≤ 1) (hle : δ ≤ Δ)
    {x y : (Fin ℓ → Fin n) → (Fin r → Fin n) → MatrixPolynomial n K}
    (hx : x ∈ spanLinear K Δ k n P) (hy : y ∈ span𝔗P K δ k n P) :
    (fun v w => x v w * y v w) ∈ spanLinear K Δ k n P := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
      obtain ⟨G, hG, rfl⟩ := hx
      obtain ⟨G', hG', rfl⟩ := hy
      have heq : (fun v w => labelledHom K G n v w * labelledHom K G' n v w) =
          labelledHom K (glue G G') n := by
        funext v w
        rw [labelledHom_glue]
      rw [heq]
      exact Submodule.subset_span ⟨glue G G', class_mul_star hP hδ hle hG hG', rfl⟩
  | zero_left y _ =>
      have heq : (fun v w =>
          (0 : (Fin ℓ → Fin n) → (Fin r → Fin n) → MatrixPolynomial n K) v w * y v w)
          = 0 := by
        funext v w
        show (0 : MatrixPolynomial n K) * y v w = 0
        rw [zero_mul]
      rw [heq]
      exact Submodule.zero_mem _
  | zero_right x _ =>
      have heq : (fun v w => x v w *
          (0 : (Fin ℓ → Fin n) → (Fin r → Fin n) → MatrixPolynomial n K) v w) = 0 := by
        funext v w
        show x v w * (0 : MatrixPolynomial n K) = 0
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

theorem pad_restrict {K : Type*} [Field K] {Δ k n : ℕ} {P₀ : Finset (Fin ℓ₀ ⊕ Fin r₀)}
    (ι : Fin ℓ₀ ↪ Fin ℓ₁) (κ : Fin r₀ ↪ Fin r₁)
    (φ : (Fin ℓ₀ → Fin n) → (Fin r₀ → Fin n) → MatrixPolynomial n K)
    (hφ : φ ∈ spanLinear K Δ k n P₀) :
    (fun v w => φ (v ∘ ι) (w ∘ κ)) ∈ spanLinear K Δ k n (P₀.image (Sum.map (⇑ι) (⇑κ))) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨G, hG, rfl⟩ := hx
      have heq : (fun v w => labelledHom K G n (v ∘ ι) (w ∘ κ)) =
          labelledHom K (padGraph G ι κ) n := by
        funext v w
        exact (labelledHom_padGraph G ι κ n K v w).symm
      rw [heq]
      exact Submodule.subset_span ⟨padGraph G ι κ, pad_class hG ι κ, rfl⟩
  | zero =>
      have heq : (fun v w => (0 : (Fin ℓ₀ → Fin n) → (Fin r₀ → Fin n) →
          MatrixPolynomial n K) (v ∘ ι) (w ∘ κ)) =
          (0 : (Fin ℓ₁ → Fin n) → (Fin r₁ → Fin n) → MatrixPolynomial n K) := by
        funext v w; rfl
      rw [heq]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      have heq : (fun v w => (x + y) (v ∘ ι) (w ∘ κ)) =
          (fun v w => x (v ∘ ι) (w ∘ κ)) + (fun v w => y (v ∘ ι) (w ∘ κ)) := by
        funext v w; rfl
      rw [heq]; exact Submodule.add_mem _ ihx ihy
  | smul c x _ ih =>
      have heq : (fun v w => (c • x) (v ∘ ι) (w ∘ κ)) = c • (fun v w => x (v ∘ ι) (w ∘ κ)) := by
        funext v w; rfl
      rw [heq]; exact Submodule.smul_mem _ c ih

theorem restrict_sum (K : Type*) [Field K] (Δ k n : ℕ)
    (P : Finset (Fin (ℓ + ℓ') ⊕ Fin (r + r')))
    (ψ : (Fin (ℓ + ℓ') → Fin n) → (Fin (r + r') → Fin n) → MatrixPolynomial n K)
    (hψ : ψ ∈ spanLinear K Δ k n P) :
    sumExt K n ψ ∈ spanLinear K (Δ + 1) k n (Finset.univ : Finset (Fin ℓ ⊕ Fin r)) := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨G, hG, rfl⟩ := hx
      have heq : sumExt K n (labelledHom K G n) =
          labelledHom K (restrict G (Fin.castAddEmb ℓ') (Fin.castAddEmb r')) n := by
        funext v w
        exact (labelledHom_restrict_eq_sum G n K v w).symm
      rw [heq]
      exact Submodule.subset_span ⟨restrict G (Fin.castAddEmb ℓ') (Fin.castAddEmb r'),
        restrict_class hG _ _, rfl⟩
  | zero =>
      have heq : sumExt K n (0 : (Fin (ℓ + ℓ') → Fin n) → (Fin (r + r') → Fin n) →
          MatrixPolynomial n K) = 0 := by
        funext v w
        show (∑ y : Fin ℓ' → Fin n, ∑ z : Fin r' → Fin n,
          (0 : (Fin (ℓ + ℓ') → Fin n) → (Fin (r + r') → Fin n) →
            MatrixPolynomial n K) (Fin.append v y) (Fin.append w z)) = 0
        simp
      rw [heq]
      exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      have heq : sumExt K n (x + y) = sumExt K n x + sumExt K n y := by
        funext v w
        show (∑ y' : Fin ℓ' → Fin n, ∑ z' : Fin r' → Fin n,
            (x + y) (Fin.append v y') (Fin.append w z')) =
          (∑ y' : Fin ℓ' → Fin n, ∑ z' : Fin r' → Fin n, x (Fin.append v y') (Fin.append w z')) +
            ∑ y' : Fin ℓ' → Fin n, ∑ z' : Fin r' → Fin n, y (Fin.append v y') (Fin.append w z')
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro y' _
        rw [← Finset.sum_add_distrib]
      rw [heq]
      exact Submodule.add_mem _ ihx ihy
  | smul c x _ ih =>
      have heq : sumExt K n (c • x) = c • sumExt K n x := by
        funext v w
        show (∑ y' : Fin ℓ' → Fin n, ∑ z' : Fin r' → Fin n,
            (c • x) (Fin.append v y') (Fin.append w z')) =
          c • ∑ y' : Fin ℓ' → Fin n, ∑ z' : Fin r' → Fin n, x (Fin.append v y') (Fin.append w z')
        simp only [Pi.smul_apply, Finset.smul_sum]
      rw [heq]
      exact Submodule.smul_mem _ c ih

theorem unrestrict {K : Type*} [Field K] {Δ k n : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)} :
    spanLinear K Δ k n P ≤ spanLinear K Δ k n (Finset.univ : Finset (Fin ℓ ⊕ Fin r)) := by
  apply Submodule.span_mono
  rintro f ⟨G, hG, rfl⟩
  exact ⟨G, ⟨hG.1, (inClassP_univ_of_inClass (PathRefinementClass.forget hG).1).2⟩, rfl⟩

theorem pad {K : Type*} [Field K] {Δ k n : ℕ}
    (ι : Fin ℓ₀ ↪ Fin ℓ₁) (κ : Fin r₀ ↪ Fin r₁)
    (φ : (Fin ℓ₀ → Fin n) → (Fin r₀ → Fin n) → MatrixPolynomial n K)
    (hφ : φ ∈ spanLinear K Δ k n (Finset.univ : Finset (Fin ℓ₀ ⊕ Fin r₀))) :
    (fun v w => φ (v ∘ ι) (w ∘ κ)) ∈
      spanLinear K Δ k n (Finset.univ : Finset (Fin ℓ₁ ⊕ Fin r₁)) :=
  unrestrict (pad_restrict ι κ φ hφ)

theorem star_at_depth {K : Type*} [Field K] {Δ k n : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)}
    {φ : (Fin ℓ → Fin n) → (Fin r → Fin n) → MatrixPolynomial n K}
    (hφ₁ : φ ∈ span𝔗P K 1 k n P) (hφΔ : φ ∈ span𝔗P K Δ k n P) :
    φ ∈ spanLinear K Δ k n P := by
  by_cases h : Δ = 0
  · subst Δ
    exact star_span (by decide : 0 ≤ 1) hφΔ
  · exact PathRefinementClass.span_mono (by omega : 1 ≤ Δ) (star_span le_rfl hφ₁)

theorem mul_star_at_depth {K : Type*} [Field K] {Δ k n : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)}
    (hP : P.card ≤ k)
    {φ ψ : (Fin ℓ → Fin n) → (Fin r → Fin n) → MatrixPolynomial n K}
    (hφ : φ ∈ spanLinear K Δ k n P) (hψ₁ : ψ ∈ span𝔗P K 1 k n P)
    (hψΔ : ψ ∈ span𝔗P K Δ k n P) :
    (fun v w => φ v w * ψ v w) ∈ spanLinear K Δ k n P := by
  by_cases h : Δ = 0
  · subst Δ
    exact mul_star hP (by decide : 0 ≤ 1) le_rfl hφ hψΔ
  · exact mul_star hP le_rfl (by omega : 1 ≤ Δ) hφ hψ₁

end Lax461425Proofs.PathRefinementSpan
