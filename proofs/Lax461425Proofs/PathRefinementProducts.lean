import Lax461425Proofs.PathRefinementInputProduct
import Lax461425Proofs.PathRefinementOrbit
import Lax461425Proofs.PathRefinementSkew

/-! The skew product step: one linear factor times Tim's input-only star factor. -/
open Lax461425.SymmetricFamilies (MatrixPolynomial)

namespace Lax461425Proofs.PathRefinementProducts

open Lax461425.Circuits Lax461425.CircuitProperties Lax461425.MatrixSymmetry Lax461425.Supports
open PatternsInductionSetup PatternsSupportAction PatternsSupportBasic PatternsSupportDepth
open PatternsInductionOrbit PatternsLabelledOps PathRefinementClass PathRefinementSkew
open PatternsInductionOrbitDecomp
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {n : ℕ} {C : Circuit (Fin n × Fin n) K}
variable (hrig : IsRigid C) (hn : 2 * supportSize C < n) {g : C.Gate} {k : ℕ}

theorem product_children (hskew : IsSkew C) (hg : C.label g = .mul)
    (hsize : supportSize C ≤ k) (hlr : leftCard hrig hn g + rightCard hrig hn g ≤ k)
    (q : C.Gate → MatrixPolynomial n K)
    (hq : ∀ h, 0 < C.wire g h → C.ComputesAt h (q h))
    (hφ : ∀ h, 0 < C.wire g h →
      ∃ φ : (Fin (leftCard hrig hn h) → Fin n) → (Fin (rightCard hrig hn h) → Fin n) →
          MatrixPolynomial n K,
        φ ∈ spanLinear K (sc C h) k n Finset.univ ∧
        φ (leftEnum hrig hn h) (rightEnum hrig hn h) = q h) :
    ∃ φ : (Fin (leftCard hrig hn g) → Fin n) → (Fin (rightCard hrig hn g) → Fin n) →
        MatrixPolynomial n K,
      φ ∈ spanLinear K (sc C g) k n Finset.univ ∧
      φ (leftEnum hrig hn g) (rightEnum hrig hn g) = ∏ h, q h ^ C.wire g h := by
  have hsub : ∀ h ∈ inputChildren C g, 0 < C.wire g h :=
    fun _ hh => (Finset.mem_filter.mp hh).2.1
  have hi : ∀ h ∈ inputChildren C g, (C.label h).IsInput :=
    fun _ hh => (Finset.mem_filter.mp hh).2.2
  have hinv : ∀ h ∈ inputChildren C g,
      ∀ δ ∈ fixingSubgroup (Γ n) (supOf hrig hn g), σOf hrig δ h ∈ inputChildren C g := by
    intro h hh δ hδ
    have hδg := fixingSubgroup_le_gateStabilizer hrig hn hδ
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (wire_eq_of_mem_gateStabilizer hrig hδg h).symm ▸ hsub h hh,
      (isInput_image (σOf_extends hrig δ) h).mpr (hi h hh)⟩
  have hφold : ∀ h, 0 < C.wire g h → ∃ φ,
      φ ∈ span𝔗P K (sc C h) k n Finset.univ ∧
      φ (leftEnum hrig hn h) (rightEnum hrig hn h) = q h := by
    intro h hw
    obtain ⟨φ, hm, he⟩ := hφ h hw
    exact ⟨φ, span_forget hm, he⟩
  obtain ⟨ψ, hψ, hψ₁, heψ⟩ := PathRefinementInputProduct.input_product hrig hn hsize hlr
    q hq hφold (inputChildren C g) hsub hinv hi
  by_cases hall : ∀ h, 0 < C.wire g h → (C.label h).IsInput
  · exact ⟨ψ, PathRefinementSpan.star_at_depth hψ₁ hψ,
      heψ.trans (product_all_inputs g hall q).symm⟩
  · push Not at hall
    obtain ⟨h, hw, hni⟩ := hall
    obtain ⟨φ, hφm, heφ⟩ := hφ h hw
    obtain ⟨χ, hχ, heχ⟩ := PathRefinementOrbit.exists_pad_child hrig hn hw
      (internal_sup_subset hrig hn hskew hg hni hw) φ hφm
    have hcard : (Finset.univ : Finset (Fin (leftCard hrig hn g) ⊕ Fin (rightCard hrig hn g))).card ≤ k := by
      simpa using hlr
    refine ⟨fun v w => χ v w * ψ v w,
      PathRefinementSpan.mul_star_at_depth hcard hχ hψ₁ hψ, ?_⟩
    change χ _ _ * ψ _ _ = _
    rw [heχ, heφ, heψ, product_one_internal hskew hg hni hw q]

end Lax461425Proofs.PathRefinementProducts
