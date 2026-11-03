import Lax461425Proofs.PathRefinementSpan
import Lax461425Proofs.PatternsInductionOrbitPsi
import Lax461425Proofs.PatternsInductionChild

/-!
The sum half of Tim's orbit construction preserves the linear refinement. Its polynomial
identity is the existing orbit/fibre calculation, reused verbatim. Only the membership
certificate changes: the all-distinct indicator is a depth-zero factor, and forgetting
labels attaches one new root to the existing decomposition.
-/

namespace Lax461425Proofs.PathRefinementOrbit

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open PatternsSupportAction PatternsSupportBasic PatternsSupportDepth PatternsInductionSetup
open PatternsInductionNidx PatternsInductionTransitive PatternsRestrictedY
open PatternsInductionOrbitMap PatternsInductionReindex PatternsLabelledOps
open PatternsInductionHomRename PatternsInductionEquivariant RigidComputes
open PatternsRestrictedSum PatternsRestrictedProd PatternsRestrictedMono
open PatternsInductionOrbitSum PatternsInductionOrbitWitness PatternsInductionOrbitFinal
open PatternsInductionOrbitPsi PatternsInductionPsiH PatternsInductionChild
open PatternsLabelledBasic PatternsRestrictedDelta PatternsRestrictedDelete
open PathRefinementClass PathRefinementSpan
open scoped Classical

noncomputable section

variable {K : Type*} [Field K] [CharZero K] {n : ℕ} {C : Circuit (Fin n × Fin n) K}
variable (hrig : IsRigid C) (hn : 2 * supportSize C < n) {g h : C.Gate} {k : ℕ}

def orbitSum
    (φh : (Fin (leftCard hrig hn h) → Fin n) → (Fin (rightCard hrig hn h) → Fin n) →
      MvPolynomial (Fin n × Fin n) K) :
    (Fin (leftCard hrig hn g) → Fin n) → (Fin (rightCard hrig hn g) → Fin n) →
      MvPolynomial (Fin n × Fin n) K :=
  (cBlock hrig hn (g := g) (h := h) : K)⁻¹ • sumExt K n (fun v w =>
    δ K (leftCard hrig hn g) (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h))
      (rightCard hrig hn g) (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) n v w *
      ψh hrig hn φh v w)

theorem ψh_mem_linear
    (φh : (Fin (leftCard hrig hn h) → Fin n) → (Fin (rightCard hrig hn h) → Fin n) →
      MvPolynomial (Fin n × Fin n) K)
    (hφh : φh ∈ spanLinear K (sc C h) k n
      (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h)))) :
    ψh hrig hn φh ∈ spanLinear K (sc C h) k n
      ((Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h))).image
        (Sum.map (ιPadEmb (leftEnum_injective hrig hn g) (leftEnum_injective hrig hn h))
          (ιPadEmb (rightEnum_injective hrig hn g) (rightEnum_injective hrig hn h)))) :=
  pad_restrict _ _ φh hφh

theorem orbitSum_mem
    (φh : (Fin (leftCard hrig hn h) → Fin n) → (Fin (rightCard hrig hn h) → Fin n) →
      MvPolynomial (Fin n × Fin n) K)
    (hφh : φh ∈ spanLinear K (sc C h) k n
      (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h))))
    (hsize : supportSize C ≤ k) :
    orbitSum hrig hn (g := g) φh ∈ spanLinear K (sc C h + 1) k n
      (Finset.univ : Finset (Fin (leftCard hrig hn g) ⊕ Fin (rightCard hrig hn g))) := by
  unfold orbitSum
  apply Submodule.smul_mem
  apply restrict_sum
  have heq : (fun v w =>
      δ K (leftCard hrig hn g) (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h))
        (rightCard hrig hn g) (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) n v w *
        ψh hrig hn φh v w) = (fun v w => ψh hrig hn φh v w *
      δ K (leftCard hrig hn g) (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h))
        (rightCard hrig hn g) (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) n v w) := by
    funext v w
    exact mul_comm _ _
  rw [heq]
  apply mul_star (ψh_P_card_le hrig hn hsize) (by decide : 0 ≤ 1) (Nat.zero_le _)
    (ψh_mem_linear hrig hn φh hφh)
  exact δ_mem_span K 0 k n _ (ψh_P_card_le hrig hn hsize)

theorem orbitSum_eval
    (φh : (Fin (leftCard hrig hn h) → Fin n) → (Fin (rightCard hrig hn h) → Fin n) →
      MvPolynomial (Fin n × Fin n) K)
    (hφh : φh ∈ span𝔗P K (sc C h) k n
      (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h))))
    (hcomp : C.ComputesAt h (φh (leftEnum hrig hn h) (rightEnum hrig hn h))) :
    orbitSum hrig hn (g := g) φh (leftEnum hrig hn g) (rightEnum hrig hn g) =
      ∑ h' ∈ Ofinset hrig hn (g := g) (h := h), qfun hrig hn (g := g) φh h' := by
  have hterm : ∀ B ∈ (Qpart hrig hn (g := g) (h := h)).parts,
      (∑ x ∈ B, ψh hrig hn φh (Fin.append (leftEnum hrig hn g) x.1)
        (Fin.append (rightEnum hrig hn g) x.2)) =
      (cBlock hrig hn (g := g) (h := h) : K) • φBlock hrig hn φh B := by
    intro B hB
    rw [Finset.sum_congr rfl (fun x hx => φBlock_const hrig hn φh hφh hcomp B hB x hx),
      Finset.sum_const, card_eq_cBlock hrig hn hB]
    exact (Nat.cast_smul_eq_nsmul K _ _).symm
  calc
    _ = ∑ B ∈ (Qpart hrig hn (g := g) (h := h)).parts, φBlock hrig hn φh B := by
      change (cBlock hrig hn (g := g) (h := h) : K)⁻¹ •
        sumExt K n (fun v w =>
          δ K (leftCard hrig hn g) (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h))
            (rightCard hrig hn g) (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) n v w *
            ψh hrig hn φh v w) (leftEnum hrig hn g) (rightEnum hrig hn g) = _
      rw [sumExt_delta_mul_eq_sum_Y K n _ _ (leftEnum_injective hrig hn g)
        (rightEnum_injective hrig hn g)]
      change (cBlock hrig hn (g := g) (h := h) : K)⁻¹ •
        (∑ yz ∈ Yu hrig hn (g := g) (h := h), ψh hrig hn φh
          (Fin.append (leftEnum hrig hn g) yz.1) (Fin.append (rightEnum hrig hn g) yz.2)) = _
      rw [Finpartition.sum_parts (Qpart hrig hn (g := g) (h := h))]
      rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, smul_smul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (cBlock_ne_zero hrig hn)), one_smul]
    _ = _ := sum_parts_eq_sum_Ofinset hrig hn φh hφh hcomp (φBlock hrig hn φh)
      (fun B hB => φBlock_eq hrig hn φh hB)

theorem exists_orbitSum
    (φh : (Fin (leftCard hrig hn h) → Fin n) → (Fin (rightCard hrig hn h) → Fin n) →
      MvPolynomial (Fin n × Fin n) K)
    (hφh : φh ∈ spanLinear K (sc C h) k n
      (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h))))
    (hcomp : C.ComputesAt h (φh (leftEnum hrig hn h) (rightEnum hrig hn h)))
    (hsize : supportSize C ≤ k) :
    ∃ ψ : (Fin (leftCard hrig hn g) → Fin n) → (Fin (rightCard hrig hn g) → Fin n) →
      MvPolynomial (Fin n × Fin n) K,
      ψ ∈ spanLinear K (sc C h + 1) k n
        (Finset.univ : Finset (Fin (leftCard hrig hn g) ⊕ Fin (rightCard hrig hn g))) ∧
      ψ (leftEnum hrig hn g) (rightEnum hrig hn g) =
        ∑ h' ∈ Ofinset hrig hn (g := g) (h := h), qfun hrig hn (g := g) φh h' :=
  ⟨orbitSum hrig hn φh, orbitSum_mem hrig hn φh hφh hsize,
    orbitSum_eval hrig hn φh (span_forget hφh) hcomp⟩

theorem exists_pad_subset {Δ : ℕ}
    (hsub : supOf hrig hn h ⊆ supOf hrig hn g)
    (φ : (Fin (leftCard hrig hn h) → Fin n) → (Fin (rightCard hrig hn h) → Fin n) →
      MvPolynomial (Fin n × Fin n) K)
    (hφ : φ ∈ spanLinear K Δ k n
      (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h)))) :
    ∃ ψ : (Fin (leftCard hrig hn g) → Fin n) → (Fin (rightCard hrig hn g) → Fin n) →
      MvPolynomial (Fin n × Fin n) K,
      ψ ∈ spanLinear K Δ k n
        (Finset.univ : Finset (Fin (leftCard hrig hn g) ⊕ Fin (rightCard hrig hn g))) ∧
      ψ (leftEnum hrig hn g) (rightEnum hrig hn g) = φ (leftEnum hrig hn h) (rightEnum hrig hn h) := by
  have hsubL : leftPart (supOf hrig hn h) ⊆ leftPart (supOf hrig hn g) := fun i hi => hsub hi
  have hsubR : rightPart (supOf hrig hn h) ⊆ rightPart (supOf hrig hn g) := fun j hj => hsub hj
  have hL : Set.range (leftEnum hrig hn h) ⊆ Set.range (leftEnum hrig hn g) := by
    rw [range_leftEnum, range_leftEnum]
    exact hsubL
  have hR : Set.range (rightEnum hrig hn h) ⊆ Set.range (rightEnum hrig hn g) := by
    rw [range_rightEnum, range_rightEnum]
    exact hsubR
  obtain ⟨ι, hι⟩ := embedding_of_range_subset (leftEnum_injective hrig hn h)
    (leftEnum_injective hrig hn g) hL
  obtain ⟨κ, hκ⟩ := embedding_of_range_subset (rightEnum_injective hrig hn h)
    (rightEnum_injective hrig hn g) hR
  refine ⟨fun v w => φ (v ∘ ι) (w ∘ κ), PathRefinementSpan.pad ι κ φ hφ, ?_⟩
  change φ ((leftEnum hrig hn g) ∘ ι) ((rightEnum hrig hn g) ∘ κ) = _
  rw [hι, hκ]

theorem exists_pad_child (hwire : 0 < C.wire g h)
    (hsub : supOf hrig hn h ⊆ supOf hrig hn g)
    (φ : (Fin (leftCard hrig hn h) → Fin n) → (Fin (rightCard hrig hn h) → Fin n) →
      MvPolynomial (Fin n × Fin n) K)
    (hφ : φ ∈ spanLinear K (sc C h) k n
      (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h)))) :
    ∃ ψ : (Fin (leftCard hrig hn g) → Fin n) → (Fin (rightCard hrig hn g) → Fin n) →
      MvPolynomial (Fin n × Fin n) K,
      ψ ∈ spanLinear K (sc C g) k n
        (Finset.univ : Finset (Fin (leftCard hrig hn g) ⊕ Fin (rightCard hrig hn g))) ∧
      ψ (leftEnum hrig hn g) (rightEnum hrig hn g) = φ (leftEnum hrig hn h) (rightEnum hrig hn h) := by
  obtain ⟨ψ, hψ, he⟩ := exists_pad_subset hrig hn hsub φ hφ
  exact ⟨ψ, PathRefinementClass.span_mono (sc_mono hwire) hψ, he⟩

end

end Lax461425Proofs.PathRefinementOrbit
