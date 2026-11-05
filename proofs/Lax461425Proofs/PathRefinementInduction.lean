import Lax461425Proofs.PatternsInductionMain
import Lax461425Proofs.PathRefinementSums
import Lax461425Proofs.PathRefinementProducts

/-! Tim's gate induction with a linear decomposition certificate at skew product gates. -/
open Lax461425.SymmetricFamilies (MatrixPolynomial)

namespace Lax461425Proofs.PathRefinementInduction

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open Lax461425Proofs.PatternsSupportDepth Lax461425Proofs.PatternsInductionSetup
open Lax461425Proofs.PatternsInductionOrbitDecomp Lax461425Proofs.PatternsInductionOrbit
open Lax461425Proofs.PatternsInductionCombine Lax461425Proofs.PatternsInductionBase
open Lax461425Proofs.PatternsInductionChild Lax461425Proofs.PatternsRestrictedMono
open Lax461425Proofs.PatternsLabelledOps Lax461425Proofs.PatternsLabelledSpanMul
open Lax461425Proofs.ReducedRigid
open PathRefinementClass
open scoped Classical

set_option maxHeartbeats 4000000

variable {K : Type*} [Field K] [CharZero K] {n k : ℕ} {C : Circuit (Fin n × Fin n) K}

/-- **`lem:induction`.** For every gate `g`, there is `φ_g` in the span at depth `sc C g`,
bounded width `k`, whose value at `g`'s own canonical enumeration is a polynomial `g` actually
computes. -/
theorem exists_phi (hskew : Lax461425.CircuitProperties.IsSkew C) (hred : C.IsReduced) (hsym : IsMatrixSymmetric C) (hk : 2 ≤ k)
    (hn' : 2 * k + 1 ≤ n) (hsize : supportSize C ≤ k) (hrig : IsRigid C)
    (hn : 2 * supportSize C < n) (g : C.Gate) :
    ∃ φ : (Fin (leftCard hrig hn g) → Fin n) → (Fin (rightCard hrig hn g) → Fin n) →
      MatrixPolynomial n K,
      φ ∈ spanLinear K (sc C g) k n
        (Finset.univ : Finset (Fin (leftCard hrig hn g) ⊕ Fin (rightCard hrig hn g))) ∧
      C.ComputesAt g (φ (leftEnum hrig hn g) (rightEnum hrig hn g)) := by
  induction g using (RigidHeight.wellFounded_child C).induction with
  | _ g ih =>
    match hg : C.label g with
    | GateLabel.var x =>
        obtain ⟨φ, hm, he⟩ := PatternsInductionMain.exists_phi hred hsym hk hn' hsize hrig hn g
        have hz : sc C g = 0 := sc_eq_zero_of_isInput (by rw [hg]; trivial)
        exact ⟨φ, star_span (by omega : sc C g ≤ 1) hm, he⟩
    | GateLabel.const c =>
        obtain ⟨φ, hm, he⟩ := PatternsInductionMain.exists_phi hred hsym hk hn' hsize hrig hn g
        have hz : sc C g = 0 := sc_eq_zero_of_isInput (by rw [hg]; trivial)
        exact ⟨φ, star_span (by omega : sc C g ≤ 1) hm, he⟩
    | GateLabel.add =>
        set S : Finset C.Gate := Finset.univ.filter (fun h' => 0 < C.wire g h') with hSdef
        have hSsub : ∀ h' ∈ S, 0 < C.wire g h' := fun h' hh' => (Finset.mem_filter.mp hh').2
        have hSinv : ∀ h' ∈ S, ∀ δ ∈ fixingSubgroup (Γ n) (supOf hrig hn g),
            σOf hrig δ h' ∈ S := by
          intro h' hh' δ hδ
          have hwire : 0 < C.wire g h' := hSsub h' hh'
          have hδg : δ ∈ gateStabilizer hrig g := fixingSubgroup_le_gateStabilizer hrig hn hδ
          rw [hSdef, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, (wire_eq_of_mem_gateStabilizer hrig hδg h').symm ▸ hwire⟩
        set q : C.Gate → MatrixPolynomial n K := fun h' =>
          if hh' : 0 < C.wire g h' then
            (ih h' (show RigidHeight.Child C g h' from hh')).choose (leftEnum hrig hn h') (rightEnum hrig hn h')
          else 0 with hqdef
        have hq : ∀ h', 0 < C.wire g h' → C.ComputesAt h' (q h') := by
          intro h' hh'
          simp only [hqdef]; rw [dif_pos hh']
          exact (ih h' (show RigidHeight.Child C g h' from hh')).choose_spec.2
        have hφ : ∀ h', 0 < C.wire g h' →
            ∃ φh' : (Fin (leftCard hrig hn h') → Fin n) → (Fin (rightCard hrig hn h') → Fin n) →
              MatrixPolynomial n K,
              φh' ∈ spanLinear K (sc C h') k n
                (Finset.univ : Finset (Fin (leftCard hrig hn h') ⊕ Fin (rightCard hrig hn h'))) ∧
              φh' (leftEnum hrig hn h') (rightEnum hrig hn h') = q h' := by
          intro h' hh'
          refine ⟨(ih h' (show RigidHeight.Child C g h' from hh')).choose, (ih h' (show RigidHeight.Child C g h' from hh')).choose_spec.1, ?_⟩
          simp only [hqdef]; rw [dif_pos hh']
        obtain ⟨φS, hφSmem, hφSval⟩ :=
          PathRefinementSums.sum_children hrig hn hsize q hq hφ S hSsub hSinv
        refine ⟨φS, hφSmem, ?_⟩
        rw [hφSval]
        have hsum_eq : (∑ h' : C.Gate, C.wire g h' • q h') = ∑ h' ∈ S, C.wire g h' • q h' := by
          rw [hSdef, Finset.sum_filter]
          refine Finset.sum_congr rfl (fun h' _ => ?_)
          by_cases hh' : 0 < C.wire g h'
          · rw [if_pos hh']
          · rw [if_neg hh', Nat.eq_zero_of_not_pos hh', zero_smul]
        rw [← hsum_eq]
        exact Circuit.ComputesAt.add q hg hq
    | GateLabel.mul =>
        set S : Finset C.Gate := Finset.univ.filter (fun h' => 0 < C.wire g h') with hSdef
        have hSsub : ∀ h' ∈ S, 0 < C.wire g h' := fun h' hh' => (Finset.mem_filter.mp hh').2
        have hSinv : ∀ h' ∈ S, ∀ δ ∈ fixingSubgroup (Γ n) (supOf hrig hn g),
            σOf hrig δ h' ∈ S := by
          intro h' hh' δ hδ
          have hwire : 0 < C.wire g h' := hSsub h' hh'
          have hδg : δ ∈ gateStabilizer hrig g := fixingSubgroup_le_gateStabilizer hrig hn hδ
          rw [hSdef, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, (wire_eq_of_mem_gateStabilizer hrig hδg h').symm ▸ hwire⟩
        set q : C.Gate → MatrixPolynomial n K := fun h' =>
          if hh' : 0 < C.wire g h' then
            (ih h' (show RigidHeight.Child C g h' from hh')).choose (leftEnum hrig hn h') (rightEnum hrig hn h')
          else 0 with hqdef
        have hq : ∀ h', 0 < C.wire g h' → C.ComputesAt h' (q h') := by
          intro h' hh'
          simp only [hqdef]; rw [dif_pos hh']
          exact (ih h' (show RigidHeight.Child C g h' from hh')).choose_spec.2
        have hφ : ∀ h', 0 < C.wire g h' →
            ∃ φh' : (Fin (leftCard hrig hn h') → Fin n) → (Fin (rightCard hrig hn h') → Fin n) →
              MatrixPolynomial n K,
              φh' ∈ spanLinear K (sc C h') k n
                (Finset.univ : Finset (Fin (leftCard hrig hn h') ⊕ Fin (rightCard hrig hn h'))) ∧
              φh' (leftEnum hrig hn h') (rightEnum hrig hn h') = q h' := by
          intro h' hh'
          refine ⟨(ih h' (show RigidHeight.Child C g h' from hh')).choose, (ih h' (show RigidHeight.Child C g h' from hh')).choose_spec.1, ?_⟩
          simp only [hqdef]; rw [dif_pos hh']
        have hlr : leftCard hrig hn g + rightCard hrig hn g ≤ k :=
          leftCard_add_rightCard_le hrig hn g hsize
        obtain ⟨φS, hφSmem, hφSval⟩ :=
          PathRefinementProducts.product_children hrig hn hskew hg hsize hlr q hq hφ
        refine ⟨φS, hφSmem, ?_⟩
        rw [hφSval]
        exact Circuit.ComputesAt.mul q hg hq

end Lax461425Proofs.PathRefinementInduction
