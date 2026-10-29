import Lax461425Proofs.PatternsInductionCombine
import Lax461425Proofs.PatternsInductionBase
import Lax461425Proofs.RigidHeight

/-!
**`lem:induction`, assembled.** By well-founded induction on `C.Gate` via the (generic, any
circuit) child relation `RigidHeight.wellFounded_child`, case-splitting on `C.label g`: `var`/
`const` via `PatternsInductionBase.exists_phi_input` (reindexed to `g`'s own canonical arity via
`PatternsInductionChild.exists_pad_of_range_eq`); `add`/`mul` via
`PatternsInductionCombine.exists_combine_sum`/`exists_combine_prod`, applied to the full
`Finset` of `g`'s children (`G`-invariant, by `PatternsInductionOrbit.wire_eq_of_mem_gateStabilizer`
combined with `G ≤ gateStabilizer hrig g`), fed by the induction hypothesis at every child.
-/

namespace Lax461425Proofs.PatternsInductionMain

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open Lax461425Proofs.PatternsSupportDepth Lax461425Proofs.PatternsInductionSetup
open Lax461425Proofs.PatternsInductionOrbitDecomp Lax461425Proofs.PatternsInductionOrbit
open Lax461425Proofs.PatternsInductionCombine Lax461425Proofs.PatternsInductionBase
open Lax461425Proofs.PatternsInductionChild Lax461425Proofs.PatternsRestrictedMono
open Lax461425Proofs.PatternsLabelledOps Lax461425Proofs.PatternsLabelledSpanMul
open Lax461425Proofs.ReducedRigid
open scoped Classical

set_option maxHeartbeats 4000000

variable {K : Type*} [Field K] [CharZero K] {n k : ℕ} {C : Circuit (Fin n × Fin n) K}

/-- **`lem:induction`.** For every gate `g`, there is `φ_g` in the span at depth `sc C g`,
bounded width `k`, whose value at `g`'s own canonical enumeration is a polynomial `g` actually
computes. -/
theorem exists_phi (hred : C.IsReduced) (hsym : IsMatrixSymmetric C) (hk : 2 ≤ k)
    (hn' : 2 * k + 1 ≤ n) (hsize : supportSize C ≤ k) (hrig : IsRigid C)
    (hn : 2 * supportSize C < n) (g : C.Gate) :
    ∃ φ : (Fin (leftCard hrig hn g) → Fin n) → (Fin (rightCard hrig hn g) → Fin n) →
      MvPolynomial (Fin n × Fin n) K,
      φ ∈ span𝔗P K (sc C g) k n
        (Finset.univ : Finset (Fin (leftCard hrig hn g) ⊕ Fin (rightCard hrig hn g))) ∧
      C.ComputesAt g (φ (leftEnum hrig hn g) (rightEnum hrig hn g)) := by
  induction g using (RigidHeight.wellFounded_child C).induction with
  | _ g ih =>
    match hg : C.label g with
    | GateLabel.var x =>
        obtain ⟨i, j⟩ := x
        obtain ⟨φ₀, hφ₀mem, hφ₀eq, hsc0, hrangeL, hrangeR⟩ :=
          exists_phi_input hk hn' hred hsym hsize hg
        have hv : Function.Injective (fun _ : Fin 1 => i) := fun a b _ => Subsingleton.elim a b
        have hw : Function.Injective (fun _ : Fin 1 => j) := fun a b _ => Subsingleton.elim a b
        obtain ⟨ψ, hψmem, hψeq⟩ :=
          exists_pad_of_range_eq hrig hn hv hw hrangeL hrangeR φ₀ hφ₀mem
        refine ⟨ψ, hsc0 ▸ hψmem, ?_⟩
        rw [hψeq, hφ₀eq]
        exact Circuit.ComputesAt.var hg
    | GateLabel.const c =>
        have hinput : (C.label g).IsInput := by rw [hg]; trivial
        have hsc0 : sc C g = 0 := sc_eq_zero_of_isInput hinput
        have hsup0 : supOf hrig hn g = (∅ : Set (Fin n ⊕ Fin n)) := supOf_const hg hred hrig hn
        have hv0 : Function.Injective (fun i : Fin 0 => i.elim0 : Fin 0 → Fin n) :=
          fun a => a.elim0
        have hvrange : Set.range (fun i : Fin 0 => i.elim0 : Fin 0 → Fin n) =
            leftPart (supOf hrig hn g) := by
          rw [hsup0]
          apply Set.eq_empty_iff_forall_notMem.mpr
          rintro x ⟨i, -⟩
          exact i.elim0
        have hwrange : Set.range (fun i : Fin 0 => i.elim0 : Fin 0 → Fin n) =
            rightPart (supOf hrig hn g) := by
          rw [hsup0]
          apply Set.eq_empty_iff_forall_notMem.mpr
          rintro x ⟨i, -⟩
          exact i.elim0
        have hφ₀mem : (fun (_ : Fin 0 → Fin n) (_ : Fin 0 → Fin n) =>
            (1 : MvPolynomial (Fin n × Fin n) K))
            ∈ span𝔗P K 0 k n (Finset.univ : Finset (Fin 0 ⊕ Fin 0)) :=
          one_mem_span𝔗P K 0 k n _
        obtain ⟨ψ, hψmem, hψeq⟩ := exists_pad_of_range_eq hrig hn hv0 hv0 hvrange hwrange _ hφ₀mem
        refine ⟨c • ψ, hsc0 ▸ Submodule.smul_mem _ _ hψmem, ?_⟩
        have hval : (c • ψ) (leftEnum hrig hn g) (rightEnum hrig hn g) = MvPolynomial.C c := by
          show c • ψ (leftEnum hrig hn g) (rightEnum hrig hn g) = MvPolynomial.C c
          rw [hψeq, Algebra.smul_def, MvPolynomial.algebraMap_eq, mul_one]
        rw [hval]
        exact Circuit.ComputesAt.const hg
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
        set q : C.Gate → MvPolynomial (Fin n × Fin n) K := fun h' =>
          if hh' : 0 < C.wire g h' then
            (ih h' (show RigidHeight.Child C g h' from hh')).choose (leftEnum hrig hn h') (rightEnum hrig hn h')
          else 0 with hqdef
        have hq : ∀ h', 0 < C.wire g h' → C.ComputesAt h' (q h') := by
          intro h' hh'
          simp only [hqdef]; rw [dif_pos hh']
          exact (ih h' (show RigidHeight.Child C g h' from hh')).choose_spec.2
        have hφ : ∀ h', 0 < C.wire g h' →
            ∃ φh' : (Fin (leftCard hrig hn h') → Fin n) → (Fin (rightCard hrig hn h') → Fin n) →
              MvPolynomial (Fin n × Fin n) K,
              φh' ∈ span𝔗P K (sc C h') k n
                (Finset.univ : Finset (Fin (leftCard hrig hn h') ⊕ Fin (rightCard hrig hn h'))) ∧
              φh' (leftEnum hrig hn h') (rightEnum hrig hn h') = q h' := by
          intro h' hh'
          refine ⟨(ih h' (show RigidHeight.Child C g h' from hh')).choose, (ih h' (show RigidHeight.Child C g h' from hh')).choose_spec.1, ?_⟩
          simp only [hqdef]; rw [dif_pos hh']
        obtain ⟨φS, hφSmem, hφSval⟩ :=
          exists_combine_sum hrig hn hsize q hq hφ S hSsub hSinv
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
        set q : C.Gate → MvPolynomial (Fin n × Fin n) K := fun h' =>
          if hh' : 0 < C.wire g h' then
            (ih h' (show RigidHeight.Child C g h' from hh')).choose (leftEnum hrig hn h') (rightEnum hrig hn h')
          else 0 with hqdef
        have hq : ∀ h', 0 < C.wire g h' → C.ComputesAt h' (q h') := by
          intro h' hh'
          simp only [hqdef]; rw [dif_pos hh']
          exact (ih h' (show RigidHeight.Child C g h' from hh')).choose_spec.2
        have hφ : ∀ h', 0 < C.wire g h' →
            ∃ φh' : (Fin (leftCard hrig hn h') → Fin n) → (Fin (rightCard hrig hn h') → Fin n) →
              MvPolynomial (Fin n × Fin n) K,
              φh' ∈ span𝔗P K (sc C h') k n
                (Finset.univ : Finset (Fin (leftCard hrig hn h') ⊕ Fin (rightCard hrig hn h'))) ∧
              φh' (leftEnum hrig hn h') (rightEnum hrig hn h') = q h' := by
          intro h' hh'
          refine ⟨(ih h' (show RigidHeight.Child C g h' from hh')).choose, (ih h' (show RigidHeight.Child C g h' from hh')).choose_spec.1, ?_⟩
          simp only [hqdef]; rw [dif_pos hh']
        have hlr : leftCard hrig hn g + rightCard hrig hn g ≤ k :=
          leftCard_add_rightCard_le hrig hn g hsize
        obtain ⟨φS, hφSmem, hφSval⟩ :=
          exists_combine_prod hrig hn hsize hlr q hq hφ S hSsub hSinv
        refine ⟨φS, hφSmem, ?_⟩
        rw [hφSval]
        have hprod_eq : (∏ h' : C.Gate, q h' ^ C.wire g h') = ∏ h' ∈ S, q h' ^ C.wire g h' := by
          rw [hSdef, Finset.prod_filter]
          refine Finset.prod_congr rfl (fun h' _ => ?_)
          by_cases hh' : 0 < C.wire g h'
          · rw [if_pos hh']
          · rw [if_neg hh', Nat.eq_zero_of_not_pos hh', pow_zero]
        rw [← hprod_eq]
        exact Circuit.ComputesAt.mul q hg hq

end Lax461425Proofs.PatternsInductionMain
