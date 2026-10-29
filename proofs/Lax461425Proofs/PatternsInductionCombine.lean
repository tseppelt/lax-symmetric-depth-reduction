import Lax461425Proofs.PatternsInductionOrbitDecomp

/-!
**Combining all children of a gate `g` into a single witness.** By strong induction on the
`Finset` of remaining, not-yet-covered children (a `G`-invariant subset of `g`'s children,
`G := fixingSubgroup (Γ n) (sup g)`), peeling one `G`-orbit off at a time: either the trivial
(`N = ∅`) orbit via `PatternsInductionChild.exists_pad_of_child`, or a genuine support-changing
orbit via `PatternsInductionOrbitPsi.exists_ψOrbitSum`/`exists_ψOrbitProd`.
-/

namespace Lax461425Proofs.PatternsInductionCombine

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open Lax461425Proofs.PatternsSupportDepth Lax461425Proofs.PatternsInductionSetup
open Lax461425Proofs.PatternsInductionNidx Lax461425Proofs.PatternsInductionTransitive
open Lax461425Proofs.PatternsRestrictedY Lax461425Proofs.PatternsInductionOrbitMap
open Lax461425Proofs.PatternsInductionOrbitSum Lax461425Proofs.PatternsInductionOrbitWitness
open Lax461425Proofs.PatternsInductionOrbitFinal Lax461425Proofs.PatternsInductionOrbitDecomp
open Lax461425Proofs.PatternsInductionPsiH Lax461425Proofs.RigidComputes
open Lax461425Proofs.PatternsInductionChild Lax461425Proofs.PatternsRestrictedMono
open Lax461425Proofs.PatternsLabelledOps Lax461425Proofs.PatternsLabelledSpanMul
open Lax461425Proofs.PatternsRestrictedProd Lax461425Proofs.PatternsInductionOrbitPsi
open scoped Classical

set_option maxHeartbeats 4000000

variable {K : Type*} [Field K] [CharZero K] {n : ℕ} {C : Circuit (Fin n × Fin n) K}
variable (hrig : IsRigid C) (hn : 2 * supportSize C < n) {g : C.Gate} {k : ℕ}

/-- **Combining a `G`-invariant `Finset` of children of `g` into a single `Σ`-witness.** -/
theorem exists_combine_sum (hsize : supportSize C ≤ k)
    (q : C.Gate → MvPolynomial (Fin n × Fin n) K)
    (hq : ∀ h', 0 < C.wire g h' → C.ComputesAt h' (q h'))
    (hφ : ∀ h', 0 < C.wire g h' →
      ∃ φh' : (Fin (leftCard hrig hn h') → Fin n) → (Fin (rightCard hrig hn h') → Fin n) →
        MvPolynomial (Fin n × Fin n) K,
        φh' ∈ span𝔗P K (sc C h') k n
          (Finset.univ : Finset (Fin (leftCard hrig hn h') ⊕ Fin (rightCard hrig hn h'))) ∧
        φh' (leftEnum hrig hn h') (rightEnum hrig hn h') = q h') :
    ∀ S : Finset C.Gate, (∀ h' ∈ S, 0 < C.wire g h') →
      (∀ h' ∈ S, ∀ δ ∈ fixingSubgroup (Γ n) (supOf hrig hn g), σOf hrig δ h' ∈ S) →
      ∃ φS : (Fin (leftCard hrig hn g) → Fin n) → (Fin (rightCard hrig hn g) → Fin n) →
        MvPolynomial (Fin n × Fin n) K,
        φS ∈ span𝔗P K (sc C g) k n
          (Finset.univ : Finset (Fin (leftCard hrig hn g) ⊕ Fin (rightCard hrig hn g))) ∧
        φS (leftEnum hrig hn g) (rightEnum hrig hn g) = ∑ h' ∈ S, C.wire g h' • q h' := by
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hSsub hSinv
    by_cases hSe : S = ∅
    · subst hSe
      exact ⟨0, Submodule.zero_mem _, by simp⟩
    · obtain ⟨h0, h0mem⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
      have hwire0 : 0 < C.wire g h0 := hSsub h0 h0mem
      set O := Ofinset hrig hn (g := g) (h := h0) with hOdef
      have hOsub : O ⊆ S := by
        intro h' hh'
        obtain ⟨δ, hδmem, rfl⟩ := mem_Ofinset_iff_exists_δ hrig hn |>.mp hh'
        exact hSinv h0 h0mem δ hδmem
      have h0memO : h0 ∈ O := self_mem_Ofinset hrig hn
      have hS'ssub : S \ O ⊂ S := Finset.sdiff_ssubset hOsub ⟨h0, h0memO⟩
      have hS'sub : ∀ h' ∈ S \ O, 0 < C.wire g h' := fun h' hh' =>
        hSsub h' (Finset.mem_sdiff.mp hh').1
      have hS'inv : ∀ h' ∈ S \ O, ∀ δ ∈ fixingSubgroup (Γ n) (supOf hrig hn g),
          σOf hrig δ h' ∈ S \ O := by
        intro h' hh' δ hδ
        have hh'S : h' ∈ S := (Finset.mem_sdiff.mp hh').1
        have hh'notO : h' ∉ O := (Finset.mem_sdiff.mp hh').2
        refine Finset.mem_sdiff.mpr ⟨hSinv h' hh'S δ hδ, ?_⟩
        intro hmem
        apply hh'notO
        have hδinv : δ⁻¹ ∈ fixingSubgroup (Γ n) (supOf hrig hn g) := Subgroup.inv_mem _ hδ
        have hmem2 := Ofinset_smul_mem hrig hn hδinv hmem
        rwa [σOf_inv_σOf] at hmem2
      obtain ⟨φS', hφS'mem, hφS'val⟩ := ih (S \ O) hS'ssub hS'sub hS'inv
      obtain ⟨φh0, hφh0mem, hφh0val⟩ := hφ h0 hwire0
      have hφh0eval : C.ComputesAt h0 (φh0 (leftEnum hrig hn h0) (rightEnum hrig hn h0)) := by
        rw [hφh0val]; exact hq h0 hwire0
      have hOcontrib : ∃ φO : (Fin (leftCard hrig hn g) → Fin n) →
          (Fin (rightCard hrig hn g) → Fin n) → MvPolynomial (Fin n × Fin n) K,
          φO ∈ span𝔗P K (sc C g) k n
            (Finset.univ : Finset (Fin (leftCard hrig hn g) ⊕ Fin (rightCard hrig hn g))) ∧
          φO (leftEnum hrig hn g) (rightEnum hrig hn g) = ∑ h' ∈ O, C.wire g h' • q h' := by
        by_cases hsub : supOf hrig hn h0 ⊆ supOf hrig hn g
        · have hOsingleton : O = {h0} := by
            apply Finset.eq_singleton_iff_unique_mem.mpr
            refine ⟨h0memO, fun h' hh' => ?_⟩
            obtain ⟨δ, hδmem, rfl⟩ := mem_Ofinset_iff_exists_δ hrig hn |>.mp hh'
            have hδmem' : δ ∈ fixingSubgroup (Γ n) (supOf hrig hn h0) :=
              fixingSubgroup_mono hsub hδmem
            exact (mem_gateStabilizer_iff hrig).mp
              (fixingSubgroup_le_gateStabilizer hrig hn hδmem')
          obtain ⟨ψ, hψmem, hψval⟩ := exists_pad_of_child hrig hn hwire0 hsub φh0 hφh0mem
          refine ⟨(C.wire g h0 : K) • ψ, Submodule.smul_mem _ _ hψmem, ?_⟩
          show (C.wire g h0 : K) • ψ (leftEnum hrig hn g) (rightEnum hrig hn g) = _
          rw [Nat.cast_smul_eq_nsmul, hψval, hφh0val, hOsingleton]
          simp
        · have hchg : ¬ minSupport C h0 ⊆ minSupport C g := by
            rw [← supOf_eq_minSupport hrig hn h0, ← supOf_eq_minSupport hrig hn g]
            exact hsub
          have hdepth : sc C h0 + 1 ≤ sc C g := sc_succ_le_of_changing hwire0 hchg
          obtain ⟨ψOSum, hψOSummem, hψOSumval⟩ :=
            exists_ψOrbitSum hrig hn φh0 hφh0mem hφh0eval hsize
          refine ⟨(C.wire g h0 : K) • ψOSum,
            Submodule.smul_mem _ _ (span𝔗P_mono hdepth hψOSummem), ?_⟩
          show (C.wire g h0 : K) • ψOSum (leftEnum hrig hn g) (rightEnum hrig hn g) = _
          rw [Nat.cast_smul_eq_nsmul, hψOSumval, Finset.smul_sum]
          refine Finset.sum_congr rfl (fun h' hh' => ?_)
          have hc1 := computesAt_qfun hrig hn φh0 hφh0mem hφh0eval hh'
          have hc2 := hq h' (wire_pos_on_Ofinset hrig hn hwire0 hh')
          rw [computesAt_unique C h' hc1 hc2, wire_const_on_Ofinset hrig hn hh']
      obtain ⟨φO, hφOmem, hφOval⟩ := hOcontrib
      refine ⟨φO + φS', Submodule.add_mem _ hφOmem hφS'mem, ?_⟩
      show φO (leftEnum hrig hn g) (rightEnum hrig hn g) +
        φS' (leftEnum hrig hn g) (rightEnum hrig hn g) = _
      rw [hφOval, hφS'val, add_comm, Finset.sum_sdiff hOsub]

/-- **Combining a `G`-invariant `Finset` of children of `g` into a single `Π`-witness.** -/
theorem exists_combine_prod (hsize : supportSize C ≤ k)
    (hlr : leftCard hrig hn g + rightCard hrig hn g ≤ k)
    (q : C.Gate → MvPolynomial (Fin n × Fin n) K)
    (hq : ∀ h', 0 < C.wire g h' → C.ComputesAt h' (q h'))
    (hφ : ∀ h', 0 < C.wire g h' →
      ∃ φh' : (Fin (leftCard hrig hn h') → Fin n) → (Fin (rightCard hrig hn h') → Fin n) →
        MvPolynomial (Fin n × Fin n) K,
        φh' ∈ span𝔗P K (sc C h') k n
          (Finset.univ : Finset (Fin (leftCard hrig hn h') ⊕ Fin (rightCard hrig hn h'))) ∧
        φh' (leftEnum hrig hn h') (rightEnum hrig hn h') = q h') :
    ∀ S : Finset C.Gate, (∀ h' ∈ S, 0 < C.wire g h') →
      (∀ h' ∈ S, ∀ δ ∈ fixingSubgroup (Γ n) (supOf hrig hn g), σOf hrig δ h' ∈ S) →
      ∃ φS : (Fin (leftCard hrig hn g) → Fin n) → (Fin (rightCard hrig hn g) → Fin n) →
        MvPolynomial (Fin n × Fin n) K,
        φS ∈ span𝔗P K (sc C g) k n
          (Finset.univ : Finset (Fin (leftCard hrig hn g) ⊕ Fin (rightCard hrig hn g))) ∧
        φS (leftEnum hrig hn g) (rightEnum hrig hn g) = ∏ h' ∈ S, q h' ^ C.wire g h' := by
  have hPcard : (Finset.univ : Finset (Fin (leftCard hrig hn g) ⊕ Fin (rightCard hrig hn g))).card
      ≤ k := by
    rw [Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    exact hlr
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hSsub hSinv
    by_cases hSe : S = ∅
    · subst hSe
      exact ⟨1, one_mem_span𝔗P K (sc C g) k n _, by simp⟩
    · obtain ⟨h0, h0mem⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
      have hwire0 : 0 < C.wire g h0 := hSsub h0 h0mem
      set O := Ofinset hrig hn (g := g) (h := h0) with hOdef
      have hOsub : O ⊆ S := by
        intro h' hh'
        obtain ⟨δ, hδmem, rfl⟩ := mem_Ofinset_iff_exists_δ hrig hn |>.mp hh'
        exact hSinv h0 h0mem δ hδmem
      have h0memO : h0 ∈ O := self_mem_Ofinset hrig hn
      have hS'ssub : S \ O ⊂ S := Finset.sdiff_ssubset hOsub ⟨h0, h0memO⟩
      have hS'sub : ∀ h' ∈ S \ O, 0 < C.wire g h' := fun h' hh' =>
        hSsub h' (Finset.mem_sdiff.mp hh').1
      have hS'inv : ∀ h' ∈ S \ O, ∀ δ ∈ fixingSubgroup (Γ n) (supOf hrig hn g),
          σOf hrig δ h' ∈ S \ O := by
        intro h' hh' δ hδ
        have hh'S : h' ∈ S := (Finset.mem_sdiff.mp hh').1
        have hh'notO : h' ∉ O := (Finset.mem_sdiff.mp hh').2
        refine Finset.mem_sdiff.mpr ⟨hSinv h' hh'S δ hδ, ?_⟩
        intro hmem
        apply hh'notO
        have hδinv : δ⁻¹ ∈ fixingSubgroup (Γ n) (supOf hrig hn g) := Subgroup.inv_mem _ hδ
        have hmem2 := Ofinset_smul_mem hrig hn hδinv hmem
        rwa [σOf_inv_σOf] at hmem2
      obtain ⟨φS', hφS'mem, hφS'val⟩ := ih (S \ O) hS'ssub hS'sub hS'inv
      obtain ⟨φh0, hφh0mem, hφh0val⟩ := hφ h0 hwire0
      have hφh0eval : C.ComputesAt h0 (φh0 (leftEnum hrig hn h0) (rightEnum hrig hn h0)) := by
        rw [hφh0val]; exact hq h0 hwire0
      have hOcontrib : ∃ φO : (Fin (leftCard hrig hn g) → Fin n) →
          (Fin (rightCard hrig hn g) → Fin n) → MvPolynomial (Fin n × Fin n) K,
          φO ∈ span𝔗P K (sc C g) k n
            (Finset.univ : Finset (Fin (leftCard hrig hn g) ⊕ Fin (rightCard hrig hn g))) ∧
          φO (leftEnum hrig hn g) (rightEnum hrig hn g) = ∏ h' ∈ O, q h' ^ C.wire g h' := by
        by_cases hsub : supOf hrig hn h0 ⊆ supOf hrig hn g
        · have hOsingleton : O = {h0} := by
            apply Finset.eq_singleton_iff_unique_mem.mpr
            refine ⟨h0memO, fun h' hh' => ?_⟩
            obtain ⟨δ, hδmem, rfl⟩ := mem_Ofinset_iff_exists_δ hrig hn |>.mp hh'
            have hδmem' : δ ∈ fixingSubgroup (Γ n) (supOf hrig hn h0) :=
              fixingSubgroup_mono hsub hδmem
            exact (mem_gateStabilizer_iff hrig).mp
              (fixingSubgroup_le_gateStabilizer hrig hn hδmem')
          obtain ⟨ψ, hψmem, hψval⟩ := exists_pad_of_child hrig hn hwire0 hsub φh0 hφh0mem
          refine ⟨fun v w => ψ v w ^ C.wire g h0, span𝔗P_pow_mem hPcard hψmem _, ?_⟩
          show ψ (leftEnum hrig hn g) (rightEnum hrig hn g) ^ C.wire g h0 = _
          rw [hψval, hφh0val, hOsingleton]
          simp
        · have hchg : ¬ minSupport C h0 ⊆ minSupport C g := by
            rw [← supOf_eq_minSupport hrig hn h0, ← supOf_eq_minSupport hrig hn g]
            exact hsub
          have hdepth : sc C h0 + 1 ≤ sc C g := sc_succ_le_of_changing hwire0 hchg
          obtain ⟨ψOProd, hψOProdmem, hψOProdval⟩ :=
            exists_ψOrbitProd hrig hn φh0 hφh0mem hφh0eval hsize hlr
          refine ⟨fun v w => ψOProd v w ^ C.wire g h0,
            span𝔗P_pow_mem hPcard (span𝔗P_mono hdepth hψOProdmem) _, ?_⟩
          show ψOProd (leftEnum hrig hn g) (rightEnum hrig hn g) ^ C.wire g h0 = _
          rw [hψOProdval, ← Finset.prod_pow]
          refine Finset.prod_congr rfl (fun h' hh' => ?_)
          have hc1 := computesAt_qfun hrig hn φh0 hφh0mem hφh0eval hh'
          have hc2 := hq h' (wire_pos_on_Ofinset hrig hn hwire0 hh')
          rw [computesAt_unique C h' hc1 hc2, wire_const_on_Ofinset hrig hn hh']
      obtain ⟨φO, hφOmem, hφOval⟩ := hOcontrib
      refine ⟨fun v w => φO v w * φS' v w, span𝔗P_mul_mem hPcard hφOmem hφS'mem, ?_⟩
      show φO (leftEnum hrig hn g) (rightEnum hrig hn g) *
        φS' (leftEnum hrig hn g) (rightEnum hrig hn g) = _
      rw [hφOval, hφS'val, mul_comm, Finset.prod_sdiff hOsub]

end Lax461425Proofs.PatternsInductionCombine
