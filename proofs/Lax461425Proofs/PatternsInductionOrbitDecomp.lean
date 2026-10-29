import Lax461425Proofs.PatternsInductionOrbitPsi
import Lax461425Proofs.PatternsInductionOrbit

/-!
**Orbit-decomposition facts needed to combine all children of a gate `g`.** Relates
`Ofinset hrig hn g h` (the image of `hYtot`, from `PatternsInductionOrbitFinal`) to the
group-theoretic description "the orbit of `h` under `G := fixingSubgroup (Γ n) (sup g)`"
(`mem_Ofinset_iff_exists_δ`), and records that `G ≤ gateStabilizer hrig g` (so `G` permutes the
children of `g`, preserving wire multiplicity exactly, via `PatternsInductionOrbit`'s
`wire_eq_of_mem_gateStabilizer`) and that `Ofinset hrig hn g h` is itself `G`-invariant and
contains `h`.
-/

namespace Lax461425Proofs.PatternsInductionOrbitDecomp

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open Lax461425Proofs.PatternsSupportDepth Lax461425Proofs.PatternsInductionSetup
open Lax461425Proofs.PatternsInductionNidx Lax461425Proofs.PatternsInductionTransitive
open Lax461425Proofs.PatternsRestrictedY Lax461425Proofs.PatternsInductionOrbitMap
open Lax461425Proofs.PatternsInductionOrbitSum Lax461425Proofs.PatternsInductionOrbitWitness
open Lax461425Proofs.PatternsInductionOrbitFinal Lax461425Proofs.PatternsInductionOrbit
open Lax461425Proofs.PatternsInductionPsiH
open scoped Classical

set_option maxHeartbeats 4000000

variable {K : Type*} [Field K] [CharZero K] {n : ℕ} {C : Circuit (Fin n × Fin n) K}
variable (hrig : IsRigid C) (hn : 2 * supportSize C < n) {g h : C.Gate}

omit [Field K] [CharZero K] in
/-- **`G ≤ gateStabilizer hrig g`.** -/
theorem fixingSubgroup_le_gateStabilizer :
    fixingSubgroup (Γ n) (supOf hrig hn g) ≤ gateStabilizer hrig g :=
  (isSupport_iff_fixingSubgroup_le hrig g (supOf hrig hn g)).mp (isSupport_supOf hrig hn g)

omit [Field K] [CharZero K] in
/-- **The group-theoretic description of `Ofinset`.** -/
theorem mem_Ofinset_iff_exists_δ {h' : C.Gate} :
    h' ∈ Ofinset hrig hn (g := g) (h := h) ↔
      ∃ δ ∈ fixingSubgroup (Γ n) (supOf hrig hn g), σOf hrig δ h = h' := by
  constructor
  · intro hh'
    obtain ⟨x, hx, hxeq⟩ := mem_Ofinset_iff hrig hn |>.mp hh'
    obtain ⟨δ, hδmem, hδy, hδz⟩ := exists_γ_of_mem_Y hrig hn hx
    exact ⟨δ, hδmem, (hYtot_eq_of_valid hrig hn hx hδmem hδy hδz).symm.trans hxeq⟩
  · rintro ⟨δ, hδmem, rfl⟩
    refine mem_Ofinset_iff hrig hn |>.mpr
      ⟨actOn hrig hn δ (yReal (leftEnum hrig hn g) (leftEnum hrig hn h),
        yReal (rightEnum hrig hn g) (rightEnum hrig hn h)), ?_, ?_⟩
    · exact actOn_mem_Yu hrig hn hδmem (yReal_mem_Yu hrig hn)
    · have h0 : hYtot hrig hn (yReal (leftEnum hrig hn g) (leftEnum hrig hn h))
          (yReal (rightEnum hrig hn g) (rightEnum hrig hn h)) = h :=
        hYtot_eq_of_valid hrig hn (yReal_mem_Yu hrig hn) (Subgroup.one_mem _) (by
          funext i; show (1 : Equiv.Perm (Fin n)) _ = _; rfl) (by
          funext j; show (1 : Equiv.Perm (Fin n)) _ = _; rfl) |>.trans (by rw [σOf_one]; rfl)
      have h1 : hYtot hrig hn
          (actOn hrig hn δ (yReal (leftEnum hrig hn g) (leftEnum hrig hn h),
            yReal (rightEnum hrig hn g) (rightEnum hrig hn h))).1
          (actOn hrig hn δ (yReal (leftEnum hrig hn g) (leftEnum hrig hn h),
            yReal (rightEnum hrig hn g) (rightEnum hrig hn h))).2 =
          σOf hrig δ (hYtot hrig hn (yReal (leftEnum hrig hn g) (leftEnum hrig hn h))
            (yReal (rightEnum hrig hn g) (rightEnum hrig hn h))) :=
        hYtot_smul hrig hn hδmem (yReal_mem_Yu hrig hn)
      rw [h0] at h1
      exact h1

omit [Field K] [CharZero K] in
/-- `h` lies in its own orbit. -/
theorem self_mem_Ofinset : h ∈ Ofinset hrig hn (g := g) (h := h) :=
  mem_Ofinset_iff_exists_δ hrig hn |>.mpr ⟨1, Subgroup.one_mem _, by rw [σOf_one]; rfl⟩

omit [Field K] [CharZero K] in
/-- `Ofinset hrig hn g h` is itself `G`-invariant: applying `σOf hrig δ` to any of its elements,
for `δ ∈ G`, stays within it. -/
theorem Ofinset_smul_mem {δ : Γ n} (hδ : δ ∈ fixingSubgroup (Γ n) (supOf hrig hn g)) {h' : C.Gate}
    (hh' : h' ∈ Ofinset hrig hn (g := g) (h := h)) :
    σOf hrig δ h' ∈ Ofinset hrig hn (g := g) (h := h) := by
  obtain ⟨δ', hδ'mem, hδ'eq⟩ := mem_Ofinset_iff_exists_δ hrig hn |>.mp hh'
  refine mem_Ofinset_iff_exists_δ hrig hn |>.mpr ⟨δ * δ', Subgroup.mul_mem _ hδ hδ'mem, ?_⟩
  rw [σOf_mul, Equiv.Perm.mul_apply, hδ'eq]

omit [Field K] [CharZero K] in
/-- Wire multiplicity from `g` is constant across `Ofinset hrig hn g h`, provided `h` is a
child of `g`. -/
theorem wire_const_on_Ofinset {h' : C.Gate}
    (hh' : h' ∈ Ofinset hrig hn (g := g) (h := h)) : C.wire g h' = C.wire g h := by
  obtain ⟨δ, hδmem, rfl⟩ := mem_Ofinset_iff_exists_δ hrig hn |>.mp hh'
  exact wire_eq_of_mem_gateStabilizer hrig (fixingSubgroup_le_gateStabilizer hrig hn hδmem) h

omit [Field K] [CharZero K] in
/-- Every element of `Ofinset hrig hn g h` is itself a child of `g`, provided `h` is. -/
theorem wire_pos_on_Ofinset (hwire : 0 < C.wire g h) {h' : C.Gate}
    (hh' : h' ∈ Ofinset hrig hn (g := g) (h := h)) : 0 < C.wire g h' := by
  rw [wire_const_on_Ofinset hrig hn hh']; exact hwire

end Lax461425Proofs.PatternsInductionOrbitDecomp
