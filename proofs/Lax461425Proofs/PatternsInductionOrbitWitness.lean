import Lax461425Proofs.PatternsInductionOrbitSum

/-!
**The `Finpartition` of `Y_u` by `hYtot`-value, and its uniform block size.** Builds the
partition `Qpart` of `Yu` whose blocks are the fibres of `hYtot` (via
`Finpartition.ofSetSetoid` on the "same `hYtot`-value" setoid), shows every block has the same
size `c` (via `PatternsInductionOrbitSum.card_filter_hYtot_eq`), and records that `Yu` itself is
nonempty (it contains the real `N`-tuple), so `c ≠ 0`.
-/

namespace Lax461425Proofs.PatternsInductionOrbitWitness

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open Lax461425Proofs.PatternsSupportDepth Lax461425Proofs.PatternsInductionSetup
open Lax461425Proofs.PatternsInductionNidx Lax461425Proofs.PatternsInductionTransitive
open Lax461425Proofs.PatternsRestrictedY Lax461425Proofs.PatternsInductionOrbitMap
open Lax461425Proofs.PatternsInductionReindex Lax461425Proofs.PatternsLabelledOps
open Lax461425Proofs.PatternsInductionHomRename Lax461425Proofs.PatternsInductionEquivariant
open Lax461425Proofs.RigidComputes Lax461425Proofs.PatternsInductionPsiH
open Lax461425Proofs.PatternsRestrictedSum Lax461425Proofs.PatternsRestrictedProd
open Lax461425Proofs.PatternsRestrictedMono Lax461425Proofs.PatternsInductionOrbitSum
open scoped Classical

set_option maxHeartbeats 4000000

variable {K : Type*} [Field K] [CharZero K] {n : ℕ} {C : Circuit (Fin n × Fin n) K}
variable (hrig : IsRigid C) (hn : 2 * supportSize C < n) {g h : C.Gate}

/-! ### A local abbreviation for the type of pairs -/

/-- The type of pairs `Yu` consists of, for this `g, h`. -/
abbrev Pairs : Type := (Fin (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h)) → Fin n) ×
  (Fin (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) → Fin n)

/-! ### `Yu` is nonempty -/

omit [Field K] [CharZero K] in
/-- The real `N`-tuple lies in `Yu`. -/
theorem yReal_mem_Yu :
    (yReal (leftEnum hrig hn g) (leftEnum hrig hn h),
      yReal (rightEnum hrig hn g) (rightEnum hrig hn h)) ∈ Yu hrig hn := by
  rw [Yu, mem_Y]
  constructor
  · rw [Fin.append_injective_iff]
    refine ⟨leftEnum_injective hrig hn g, yReal_injective (leftEnum_injective hrig hn h), ?_⟩
    intro i j hij
    exact yReal_disjoint_v j ⟨i, hij⟩
  · rw [Fin.append_injective_iff]
    refine ⟨rightEnum_injective hrig hn g, yReal_injective (rightEnum_injective hrig hn h), ?_⟩
    intro i j hij
    exact yReal_disjoint_v j ⟨i, hij⟩

/-! ### The `Finpartition` of `Yu` by `hYtot`-value -/

/-- The "same `hYtot`-value" setoid on pairs. -/
noncomputable def hYtotSetoid : Setoid (Pairs hrig hn (g := g) (h := h)) where
  r a b := hYtot hrig hn a.1 a.2 = hYtot hrig hn b.1 b.2
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- **`Qpart`**: the `Finpartition` of `Yu` into the fibres of `hYtot`. -/
noncomputable def Qpart : Finpartition (Yu hrig hn (g := g) (h := h)) :=
  Finpartition.ofSetSetoid (hYtotSetoid hrig hn) (Yu hrig hn)

omit [Field K] [CharZero K] in
theorem exists_rep_of_mem_Qpart {B : Finset (Pairs hrig hn (g := g) (h := h))}
    (hB : B ∈ (Qpart hrig hn (g := g) (h := h)).parts) :
    ∃ a : Pairs hrig hn (g := g) (h := h), a ∈ Yu hrig hn ∧ B = (Yu hrig hn).filter
      (fun x : Pairs hrig hn (g := g) (h := h) => hYtot hrig hn a.1 a.2 = hYtot hrig hn x.1 x.2) := by
  have heq : (Qpart hrig hn (g := g) (h := h)).parts = (Yu hrig hn).image
      (fun a => (Yu hrig hn).filter (fun x => hYtotSetoid hrig hn |>.r a x)) :=
    Finpartition.ofSetSetoid_parts ..
  rw [heq] at hB
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hB
  exact ⟨a, ha, rfl⟩

omit [Field K] [CharZero K] in
theorem mem_of_mem_rep_filter {a : Pairs hrig hn (g := g) (h := h)} (ha : a ∈ Yu hrig hn) :
    a ∈ (Yu hrig hn).filter
      (fun x : Pairs hrig hn (g := g) (h := h) => hYtot hrig hn a.1 a.2 = hYtot hrig hn x.1 x.2) :=
  Finset.mem_filter.mpr ⟨ha, rfl⟩

/-! ### Uniform block size -/

/-- **`cBlock`**: the common size of every block of `Qpart`, realised by the block containing
the real `N`-tuple. -/
noncomputable def cBlock : ℕ :=
  ((Yu hrig hn (g := g) (h := h)).filter
    (fun x : Pairs hrig hn (g := g) (h := h) => hYtot hrig hn
      (yReal (leftEnum hrig hn g) (leftEnum hrig hn h))
      (yReal (rightEnum hrig hn g) (rightEnum hrig hn h)) = hYtot hrig hn x.1 x.2)).card

omit [Field K] [CharZero K] in
theorem card_eq_cBlock {B : Finset (Pairs hrig hn (g := g) (h := h))}
    (hB : B ∈ (Qpart hrig hn (g := g) (h := h)).parts) :
    B.card = cBlock hrig hn (g := g) (h := h) := by
  obtain ⟨a, ha, rfl⟩ := exists_rep_of_mem_Qpart hrig hn hB
  exact card_filter_hYtot_eq hrig hn ha (yReal_mem_Yu hrig hn)

omit [Field K] [CharZero K] in
theorem cBlock_ne_zero : cBlock hrig hn (g := g) (h := h) ≠ 0 := by
  rw [cBlock, Finset.card_ne_zero]
  exact ⟨_, mem_of_mem_rep_filter hrig hn (yReal_mem_Yu hrig hn)⟩

end Lax461425Proofs.PatternsInductionOrbitWitness
