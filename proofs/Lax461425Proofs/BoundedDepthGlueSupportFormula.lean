import Lax461425Proofs.BoundedDepthGlueSymmetric
import Lax461425Proofs.BoundedDepthReducedFormula
import Lax461425Proofs.BoundedDepthEmbed
import Lax461425Proofs.PatternsSupportBasic

/-!
Exact formulas for `minSupport` of the rigidified glue circuit's gates: block gates inherit
their block's own `minSupport` exactly (`minSupport_reduced_blk_eq`), while every glue gate
(`scaledG`, `constG`, `outGG`) has empty `minSupport` (`minSupport_reduced_glue_eq`).
-/

namespace Lax461425Proofs

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.RigidConstruction Lax461425Proofs.PatternsSupportAction
open Lax461425Proofs.PatternsSupportBasic Lax461425Proofs.RigidRep

open scoped Classical

variable {n m : ℕ} {K : Type*} [Field K] [CharZero K] (D : Fin m → Circuit (Fin n × Fin n) K)
  (f : Fin m → K)

theorem blk_injective (i : Fin m) : Function.Injective (blk D i) := by
  intro x y hxy
  simpa using (Sum.inl_injective hxy : (⟨i, x⟩ : Σ j, (D j).Gate) = ⟨i, y⟩)

/-- `blk D i` embeds `D i` into `glueCircuit D f` as an isolated block (injective, label- and
wire-preserving, with no wire leaving the block). -/
theorem blk_ι_conf (i : Fin m) (y : (D i).Gate) (h' : GGate D)
    (hpos : 0 < (glueCircuit D f).wire (blk D i y) h') : ∃ h, h' = blk D i h := by
  rw [glueCircuit_wire] at hpos
  by_contra hc
  push Not at hc
  exact absurd (blk_wire_eq_zero_of_not_blk D hc) (Nat.pos_iff_ne_zero.mp hpos)

theorem blk_ι_wire (i : Fin m) (y h : (D i).Gate) :
    (glueCircuit D f).wire (blk D i y) (blk D i h) = (D i).wire y h := by
  rw [glueCircuit_wire, gwire_blk_blk_self]

/-- **Distinct gates of a block are never identified** by the glue circuit's equivalence
relation. -/
theorem blk_equiv_eq (hred : ∀ i, (D i).IsReduced) (i : Fin m) {y1 y2 : (D i).Gate}
    (h : RigidEquiv.Equiv (glueCircuit D f) (blk D i y1) (blk D i y2)) : y1 = y2 :=
  embed_equiv_eq (D := D i) (E := glueCircuit D f) (blk D i) (blk_injective D i) (fun y => rfl)
    (blk_ι_conf D f i) (blk_ι_wire D f i) (hred i) h

/-- **`IsSupport` transfers exactly between a block's own gates and the rigidified glue
circuit's.** -/
theorem isSupport_reduced_blk_iff (hred : ∀ i, (D i).IsReduced)
    (hsym : ∀ i, IsMatrixSymmetric (D i)) (i : Fin m)
    (hrigRed : IsRigid (reduced (glueCircuit D f))) (y : (D i).Gate)
    (S : Set (Fin n ⊕ Fin n)) :
    IsSupport (reduced (glueCircuit D f)) (toC' (glueCircuit D f) (blk D i y)) S ↔
      IsSupport (D i) y S := by
  rw [isSupport_iff_fixingSubgroup_le hrigRed,
    isSupport_iff_fixingSubgroup_le (hrigOf D hred hsym i)]
  constructor
  · intro hle γ hγ
    rw [mem_gateStabilizer_iff]
    have hstab := hle hγ
    rw [mem_gateStabilizer_iff, reduced_σOf_eq (τG D hred hsym) (τG_extends D f hred hsym) hrigRed,
      τG_blk] at hstab
    exact blk_equiv_eq D f hred i (equiv_of_rep_eq (glueCircuit D f) (congrArg Subtype.val hstab))
  · intro hle γ hγ
    rw [mem_gateStabilizer_iff, reduced_σOf_eq (τG D hred hsym) (τG_extends D f hred hsym) hrigRed,
      τG_blk]
    have hstab : σOf (hrigOf D hred hsym i) γ y = y := hle hγ
    rw [hstab]

/-- **`minSupport` of a block gate equals the block's own `minSupport`.** -/
theorem minSupport_reduced_blk_eq (hred : ∀ i, (D i).IsReduced)
    (hsym : ∀ i, IsMatrixSymmetric (D i)) (i : Fin m)
    (hrigRed : IsRigid (reduced (glueCircuit D f)))
    {k : ℕ} (hssE : supportSize (reduced (glueCircuit D f)) ≤ k) (hssD : supportSize (D i) ≤ k)
    (hn : 2 * k < n) (y : (D i).Gate) :
    minSupport (reduced (glueCircuit D f)) (toC' (glueCircuit D f) (blk D i y)) =
      minSupport (D i) y := by
  apply Set.Subset.antisymm
  · intro z hz
    intro S hS hSc
    have hS' : IsSupport (reduced (glueCircuit D f)) (toC' (glueCircuit D f) (blk D i y)) S :=
      (isSupport_reduced_blk_iff D f hred hsym i hrigRed y S).mpr hS
    exact minSupport_subset_of_isSupport_le hrigRed hS' (le_trans hSc hssD) hssE hn hz
  · intro z hz
    intro T hT hTc
    have hT' : IsSupport (D i) y T :=
      (isSupport_reduced_blk_iff D f hred hsym i hrigRed y T).mp hT
    exact minSupport_subset_of_isSupport_le (hrigOf D hred hsym i) hT' (le_trans hTc hssE) hssD hn
      hz

/-- Every glue gate (`scaledG`, `constG`, `outGG`) has empty minimal support in the rigidified
glue circuit. -/
theorem minSupport_reduced_glue_eq (hred : ∀ i, (D i).IsReduced)
    (hsym : ∀ i, IsMatrixSymmetric (D i)) (hrigRed : IsRigid (reduced (glueCircuit D f)))
    {x : GGate D} (hx : ∀ i y, x ≠ blk D i y) :
    minSupport (reduced (glueCircuit D f)) (toC' (glueCircuit D f) x) =
      (∅ : Set (Fin n ⊕ Fin n)) := by
  apply Set.subset_empty_iff.mp
  intro z hz
  refine hz ∅ ?_ (by simp)
  rw [isSupport_iff_fixingSubgroup_le hrigRed]
  intro γ _hγ
  rw [mem_gateStabilizer_iff, reduced_σOf_eq (τG D hred hsym) (τG_extends D f hred hsym) hrigRed]
  congr 1
  rcases x with ⟨i, y⟩ | i | i | ⟨⟩
  · exact absurd rfl (hx i y)
  · exact τG_scaled D hred hsym γ i
  · exact τG_const D hred hsym γ i
  · exact τG_out D hred hsym γ

end Lax461425Proofs
