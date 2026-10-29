import Lax461425Proofs.BoundedDepthGlueComputes
import Lax461425Proofs.PatternsSupportBasic
import Lax461425.ReducedRigid

/-!
**The glue circuit is matrix-symmetric**, given that every block `D i` is reduced and
matrix-symmetric (hence rigid). The automorphism extending `γ` acts as the canonical extension
`σOf (hrig i) γ` within each block, and fixes every glue gate (`scaledG`, `constG`, `outGG`)
pointwise.
-/

namespace Lax461425Proofs

open Lax461425.Circuits Lax461425.MatrixSymmetry
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic

open scoped Classical

variable {n m : ℕ} {K : Type*} [Field K] [CharZero K] (D : Fin m → Circuit (Fin n × Fin n) K)
  (f : Fin m → K)

/-- `D i` is rigid, given reducedness and matrix-symmetry. -/
theorem hrigOf (hred : ∀ i, (D i).IsReduced) (hsym : ∀ i, IsMatrixSymmetric (D i)) (i : Fin m) :
    IsRigid (D i) :=
  Lax461425.ReducedRigid.isRigid (D i) (hsym i) (hred i)

/-- The automorphism of the glue circuit extending `γ`: the canonical extension within each
block, fixing every glue gate. -/
noncomputable def τG (hred : ∀ i, (D i).IsReduced) (hsym : ∀ i, IsMatrixSymmetric (D i))
    (γ : Γ n) : GGate D ≃ GGate D :=
  Equiv.sumCongr (Equiv.sigmaCongrRight (fun i => σOf (hrigOf D hred hsym i) γ))
    (Equiv.refl (Fin m ⊕ Fin m ⊕ Unit))

variable (hred : ∀ i, (D i).IsReduced) (hsym : ∀ i, IsMatrixSymmetric (D i))

theorem τG_blk (γ : Γ n) (i : Fin m) (y : (D i).Gate) :
    τG D hred hsym γ (blk D i y) = blk D i (σOf (hrigOf D hred hsym i) γ y) := rfl

theorem τG_scaled (γ : Γ n) (i : Fin m) : τG D hred hsym γ (scaledG D i) = scaledG D i := rfl

theorem τG_const (γ : Γ n) (i : Fin m) : τG D hred hsym γ (constG D i) = constG D i := rfl

theorem τG_out (γ : Γ n) : τG D hred hsym γ (outGG D) = outGG D := rfl

theorem τG_extends (γ : Γ n) : Extends (glueCircuit D f) (τG D hred hsym γ) (actVar γ) := by
  constructor
  · rintro (⟨i, y⟩ | i | i | ⟨⟩)
    · show (glueCircuit D f).label (blk D i (σOf (hrigOf D hred hsym i) γ y)) =
        ((glueCircuit D f).label (blk D i y)).map (actVar γ)
      show (D i).label (σOf (hrigOf D hred hsym i) γ y) = ((D i).label y).map (actVar γ)
      exact (σOf_extends (hrigOf D hred hsym i) γ).1 y
    · rfl
    · rfl
    · rfl
  · rintro (⟨i, y⟩ | i | i | ⟨⟩) <;> rintro (⟨i', y'⟩ | i' | i' | ⟨⟩)
    · show gwire D (blk D i (σOf (hrigOf D hred hsym i) γ y))
          (blk D i' (σOf (hrigOf D hred hsym i') γ y')) = gwire D (blk D i y) (blk D i' y')
      rw [gwire_blk_blk, gwire_blk_blk]
      by_cases heq : i = i'
      · subst heq
        simp only [dif_pos rfl]
        exact (σOf_extends (hrigOf D hred hsym i) γ).2 y y'
      · simp [dif_neg heq]
    · show gwire D (blk D i (σOf (hrigOf D hred hsym i) γ y)) (scaledG D i') =
        gwire D (blk D i y) (scaledG D i')
      rw [gwire_blk_scaled, gwire_blk_scaled]
    · show gwire D (blk D i (σOf (hrigOf D hred hsym i) γ y)) (constG D i') =
        gwire D (blk D i y) (constG D i')
      rw [gwire_blk_const, gwire_blk_const]
    · show gwire D (blk D i (σOf (hrigOf D hred hsym i) γ y)) (outGG D) =
        gwire D (blk D i y) (outGG D)
      rw [gwire_blk_out, gwire_blk_out]
    · show gwire D (scaledG D i) (blk D i' (σOf (hrigOf D hred hsym i') γ y')) =
        gwire D (scaledG D i) (blk D i' y')
      rw [gwire_scaled_blk, gwire_scaled_blk]
      by_cases heq : i = i'
      · subst heq
        simp only [dif_pos rfl]
        have hfix : σOf (hrigOf D hred hsym i) γ (D i).out = (D i).out :=
          extends_fixes_out (σOf_extends (hrigOf D hred hsym i) γ)
        by_cases hy : y' = (D i).out
        · subst hy; rw [hfix]
        · have hy' : σOf (hrigOf D hred hsym i) γ y' ≠ (D i).out := by
            intro hc
            exact hy ((σOf (hrigOf D hred hsym i) γ).injective (hc.trans hfix.symm))
          simp [hy, hy']
      · simp [dif_neg heq]
    · rfl
    · show gwire D (scaledG D i) (constG D i') = gwire D (scaledG D i) (constG D i')
      rfl
    · show gwire D (scaledG D i) (outGG D) = gwire D (scaledG D i) (outGG D)
      rfl
    · show gwire D (constG D i) (blk D i' (σOf (hrigOf D hred hsym i') γ y')) =
        gwire D (constG D i) (blk D i' y')
      rw [gwire_const_any, gwire_const_any]
    · rfl
    · rfl
    · rfl
    · show gwire D (outGG D) (blk D i' (σOf (hrigOf D hred hsym i') γ y')) =
        gwire D (outGG D) (blk D i' y')
      rw [gwire_out_blk, gwire_out_blk]
    · rfl
    · rfl
    · rfl

/-- **The glue circuit is matrix-symmetric.** -/
theorem glueCircuit_isMatrixSymmetric (hred : ∀ i, (D i).IsReduced)
    (hsym : ∀ i, IsMatrixSymmetric (D i)) : IsMatrixSymmetric (glueCircuit D f) :=
  fun γ => ⟨τG D hred hsym γ, τG_extends D f hred hsym γ⟩

end Lax461425Proofs
