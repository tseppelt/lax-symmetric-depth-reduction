import Lax461425Proofs.RigidSymmetric
import Lax461425Proofs.PatternsSupportBasic

/-!
A generic formula for `σOf` on a rigidified circuit: given *any* family `τ` witnessing that `C`
is matrix-symmetric, `σOf hrigRed γ` (the canonical automorphism of `reduced C`, which exists
since `reduced C` is always rigid, being reduced and matrix-symmetric) agrees, through the
quotient map `toC'`, with `τ γ` — regardless of whether `τ` itself is a canonical/rigid choice
for `C`. This holds because `reduced C` is rigid: *any* valid witness of `C`'s matrix-symmetry
induces the *same* unique automorphism of `reduced C`.
-/

namespace Lax461425Proofs

open Lax461425.Circuits Lax461425.MatrixSymmetry
open Lax461425Proofs.RigidConstruction Lax461425Proofs.RigidRep Lax461425Proofs.RigidSymmetric
open Lax461425Proofs.PatternsSupportAction

variable {n : ℕ} {K : Type*} [CommSemiring K] {C : Circuit (Fin n × Fin n) K}

/-- **The `σOf`-formula for the rigidification.** -/
theorem reduced_σOf_eq (τ : Γ n → C.Gate ≃ C.Gate) (hτ : ∀ γ, Extends C (τ γ) (actVar γ))
    (hrigRed : IsRigid (reduced C)) (γ : Γ n) (x : C.Gate) :
    σOf hrigRed γ (toC' C x) = toC' C (τ γ x) := by
  have hcast : Extends C (τ γ) (⇑(Equiv.prodCongr γ.1 γ.2)) := hτ γ
  have heq : toC'Equiv C hcast = σOf hrigRed γ := σOf_unique hrigRed (extends_toC'Equiv hcast)
  have hstep : toC'Equiv C hcast (toC' C x) = toC' C (τ γ (rep C x)) := rfl
  rw [← heq, hstep]
  exact toC'_eq_of_equiv C
    ((equiv_extends C hcast (rep C x) x).mpr (RigidEquiv.equiv_symm C (rep_equiv C x)))

end Lax461425Proofs
