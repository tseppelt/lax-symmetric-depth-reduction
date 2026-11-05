import Lax461425.Permanent
import Lax461425.SymmetricFamilies

/-! Affine-entry facts and constant permanent projections for Section 7.3. -/

namespace Lax461425Proofs.Permanent

open Lax461425.Permanent Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies
open scoped BigOperators

variable {V G K : Type*} [CommSemiring K]

lemma isAffine_C (c : K) : IsAffine (MvPolynomial.C c : MvPolynomial V K) := by
  exact ⟨c, ∅, fun _ => 0, by simp⟩

lemma isAffine_X (v : V) : IsAffine (MvPolynomial.X v : MvPolynomial V K) := by
  classical
  exact ⟨0, {v}, fun _ => 1, by simp⟩

end Lax461425Proofs.Permanent
