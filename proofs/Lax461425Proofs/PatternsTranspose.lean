import Lax461425Proofs.PatternsLabelledOps
import Mathlib.Algebra.MvPolynomial.Rename

/-!
---
title: Transposing patterns (A/B symmetry)
type: definition
---
Swapping the two sides of a bipartite pattern: `Pattern.transpose`, `LabelledPattern.transpose`,
and the effect on homomorphism polynomials, which are mapped by the coordinate swap
`Prod.swap` on `MvPolynomial (Fin n × Fin n) K`. This lets `B`-side statements be derived from
their `A`-side twins.
-/

namespace Lax461425Proofs.PatternsTranspose

open Lax461425.HomomorphismPolynomials Lax461425Proofs.PatternsLabelledBasic
open Lax461425Proofs.PatternsLabelledOps

/-- Swap the two sides of a pattern. -/
def _root_.Lax461425.HomomorphismPolynomials.Pattern.transpose (F : Pattern) : Pattern where
  A := F.B
  B := F.A
  mult := fun b a => F.mult a b

/-- Swap the two sides (and label tuples) of a labelled pattern. -/
def _root_.Lax461425Proofs.PatternsLabelledBasic.LabelledPattern.transpose {ℓ r : ℕ} (G : LabelledPattern ℓ r) : LabelledPattern r ℓ where
  F := G.F.transpose
  a := G.b
  b := G.a

/-- The coordinate swap on `MvPolynomial (Fin n × Fin n) K`. -/
noncomputable def swapPoly (K : Type*) [CommSemiring K] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) K →ₐ[K] MvPolynomial (Fin n × Fin n) K :=
  MvPolynomial.rename Prod.swap

theorem labelledHom_transpose (K : Type*) [CommSemiring K] {ℓ r : ℕ} (G : LabelledPattern ℓ r)
    (n : ℕ) (v : Fin ℓ → Fin n) (w : Fin r → Fin n) :
    labelledHom K G.transpose n w v = swapPoly K n (labelledHom K G n v w) := by
  unfold labelledHom swapPoly
  simp only [map_sum, apply_ite (MvPolynomial.rename Prod.swap), map_prod, map_pow,
    MvPolynomial.rename_X, map_zero, Prod.swap_prod_mk]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun hB _ => Finset.sum_congr rfl fun hA _ => by
    simp only [LabelledPattern.transpose, Pattern.transpose, and_comm]
    split_ifs
    · exact Finset.prod_comm
    · rfl)

theorem hom_transpose (K : Type*) [CommSemiring K] (F : Pattern) (n : ℕ) :
    hom K F.transpose n = swapPoly K n (hom K F n) := by
  unfold hom swapPoly
  simp only [map_sum, map_prod, map_pow, MvPolynomial.rename_X, Prod.swap_prod_mk]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun hB _ => Finset.sum_congr rfl fun hA _ =>
    Finset.prod_comm)

theorem isEdgeless_transpose {F : Pattern} (h : isEdgeless F) : isEdgeless F.transpose :=
  fun b a => h a b

end Lax461425Proofs.PatternsTranspose
