import Lax461425.SymmetricABPs

/-!
---
title: Symmetric ABPs for bounded-pathwidth patterns
type: theorem
---
The path-decomposition construction used in the proof of Lemma 6.5. A pattern of
pathwidth at most `k` has a matrix-symmetric ABP computing its homomorphism polynomial
with vertex-orbit size at most `n^(k+1)`, for `n ≥ 1`.
-/

namespace Lax461425.ABPsForPatterns

open SymmetricABPs HomomorphismPolynomials

/-- The bounded-pathwidth ABP construction in the proof of Lemma 6.5. -/
axiom exists_abp {K : Type*} [CommSemiring K] {n k : ℕ} (hn : 1 ≤ n)
    (F : Pattern) (hF : PathwidthLE k F) :
    ∃ G : ABP (Fin n × Fin n) K,
      G.Computes (hom K F n) ∧ G.IsMatrixSymmetric ∧ G.orbitSize ≤ n ^ (k + 1)

end Lax461425.ABPsForPatterns
