import Lax461425.SymmetricABPFamilies

/-!
---
title: Symmetric ABPs for bounded-pathwidth patterns
type: theorem
---
The path-decomposition construction used in the proof of Lemma 6.5. A pattern of
pathwidth at most `k` has a matrix-symmetric ABP computing its homomorphism polynomial
with vertex-orbit size at most `n^(k+1)`, for `n ≥ 1`. Appending `r` empty bags
gives a layered witness of exact length `ℓ + r`, for a fixed base length `ℓ`.
-/

namespace Lax461425.ABPsForPatterns

open SymmetricABPs HomomorphismPolynomials

/-- The bounded-pathwidth ABP construction in the proof of Lemma 6.5. -/
axiom exists_abp {K : Type*} [CommSemiring K] {n k : ℕ} (hn : 1 ≤ n)
    (F : Pattern) (hF : PathwidthLE k F) :
    ∃ ℓ : ℕ, ∀ r : ℕ, ∃ G : ABP (Fin n × Fin n) K,
      G.Computes (hom K F n) ∧ G.IsMatrixSymmetric ∧ G.orbitSize ≤ n ^ (k + 1) ∧
        ∃ L : G.Layering, L.layer G.sink = ℓ + r

end Lax461425.ABPsForPatterns
