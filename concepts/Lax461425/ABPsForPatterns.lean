import Lax461425.SymmetricABPs
import Lax461425.PatternWidths

/-!
---
title: Symmetric ABPs for bounded-pathwidth patterns
type: theorem
---
For `n ≥ 1`, the homomorphism polynomial of a pattern of pathwidth at most `k` on `n × n`
matrices is computed by a matrix-symmetric ABP whose vertex orbits have size at most
`n^(k+1)`.
-/

namespace Lax461425.ABPsForPatterns

open SymmetricABPs HomomorphismPolynomials PatternWidths

/-- Homomorphism polynomials of patterns of pathwidth at most `k` have matrix-symmetric ABPs
with vertex orbits of size at most `n^(k+1)`. -/
axiom exists_abp {K : Type*} [CommSemiring K] {n k : ℕ} (hn : 1 ≤ n)
    (F : Pattern) (hF : PathwidthLE k F) :
    ∃ G : ABP (Fin n × Fin n) K,
      G.Computes (hom K F n) ∧ G.IsMatrixSymmetric ∧ G.orbitSize ≤ n ^ (k + 1)

end Lax461425.ABPsForPatterns
