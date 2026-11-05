import Lax461425Proofs.Section6Schedule
import Lax461425Proofs.Section6BagComputes
import Lax461425.ABPsForPatterns

/-!
The path-decomposition construction of Section 6. This theorem includes the exact orbit
bound, evaluated over all extending automorphisms, and literal homomorphism computation.
-/

namespace Lax461425Proofs.Section6ABPForPatterns

open Lax461425.SymmetricABPs Lax461425.HomomorphismPolynomials
open Lax461425.PatternWidths

/--
---
conclusion: Lax461425.ABPsForPatterns.exists_abp
---
Every pattern of pathwidth at most `k` has a symmetric affine ABP with vertex-orbit
size at most `n^(k+1)`. -/
theorem exists_abp {K : Type*} [CommSemiring K] {n k : ℕ} (hn : 1 ≤ n)
    (F : Pattern) (hF : PathwidthLE k F) :
    ∃ G : ABP (Fin n × Fin n) K,
      G.Computes (hom K F n) ∧ G.IsMatrixSymmetric ∧ G.orbitSize ≤ n ^ (k + 1) := by
  obtain ⟨D⟩ := SymmetricPathDecomposition.pathwidthLE_iff.1 hF
  let S := Section6Schedule.schedule D
  exact ⟨Section6BagProgram.abp S n hn K,
    Section6BagComputes.computes_hom S n hn K,
    Section6BagSymmetry.isMatrixSymmetric S n hn K,
    Section6BagProgram.orbitSize_le S n hn K⟩

end Lax461425Proofs.Section6ABPForPatterns
