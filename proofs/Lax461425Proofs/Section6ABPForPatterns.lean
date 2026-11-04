import Lax461425Proofs.Section6Schedule
import Lax461425Proofs.Section6BagComputes
import Lax461425.ABPsForPatterns

/-!
The path-decomposition construction of Section 6. This theorem includes the exact orbit
bound, evaluated over all extending automorphisms, and literal homomorphism computation.
-/

namespace Lax461425Proofs.Section6ABPForPatterns

open Lax461425.SymmetricABPs Lax461425.HomomorphismPolynomials

/--
---
conclusion: Lax461425.ABPsForPatterns.exists_abp
---
Every pattern of pathwidth at most `k` has a symmetric affine ABP with vertex-orbit
size at most `n^(k+1)`. Empty endpoint bags supply arbitrary unit-labelled padding
without changing the computation or orbit bound. -/
theorem exists_abp {K : Type*} [CommSemiring K] {n k : ℕ} (hn : 1 ≤ n)
    (F : Pattern) (hF : PathwidthLE k F) :
    ∃ ℓ : ℕ, ∀ r : ℕ, ∃ G : ABP (Fin n × Fin n) K,
      G.Computes (hom K F n) ∧ G.IsMatrixSymmetric ∧ G.orbitSize ≤ n ^ (k + 1) ∧
        ∃ L : G.Layering, L.layer G.sink = ℓ + r := by
  obtain ⟨D⟩ := SymmetricPathDecomposition.pathwidthLE_iff.1 hF
  let S := Section6Schedule.schedule D
  refine ⟨S.length, fun r => ?_⟩
  let T := Section6Schedule.padSchedule S r
  exact ⟨Section6BagProgram.abp T n hn K,
    Section6BagComputes.computes_hom T n hn K,
    Section6BagSymmetry.isMatrixSymmetric T n hn K,
    Section6BagProgram.orbitSize_le T n hn K,
    ⟨{
      layer := fun v => v.1.1.val
      source_layer := rfl
      edge_layer := fun _ _ h => h.1.symm
    }, rfl⟩⟩

end Lax461425Proofs.Section6ABPForPatterns
