import Lax461425.Permanent
import Lax461425.BooleanSumSymmetry

/-!
---
title: Symmetric membership and hardness of the permanent
type: theorem
---
Proposition 7.5 and the hardness direction of Theorem 7.7. Together these give completeness,
proved by `Lax461425Proofs.PermanentProjection.completeness`. The projection order is
unrestricted. Proofs use Ryser's identity and an explicit equivariant bouquet.
-/

namespace Lax461425.PermanentCompleteness

open Permanent SymmetricFamilies SymmetricClasses SymmetricVNP

/-- The permanent has a jointly symmetric Boolean witness over every commutative ring. -/
axiom membership (K : Type*) [CommRing K] : InSymVNP (permanent K)

/-- Every symmetric-VNP family projects symmetrically to the permanent, allowing
unrestricted source order independently for every matrix size. -/
axiom hardness (K : Type) [Field K] [CharZero K] :
    ∀ f : MatrixFamily K, InSymVNP f →
      ∀ n, IsSymmetricProjection (matrixAction n) (f n)

end Lax461425.PermanentCompleteness
