import Lax461425.Permanent
import Lax461425.BooleanSumSymmetry

/-!
---
title: Symmetric membership and hardness of the permanent
type: theorem
---
The permanent family lies in symmetric VNP over every commutative ring. Over a field of
characteristic zero, every polynomial of a family in symmetric VNP is a symmetric affine
projection of a permanent of some order.
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
