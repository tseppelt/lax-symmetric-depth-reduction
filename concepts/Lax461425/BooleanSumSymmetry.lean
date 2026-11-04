import Lax461425.SymmetricFamilies

/-!
---
title: Boolean-sum symmetry — Observation 7.2
type: theorem
---
Joint symmetry of a Boolean witness implies matrix symmetry of its Boolean sum.
Observation 7.2 follows by circuit evaluation equivariance and reindexing Boolean assignments.
Its proof is `BooleanWitnesses.matrixInvariant_of_mem`.
-/

namespace Lax461425.BooleanSumSymmetry

universe u

open SymmetricFamilies

/-- Every member of a symmetric VNP family is matrix-invariant. -/
axiom matrixInvariant_of_mem {K : Type u} [CommSemiring K] (f : MatrixFamily K)
    (hf : InSymVNP f) (n : ℕ) : MatrixInvariant (f n)

end Lax461425.BooleanSumSymmetry
