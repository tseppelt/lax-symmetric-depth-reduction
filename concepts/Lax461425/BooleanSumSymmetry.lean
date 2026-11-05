import Lax461425.SymmetricFamilies
import Lax461425.SymmetricClasses
import Lax461425.SymmetricVNP

/-!
---
title: Boolean-sum symmetry
type: theorem
---
Every polynomial of a family in symmetric VNP is invariant under independent row and
column permutations of the matrix variables.
-/

namespace Lax461425.BooleanSumSymmetry

open SymmetricFamilies SymmetricClasses SymmetricVNP

/-- Every member of a symmetric VNP family is matrix-invariant. -/
axiom matrixInvariant_of_mem {K : Type*} [CommSemiring K] (f : MatrixFamily K)
    (hf : InSymVNP f) (n : ℕ) : MatrixInvariant (f n)

end Lax461425.BooleanSumSymmetry
