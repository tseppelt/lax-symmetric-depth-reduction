import Lax461425.BooleanSumSymmetry
import Lax461425.SymmetricFormulaWitness

/-!
---
title: Symmetric VNP
type: theorem
---
Over a field of characteristic zero, symmetric VNP consists precisely of the families
of matrix-invariant polynomials.
-/

namespace Lax461425.SymmetricVNPCharacterisation

open SymmetricFamilies SymmetricClasses SymmetricVNP

/-- Symmetric VNP consists precisely of all matrix-invariant polynomial families. -/
axiom all_matrix_symmetric_iff {K : Type*} [Field K] [CharZero K] (f : MatrixFamily K) :
    InSymVNP f ↔ ∀ n, MatrixInvariant (f n)

end Lax461425.SymmetricVNPCharacterisation
