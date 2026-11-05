import Lax461425.BooleanSumSymmetry
import Lax461425.SymmetricFormulaWitness

/-!
---
title: Symmetric VNP
type: theorem
---
The family characterisation of Theorem 7.3: symmetric VNP consists precisely of all
matrix-invariant polynomial families. Boolean-sum symmetry (Observation 7.2) gives
one implication, and the quantitative symmetric formula witness gives the other.
Matrix order zero has a separate constant witness. The proof is
`Section7FormulaConstruction.all_matrix_symmetric_iff`.
-/

namespace Lax461425.SymmetricVNPCharacterisation

open SymmetricFamilies SymmetricClasses SymmetricVNP

/-- Symmetric VNP consists precisely of all matrix-invariant polynomial families. -/
axiom all_matrix_symmetric_iff {K : Type*} [Field K] [CharZero K] (f : MatrixFamily K) :
    InSymVNP f ↔ ∀ n, MatrixInvariant (f n)

end Lax461425.SymmetricVNPCharacterisation
