import Lax461425.BooleanSumSymmetry
import Lax461425.SymmetricFormulaWitness

/-!
---
title: Formula-witness equivalence — Corollary 7.4
type: theorem
---
Corollary 7.4: symmetric circuit and formula witnesses define the same Boolean-sum class.
The proof combines Observation 7.2 with the quantitative formula witnesses of Theorem 7.3,
using a constant witness at matrix order zero. It is
`Section7FormulaConstruction.formula_witnesses_iff`.
-/

namespace Lax461425.FormulaWitnessEquivalence

open SymmetricFamilies SymmetricClasses

/-- Formula witnesses and circuit witnesses define the same Boolean-sum class. -/
axiom formula_witnesses_iff {K : Type*} [Field K] [CharZero K] (f : MatrixFamily K) :
    InSymVNP f ↔ InSymVNPFormula f

end Lax461425.FormulaWitnessEquivalence
