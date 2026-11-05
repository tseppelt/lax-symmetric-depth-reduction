import Lax461425.BooleanSumSymmetry
import Lax461425.SymmetricFormulaWitness

/-!
---
title: Formula-witness equivalence
type: theorem
---
Over a field of characteristic zero, symmetric VNP is unchanged when the witnessing
circuits are required to be formulas.
-/

namespace Lax461425.FormulaWitnessEquivalence

open SymmetricFamilies SymmetricClasses SymmetricVNP

/-- Formula witnesses and circuit witnesses define the same Boolean-sum class. -/
axiom formula_witnesses_iff {K : Type*} [Field K] [CharZero K] (f : MatrixFamily K) :
    InSymVNP f ↔ InSymVNPFormula f

end Lax461425.FormulaWitnessEquivalence
