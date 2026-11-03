import Lax461425.SymmetricABPFamilies
import Lax461425.ABPsForPatterns
import Lax461425.SkewCircuitCharacterisation
import Lax461425.HomomorphismSpanning

/-!
---
title: Symmetric ABPs from skew circuits — Lemma 6.5
type: theorem
---
Lemma 6.5 states `symVS ⊆ symVBP`. Its proof uses the bounded-pathwidth
homomorphism span, the ABP construction for patterns, and general homomorphism
spanning for the finitely many small positive indices.
-/

namespace Lax461425.ABPFromSkew

open SymmetricFamilies SymmetricABPs

/-- Lemma 6.5: symmetric polynomial-orbit skew-circuit families have symmetric
polynomial-orbit ABPs. -/
axiom family_inclusion {K : Type*} [Field K] [CharZero K] (f : MatrixFamily K)
    (hf : InSymVS f) : InSymVBP f

end Lax461425.ABPFromSkew
