import Lax461425.SymmetricABPs
import Lax461425.SkewFromABP
import Lax461425.ABPsForPatterns
import Lax461425.SkewCircuitCharacterisation
import Lax461425.HomomorphismSpanning

/-!
---
title: Symmetric ABP characterisation
type: theorem
---
Families computed by matrix-symmetric ABPs with polynomial vertex orbits and families
computed by matrix-symmetric skew circuits with polynomial gate orbits coincide over a
field of characteristic zero, that is, `symVBP = symVS`. The inclusion `symVBP ⊆ symVS`
is the theorem on symmetric skew circuits from symmetric ABPs; the reverse inclusion follows
from the characterisation of matrix-symmetric skew circuits by bounded-pathwidth patterns.
-/

namespace Lax461425.SymmetricABPCharacterisation

open SymmetricABPs SymmetricFamilies SymmetricClasses SymmetricVNP

/-- Symmetric polynomial-orbit skew-circuit families have symmetric
polynomial-orbit ABPs. -/
axiom inSymVBP_of_inSymVS {K : Type*} [Field K] [CharZero K] (f : MatrixFamily K)
    (hf : InSymVS f) : InSymVBP f

/-- Symmetric polynomial-orbit ABPs and skew circuits define the same class. -/
axiom characterisation {K : Type*} [Field K] [CharZero K] (f : MatrixFamily K) :
    InSymVBP f ↔ InSymVS f

end Lax461425.SymmetricABPCharacterisation
