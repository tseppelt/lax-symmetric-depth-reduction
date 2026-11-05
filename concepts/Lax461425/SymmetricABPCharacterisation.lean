import Lax461425.SymmetricABPs
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
holds over every commutative semiring.
-/

namespace Lax461425.SymmetricABPCharacterisation

open SymmetricABPs SymmetricFamilies SymmetricClasses SymmetricVNP

/-- Families with symmetric polynomial-orbit ABPs have symmetric polynomial-orbit skew
circuits, over every commutative semiring. -/
axiom inSymVS_of_inSymVBP {K : Type*} [CommSemiring K] (f : MatrixFamily K)
    (hf : InSymVBP f) : InSymVS f

/-- Symmetric polynomial-orbit skew-circuit families have symmetric
polynomial-orbit ABPs. -/
axiom inSymVBP_of_inSymVS {K : Type*} [Field K] [CharZero K] (f : MatrixFamily K)
    (hf : InSymVS f) : InSymVBP f

/-- Symmetric polynomial-orbit ABPs and skew circuits define the same class. -/
axiom characterisation {K : Type*} [Field K] [CharZero K] (f : MatrixFamily K) :
    InSymVBP f ↔ InSymVS f

end Lax461425.SymmetricABPCharacterisation
