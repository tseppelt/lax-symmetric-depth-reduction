import Lax461425.SymmetricABPs

/-!
---
title: Symmetric skew circuits from symmetric ABPs
type: theorem
---
Over every commutative semiring, a family of polynomials computed by matrix-symmetric ABPs
with polynomial vertex orbits is computed by matrix-symmetric skew circuits with polynomial
gate orbits, that is, `symVBP ⊆ symVS`.
-/

namespace Lax461425.SkewFromABP

open SymmetricABPs SymmetricFamilies SymmetricClasses

/-- Families with symmetric polynomial-orbit ABPs have symmetric polynomial-orbit skew
circuits, over every commutative semiring. -/
axiom inSymVS_of_inSymVBP {K : Type*} [CommSemiring K] (f : MatrixFamily K)
    (hf : InSymVBP f) : InSymVS f

end Lax461425.SkewFromABP
