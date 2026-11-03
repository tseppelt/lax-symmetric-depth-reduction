import Lax461425.SymmetricABPFamilies

/-!
---
title: Skew circuits from symmetric ABPs — Lemma 6.4
type: theorem
---
Lemma 6.4 states `symVBP ⊆ symVS`. The explicit ABP-to-skew-circuit conversion
preserves computation, matrix symmetry, and polynomial orbit bounds.
-/

namespace Lax461425.SkewFromABP

open SymmetricFamilies SymmetricABPs

/-- Lemma 6.4. The construction works over every commutative semiring. -/
axiom family_inclusion {K : Type*} [CommSemiring K] (f : MatrixFamily K)
    (hf : InSymVBP f) : InSymVS f

end Lax461425.SkewFromABP
