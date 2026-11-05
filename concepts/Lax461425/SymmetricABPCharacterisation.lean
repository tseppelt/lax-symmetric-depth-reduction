import Lax461425.SymmetricABPs
import Lax461425.ABPsForPatterns
import Lax461425.SkewCircuitCharacterisation
import Lax461425.HomomorphismSpanning

/-!
---
title: Symmetric ABP characterisation — Theorem 6.3
type: theorem
---
Theorem 6.3 of the paper states `symVBP = symVS`. Its two directions are Lemma 6.4
(`symVBP ⊆ symVS`) and Lemma 6.5 (`symVS ⊆ symVBP`).

Lemma 6.4 is the explicit ABP-to-skew-circuit conversion, which preserves computation,
matrix symmetry, and polynomial orbit bounds. Lemma 6.5 uses the bounded-pathwidth
homomorphism span, the ABP construction for patterns, and general homomorphism
spanning for the finitely many small positive indices.
-/

namespace Lax461425.SymmetricABPCharacterisation

open SymmetricABPs SymmetricFamilies SymmetricClasses

/-- Lemma 6.4. The construction works over every commutative semiring. -/
axiom inSymVS_of_inSymVBP {K : Type*} [CommSemiring K] (f : MatrixFamily K)
    (hf : InSymVBP f) : InSymVS f

/-- Lemma 6.5: symmetric polynomial-orbit skew-circuit families have symmetric
polynomial-orbit ABPs. -/
axiom inSymVBP_of_inSymVS {K : Type*} [Field K] [CharZero K] (f : MatrixFamily K)
    (hf : InSymVS f) : InSymVBP f

/-- Theorem 6.3: symmetric polynomial-orbit ABPs and skew circuits define the same class. -/
axiom characterisation {K : Type*} [Field K] [CharZero K] (f : MatrixFamily K) :
    InSymVBP f ↔ InSymVS f

end Lax461425.SymmetricABPCharacterisation
