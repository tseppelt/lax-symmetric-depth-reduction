import Lax461425.SkewFromABP
import Lax461425.ABPFromSkew

/-!
---
title: Symmetric ABP characterisation — Theorem 6.3
type: theorem
---
Theorem 6.3 of the paper states `symVBP = symVS`. Its two directions are proved
separately in `SkewFromABP` (Lemma 6.4) and `ABPFromSkew` (Lemma 6.5).
The equality uses their checked interfaces, so both nodes feed the main theorem
in the statement/proof graph.
-/

namespace Lax461425.SymmetricABPCharacterisation

open SymmetricABPs SymmetricFamilies

/-- Theorem 6.3: symmetric polynomial-orbit ABPs and skew circuits define the same class. -/
axiom characterisation {K : Type*} [Field K] [CharZero K] (f : MatrixFamily K) :
    InSymVBP f ↔ InSymVS f

end Lax461425.SymmetricABPCharacterisation
