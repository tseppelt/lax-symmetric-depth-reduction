import Lax461425.SymmetricClasses
import Lax461425.PatternWidths
import Lax461425.BoundedDepthCharacterisation
import Lax461425.TreedepthForestwidth
import Lax461425.FormulaSupportDepth
import Lax461425.FormulasForPatterns
import Lax461425.HomomorphismSpanning
import Mathlib.LinearAlgebra.Span.Defs

/-!
---
title: Characterisation of symmetric VF
type: theorem
---
Over a field of characteristic zero, a family of polynomials $(p_n)$ is computed by
matrix-symmetric formulas of polynomial orbit size if, and only if, there is a constant $t$
such that every $p_n$ is a linear combination of homomorphism polynomials $\hom_{F,n}$ of
patterns $F$ of treedepth at most $t$. This is a result of Dwivedi, Pago, and Seppelt
(STOC 2026). Symmetric formulas have rigidifications of bounded support depth, so it follows
from the characterisation of bounded-depth matrix-symmetric circuits, since bounded
$\Delta$-forestwidth for bounded $\Delta$ amounts to bounded treedepth.
-/

namespace Lax461425.SymmetricVFCharacterisation

open SymmetricFamilies SymmetricClasses HomomorphismPolynomials PatternWidths

/-- `symVF` consists of the families spanned by homomorphism polynomials of patterns of
bounded treedepth. -/
axiom characterisation {K : Type*} [Field K] [CharZero K] (f : MatrixFamily K) :
    InSymVF f ↔ ∃ t : ℕ, ∀ n,
      f n ∈ Submodule.span K {q | ∃ F : Pattern, TreedepthLE t F ∧ hom K F n = q}

end Lax461425.SymmetricVFCharacterisation
