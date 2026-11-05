import Lax461425.SymmetricClasses
import Lax461425.PatternWidths
import Lax461425.BoundedDepthCharacterisation
import Lax461425.TreewidthForestwidth
import Lax461425.SupportTheorem
import Lax461425.Rigidification
import Lax461425.HomomorphismSpanning
import Mathlib.LinearAlgebra.Span.Defs

/-!
---
title: Characterisation of symmetric VP
type: theorem
---
Over a field of characteristic zero, a family of polynomials $(p_n)$ is computed by
matrix-symmetric circuits of polynomial orbit size if, and only if, there is a constant $k$
such that every $p_n$ is a linear combination of homomorphism polynomials $\hom_{F,n}$ of
patterns $F$ of treewidth at most $k$. This is the main result of Dawar, Pago, and Seppelt
(ITCS 2026). It follows from the characterisation of bounded-depth matrix-symmetric circuits,
as every circuit has finite support depth and every tree decomposition has finite depth.
-/

namespace Lax461425.SymmetricVPCharacterisation

open SymmetricFamilies SymmetricClasses HomomorphismPolynomials PatternWidths

/-- `symVP` consists of the families spanned by homomorphism polynomials of patterns of
bounded treewidth. -/
axiom characterisation {K : Type*} [Field K] [CharZero K] (f : MatrixFamily K) :
    InSymVP f ↔ ∃ k : ℕ, ∀ n,
      f n ∈ Submodule.span K {q | ∃ F : Pattern, TreewidthLE k F ∧ hom K F n = q}

end Lax461425.SymmetricVPCharacterisation
