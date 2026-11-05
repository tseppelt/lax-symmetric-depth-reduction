import Lax461425.SymmetricFamilies
import Lax461425.HomomorphismPolynomials
import Mathlib.LinearAlgebra.Span.Defs

/-!
---
title: Homomorphism polynomials span matrix-symmetric polynomials
type: theorem
---
Over a field of characteristic zero, every matrix-symmetric polynomial in an `n × n`
matrix, for `n ≥ 1`, is a finite linear combination of homomorphism polynomials of
bipartite multigraph patterns having at most `n` vertices on each side.
-/

namespace Lax461425.HomomorphismSpanning

open SymmetricFamilies HomomorphismPolynomials

/-- Matrix-invariant polynomials are linear combinations of homomorphism polynomials of
patterns with at most `n` vertices on each side. -/
axiom invariant_mem_span_hom {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (hn : 1 ≤ n) (p : MatrixPolynomial n K) (hp : MatrixInvariant p) :
    p ∈ Submodule.span K {q | ∃ F : Pattern,
      Fintype.card F.A ≤ n ∧ Fintype.card F.B ≤ n ∧ hom K F n = q}

end Lax461425.HomomorphismSpanning
