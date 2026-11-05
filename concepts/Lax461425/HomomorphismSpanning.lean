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

This is the general homomorphism-spanning result cited from DPS, ITCS 2026, Lemma 4.
It imposes no bound on pathwidth or degree. The proof follows the paper's distinct
monomial orbits and embedding polynomials, then applies partition Möbius inversion
from the full version's Corollary A.3. Quotient patterns preserve the vertex bounds.
-/

namespace Lax461425.HomomorphismSpanning

open SymmetricFamilies HomomorphismPolynomials

/-- General homomorphism spanning, with the finite vertex bounds used in Sections 6–7. -/
axiom invariant_mem_span_hom {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (hn : 1 ≤ n) (p : MatrixPolynomial n K) (hp : MatrixInvariant p) :
    p ∈ Submodule.span K {q | ∃ F : Pattern,
      Fintype.card F.A ≤ n ∧ Fintype.card F.B ≤ n ∧ hom K F n = q}

end Lax461425.HomomorphismSpanning
