import Lax461425.PatternWidths
import Lax461425.CircuitProperties
import Lax461425.MatrixSymmetry

/-!
---
title: Symmetric formulas for patterns of bounded treedepth
type: theorem
---
Over a field of characteristic zero, for $n \geq 1$ and every pattern $F$ of treedepth at most
$t$, the homomorphism polynomial $\hom_{F,n}$ is computed by a matrix-symmetric formula of
orbit size at most $n^{t+2}$.

For an elimination forest of height at most $t$, the formula has a sum gate for every vertex
$v$ and every assignment of values in $[n]$ to the proper ancestors of $v$. It sums over the
values of $v$ the product of the edge variables from $v$ to its ancestors and of the sum gates
of the children of $v$. Parallel edges are multiplied out one at a time. Each copy of a
subformula is multiplied by its own pair of mutually inverse constants, which are chosen
distinct and different from all other constants, so that automorphisms cannot exchange copies.
Hence every internal gate lies in an orbit of size at most $n^t$, and input gates lie in orbits
of size at most $n^2$.
-/

namespace Lax461425.FormulasForPatterns

open Circuits CircuitProperties MatrixSymmetry HomomorphismPolynomials PatternWidths

/-- The homomorphism polynomial of a pattern of treedepth at most `t` has a matrix-symmetric
formula of orbit size at most `n ^ (t + 2)`. -/
axiom exists_formula {K : Type*} [Field K] [CharZero K] {n t : ℕ} (hn : 1 ≤ n)
    (F : Pattern) (hF : TreedepthLE t F) :
    ∃ C : Circuit (Fin n × Fin n) K,
      C.Computes (hom K F n) ∧ IsFormula C ∧ IsMatrixSymmetric C ∧ orbitSize C ≤ n ^ (t + 2)

end Lax461425.FormulasForPatterns
