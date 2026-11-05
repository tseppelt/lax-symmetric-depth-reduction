import Lax461425.CircuitProperties
import Lax461425.SymmetricFamilies
import Lax461425.SymmetricClasses
import Lax461425.SymmetricVNP
import Lax461425.HomomorphismSpanning

open Lax461425.CircuitProperties

/-!
---
title: Symmetric formula witnesses
type: theorem
---
Over a field of characteristic zero, every matrix-invariant polynomial on an `n × n`
matrix, for `n ≥ 1`, is the hypercube sum of a polynomial with `2n²` auxiliary variables
that is computed by a jointly symmetric formula with gate orbits of size at most `4n²`.
-/

namespace Lax461425.SymmetricFormulaWitness

open Circuits MatrixSymmetry SymmetricFamilies SymmetricClasses SymmetricVNP

/-- Matrix-invariant polynomials have jointly symmetric formula witnesses with `2n²`
auxiliary variables and gate orbits of size at most `4n²`. -/
axiom formula_witness {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (hn : 1 ≤ n) (p : MatrixPolynomial n K) (hp : MatrixInvariant p) :
    ∃ (ρ : Γ n →* Equiv.Perm (Fin (2 * n ^ 2)))
      (g : MvPolynomial ((Fin n × Fin n) ⊕ Fin (2 * n ^ 2)) K)
      (C : Circuit ((Fin n × Fin n) ⊕ Fin (2 * n ^ 2)) K),
      C.Computes g ∧ Symmetric (jointAction ρ) C ∧
      orbitSize (jointAction ρ) C ≤ 4 * n ^ 2 ∧ IsFormula C ∧ boolSum g = p

end Lax461425.SymmetricFormulaWitness
