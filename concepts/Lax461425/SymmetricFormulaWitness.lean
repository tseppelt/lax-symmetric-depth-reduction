import Lax461425.CircuitProperties
import Lax461425.SymmetricFamilies
import Lax461425.HomomorphismSpanning

open Lax461425.CircuitProperties

/-!
---
title: Symmetric formula witnesses — Theorem 7.3
type: theorem
---
The quantitative part of Theorem 7.3. Every matrix-invariant polynomial of positive
matrix order has a jointly symmetric formula witness with exactly `2n²` Boolean
variables and gate orbits at most `4n²`, with equal-labelled inputs identified.
The proof uses homomorphism spanning, isolated-vertex padding, and the paper's selectors
and fresh inverse tags. It is `Section7FormulaConstruction.formula_witness`.
-/

namespace Lax461425.SymmetricFormulaWitness

universe u

open Circuits MatrixSymmetry SymmetricFamilies

/-- The quantitative formula witness for each positive matrix order. -/
axiom formula_witness {K : Type u} [Field K] [CharZero K] {n : ℕ}
    (hn : 1 ≤ n) (p : MvPolynomial (Fin n × Fin n) K) (hp : MatrixInvariant p) :
    ∃ (ρ : Γ n →* Equiv.Perm (Fin (2 * n ^ 2)))
      (g : MvPolynomial ((Fin n × Fin n) ⊕ Fin (2 * n ^ 2)) K)
      (C : Circuit ((Fin n × Fin n) ⊕ Fin (2 * n ^ 2)) K),
      C.Computes g ∧ Symmetric (jointAction ρ) C ∧
      orbitSize (jointAction ρ) C ≤ 4 * n ^ 2 ∧ (IsFormula C) ∧ (InputsIdentified C) ∧ boolSum g = p

end Lax461425.SymmetricFormulaWitness
