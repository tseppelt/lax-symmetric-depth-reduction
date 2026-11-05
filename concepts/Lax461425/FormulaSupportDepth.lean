import Lax461425.Supports
import Lax461425.CircuitProperties
import Lax461425.SymmetricFamilies
import Mathlib.Data.Nat.Choose.Basic

/-!
---
title: Support depth of symmetric formulas
type: theorem
---
Let $n \geq 20$ and $\kappa \in \mathbb{N}$ with $3\kappa \leq n + 2$. Every polynomial
computed by a matrix-symmetric formula of orbit size $< \binom{n}{\kappa}$ is computed by a
reduced matrix-symmetric circuit of support size $\leq \kappa - 1$ and support depth
$\leq 2\kappa$.

The circuit is the rigidification of the formula, whose support size is bounded by the support
theorem. In a formula, every internal gate has a unique chain of ancestors. A path in the
rigidification with many support-changing wires can be moved by stabilisers so that each such
wire adds a new point to the union of the supports along the path. Lifting the path to the
formula, the gates at its end lie in a gate orbit at least as large as the orbit of this union,
which bounds the number of support-changing wires.
-/

namespace Lax461425.FormulaSupportDepth

open Circuits CircuitProperties MatrixSymmetry SymmetricFamilies Supports

/-- The rigidification of a symmetric formula of small orbit size has bounded support
depth. -/
axiom exists_reduced {K : Type*} [CommSemiring K] {n κ : ℕ} (hn : 20 ≤ n)
    (hκ : 3 * κ ≤ n + 2) (C : Circuit (Fin n × Fin n) K) (hformula : IsFormula C)
    (hsym : IsMatrixSymmetric C) (horb : orbitSize C < n.choose κ)
    {p : MatrixPolynomial n K} (hp : C.Computes p) :
    ∃ C' : Circuit (Fin n × Fin n) K,
      C'.Computes p ∧ C'.IsReduced ∧ IsMatrixSymmetric C' ∧
        supportSize C' ≤ κ - 1 ∧ supportDepth C' ≤ 2 * κ

end Lax461425.FormulaSupportDepth
