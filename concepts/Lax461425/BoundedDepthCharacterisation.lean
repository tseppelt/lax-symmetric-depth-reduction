import Mathlib.LinearAlgebra.Span.Defs
import Lax461425.Supports
import Lax461425.Forestwidth

/-!
---
title: Characterisation of bounded-depth matrix-symmetric circuits
type: theorem
---
Let $\mathbb{K}$ be a field of characteristic zero. Let $\Delta \geq 1$, $k \geq 2$, and
$n \geq 2k + 1$. For a polynomial $p \in \mathbb{K}[\mathcal{X}_n]$, the following are
equivalent:

1. $p$ is computed by a reduced matrix-symmetric circuit of support size $\leq k$ and support
   depth $\leq \Delta$.
2. $p$ is a linear combination of homomorphism polynomials $\hom_{F,n}$ for patterns $F$ with
   $\mathrm{fw}_\Delta(F) \leq k - 1$.

The implication from 1 to 2 is the theorem on homomorphism polynomials from symmetric
circuits. For the implication from 2 to 1, one constructs a circuit for every pattern in the
linear combination as in the theorem on circuits for patterns of bounded forestwidth,
multiplies the output gates by the coefficients, adds an output sum gate, and rigidifies.
-/

namespace Lax461425.BoundedDepthCharacterisation

open Circuits MatrixSymmetry Supports HomomorphismPolynomials Forestwidth

/-- A polynomial is computed by a reduced matrix-symmetric circuit of support size `≤ k` and
support depth `≤ Δ` if, and only if, it is a linear combination of homomorphism polynomials of
patterns of `Δ`-forestwidth at most `k - 1`. -/
axiom characterisation {K : Type*} [Field K] [CharZero K] {Δ k n : ℕ} (hΔ : 1 ≤ Δ)
    (hk : 2 ≤ k) (hn : 2 * k + 1 ≤ n) (p : MvPolynomial (Fin n × Fin n) K) :
    (∃ C : Circuit (Fin n × Fin n) K,
        C.Computes p ∧ C.IsReduced ∧ IsMatrixSymmetric C ∧
          supportSize C ≤ k ∧ supportDepth C ≤ Δ) ↔
      p ∈ Submodule.span K {q | ∃ F : Pattern, ForestwidthLE Δ (k - 1) F ∧ hom K F n = q}

end Lax461425.BoundedDepthCharacterisation
