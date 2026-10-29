import Mathlib.LinearAlgebra.Span.Defs
import Lax461425.Supports
import Lax461425.Forestwidth

/-!
---
title: Homomorphism polynomials from symmetric circuits
type: theorem
---
Let $\Delta \geq 1$, $k \geq 2$, and $n \geq 2k + 1$. If a polynomial
$p \in \mathbb{K}[\mathcal{X}_n]$ is computed by a reduced matrix-symmetric circuit of support
size $\leq k$ and support depth $\leq \Delta$, then $p$ is a linear combination of homomorphism
polynomials $\hom_{F,n}$ for patterns $F$ with $\mathrm{fw}_\Delta(F) \leq k - 1$.

The proof proceeds via homomorphism polynomials of labelled graphs. By induction on the
circuit, the polynomial computed at every gate $g$ is obtained by evaluating a linear
combination of labelled homomorphism polynomials at the minimal support of $g$, where the
labelled graphs admit tree decompositions of depth at most the number of support-changing
wires below $g$, with bags of size $\leq k$, whose root bag consists exactly of the labelled
non-isolated vertices. At a gate, all labels of an orbit of children are eliminated at once by
a restricted sum over injective assignments, and products over orbits are expressed via power
sums. The output gate has empty support, which yields unlabelled patterns of
$\Delta$-forestwidth at most $k - 1$.
-/

namespace Lax461425.PatternsFromCircuits

open Circuits MatrixSymmetry Supports HomomorphismPolynomials Forestwidth

/-- A polynomial computed by a reduced matrix-symmetric circuit of support size `≤ k` and
support depth `≤ Δ` is a linear combination of homomorphism polynomials of patterns of
`Δ`-forestwidth at most `k - 1`. -/
axiom mem_span_hom {K : Type*} [Field K] [CharZero K] {Δ k n : ℕ} (hΔ : 1 ≤ Δ) (hk : 2 ≤ k)
    (hn : 2 * k + 1 ≤ n) (C : Circuit (Fin n × Fin n) K)
    (hred : C.IsReduced) (hsym : IsMatrixSymmetric C) (hsize : supportSize C ≤ k)
    (hdepth : supportDepth C ≤ Δ) {p : MvPolynomial (Fin n × Fin n) K} (hp : C.Computes p) :
    p ∈ Submodule.span K {q | ∃ F : Pattern, ForestwidthLE Δ (k - 1) F ∧ hom K F n = q}

end Lax461425.PatternsFromCircuits
