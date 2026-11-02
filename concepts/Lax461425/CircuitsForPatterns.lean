import Lax461425.Supports
import Lax461425.Forestwidth

/-!
---
title: Circuits for patterns of bounded forestwidth
type: theorem
---
Let $\Delta \geq 1$, $k \geq 2$, and $n \geq 2k + 1$. Let $F$ be a pattern with
$\mathrm{fw}_\Delta(F) \leq k - 1$. Then $\hom_{F,n}$ is computed by a reduced
matrix-symmetric circuit of support size $\leq k$, support depth $\leq \Delta$, orbit size
$\leq n^k$, depth $\leq 2\Delta + 1$, and size $\leq 5 n^k (|V(F)| + |E(F)|) + 1$, where
$|E(F)|$ counts edges with multiplicity.
-/

namespace Lax461425.CircuitsForPatterns

open Circuits MatrixSymmetry Supports HomomorphismPolynomials Forestwidth

/-- The homomorphism polynomial of a pattern of `Δ`-forestwidth at most `k - 1` is computed by a
reduced matrix-symmetric circuit of support size `≤ k`, support depth `≤ Δ`, orbit size
`≤ n ^ k`, depth `≤ 2Δ + 1`, and size `≤ 5 n ^ k (|V(F)| + |E(F)|) + 1`. -/
axiom exists_circuit {K : Type*} [Field K] [CharZero K] {Δ k n : ℕ} (hΔ : 1 ≤ Δ) (hk : 2 ≤ k)
    (hn : 2 * k + 1 ≤ n) (F : Pattern) (hF : ForestwidthLE Δ (k - 1) F) :
    ∃ C : Circuit (Fin n × Fin n) K,
      C.Computes (hom K F n) ∧ C.IsReduced ∧ IsMatrixSymmetric C ∧
        supportSize C ≤ k ∧
        supportDepth C ≤ Δ ∧
        orbitSize C ≤ n ^ k ∧
        C.depth ≤ 2 * Δ + 1 ∧
        C.size ≤ 5 * n ^ k * (Fintype.card F.A + Fintype.card F.B + ∑ a, ∑ b, F.mult a b) + 1

end Lax461425.CircuitsForPatterns
