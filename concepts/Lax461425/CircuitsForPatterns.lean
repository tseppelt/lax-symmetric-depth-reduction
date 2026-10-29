import Lax461425.Supports
import Lax461425.Forestwidth

/-!
---
title: Circuits for patterns of bounded forestwidth
type: theorem
---
Let $\Delta \geq 1$, $k \geq 2$, and $n \geq 2k + 1$. Let $F$ be a pattern with at least one
edge and $\mathrm{fw}_\Delta(F) \leq k - 1$. Then $\hom_{F,n}$ is computed by a reduced
matrix-symmetric circuit of support size $\leq k$, support depth $\leq \Delta$, orbit size
$\leq n^k$, depth $\leq 2\Delta + 1$, and size $\leq 5 n^k (|V(F)| + |E(F)|)$, where $|E(F)|$
counts edges with multiplicity.

After deleting isolated vertices, which contributes a constant factor, take a decomposition
$(T, \beta)$ of $F$ with root $r_0$ witnessing $\mathrm{fw}_\Delta(F) \leq k - 1$, and represent
every edge at a node whose bag contains it. The decomposition is normalised such that every
vertex in a bag is incident with an edge represented at this node or below it, no bag is
contained in its parent's bag, and $|V(T)| \leq |V(F)| + 1$. For every node $t$ and every
admissible map
$\gamma \colon \beta(t) \to [n] \uplus [n]$, i.e. one mapping left vertices to the left and
right vertices to the right copy of $[n]$, and for every node $c \neq r_0$ with parent $t$ and
admissible $\delta$ on $\beta(t) \cap \beta(c)$, the circuit has gates
$$
  R_{t,\gamma} = \prod_{ab \text{ represented at } t} x_{\gamma(a), \gamma(b)}
    \cdot \prod_{c \text{ child of } t} S_{c,\, \gamma|_{\beta(t)\cap\beta(c)}},
  \qquad
  S_{c,\delta} = \sum_{\gamma' \supseteq \delta \text{ admissible on } \beta(c)} R_{c,\gamma'},
$$
with output gate $R_{r_0, \emptyset}$. The group $\Gamma_n$ acts by
$R_{t,\gamma} \mapsto R_{t, \pi \circ \gamma}$ and $S_{c,\delta} \mapsto S_{c, \pi \circ \delta}$.
After rigidification, $\gamma(\beta(t))$ is the minimal support of $R_{t,\gamma}$, so only the
wires into sum gates are support-changing.
-/

namespace Lax461425.CircuitsForPatterns

open Circuits MatrixSymmetry Supports HomomorphismPolynomials Forestwidth

/-- The homomorphism polynomial of a pattern of `Δ`-forestwidth at most `k - 1` with at least
one edge is computed by a reduced matrix-symmetric circuit of support size `≤ k`, support
depth `≤ Δ`, orbit size `≤ n ^ k`, depth `≤ 2Δ + 1`, and size `≤ 5 n ^ k (|V(F)| + |E(F)|)`. -/
axiom exists_circuit {K : Type*} [Field K] [CharZero K] {Δ k n : ℕ} (hΔ : 1 ≤ Δ) (hk : 2 ≤ k)
    (hn : 2 * k + 1 ≤ n) (F : Pattern) (hE : ∃ a b, F.mult a b ≠ 0)
    (hF : ForestwidthLE Δ (k - 1) F) :
    ∃ C : Circuit (Fin n × Fin n) K,
      C.Computes (hom K F n) ∧ C.IsReduced ∧ IsMatrixSymmetric C ∧
        supportSize C ≤ k ∧
        supportDepth C ≤ Δ ∧
        orbitSize C ≤ n ^ k ∧
        C.depth ≤ 2 * Δ + 1 ∧
        C.size ≤ 5 * n ^ k * (Fintype.card F.A + Fintype.card F.B + ∑ a, ∑ b, F.mult a b)

end Lax461425.CircuitsForPatterns
