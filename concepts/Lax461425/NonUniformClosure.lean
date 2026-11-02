import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Span.Defs
import Lax68.GraphMinors
import Lax871432.ClosureProperties
import Lax461425.HomomorphismPolynomials
import Lax461425.Oddomorphisms

/-!
---
title: Homomorphism polynomials outside the span of a graph class
type: theorem
---
The *underlying simple graph* of a pattern $F$ with bipartition $A \uplus B$ has vertex set
$A \uplus B$, with $a \in A$ and $b \in B$ adjacent if $F(a, b) > 0$. A pattern $F$ belongs to
a class $\mathcal{F}$ of finite simple graphs if its underlying simple graph does. For a graph
$G$, let $\gamma(G) = \sum_{v \in V(G)} 2^{\deg_G(v) - 1}$, the number of vertices of a CFI
graph of $G$.

Let $\mathbb{K}$ be a field of characteristic zero. Let $\mathcal{F}$ be a class of finite
simple graphs that contains $K_1$, is minor-closed, and is closed under weak oddomorphisms.
Let $G \notin \mathcal{F}$ be a connected graph, let $F$ be a pattern whose underlying simple
graph contains $G$ as a minor, and let $N \geq \gamma(G)$. Then $\hom_{F,N}$ is not a linear
combination of homomorphism polynomials $\hom_{F',N}$ of patterns $F' \in \mathcal{F}$.

The proof distinguishes $\hom_{F,N}$ from all $\hom_{F',N}$ with $F' \in \mathcal{F}$ by
evaluating at the bi-adjacency matrices of two bipartite graphs with $N$ vertices on either
side, obtained from the two CFI graphs of $G$ by replacing the non-edges of $G$ with complete
bipartite graphs between the gadgets, passing to the bipartite double cover with a perfect
matching added, and padding with isolated vertices.
-/

namespace Lax461425.NonUniformClosure

open HomomorphismPolynomials Oddomorphisms Lax871432.GraphClasses Lax871432.ClosureProperties
  Lax68.GraphMinors

/-- The underlying simple graph of a pattern: `a` and `b` are adjacent if `F.mult a b ≠ 0`. -/
def underlying (F : Pattern) : SimpleGraph (F.A ⊕ F.B) :=
  SimpleGraph.fromRel fun u v => ∃ a b, u = Sum.inl a ∧ v = Sum.inr b ∧ F.mult a b ≠ 0

/-- `γ(G) = ∑_v 2^(deg v - 1)`, the number of vertices of a CFI graph of `G`. -/
noncomputable def cfiSize {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  ∑ v, 2 ^ ((G.neighborSet v).ncard - 1)

/-- The linear span of the homomorphism polynomials `hom_{F,N}` of the patterns `F ∈ 𝓕`. -/
noncomputable def homSpan (K : Type*) [CommSemiring K] (𝓕 : GraphClass) (N : ℕ) :
    Submodule K (MvPolynomial (Fin N × Fin N) K) :=
  Submodule.span K {q | ∃ F : Pattern, 𝓕.Mem (underlying F) ∧ hom K F N = q}

/-- If `𝓕` contains `K₁` and is closed under minors and weak oddomorphisms, `G ∉ 𝓕` is
connected, and `G` is a minor of (the underlying simple graph of) `F`, then `hom_{F,N}` is not
a linear combination of homomorphism polynomials of patterns in `𝓕`, for all `N ≥ γ(G)`. -/
axiom hom_not_mem_homSpan {K : Type*} [Field K] [CharZero K] (𝓕 : GraphClass)
    (hK₁ : 𝓕.Mem (⊥ : SimpleGraph (Fin 1))) (hminor : IsMinorClosed 𝓕)
    (hodd : IsWeakOddomorphismClosed 𝓕) {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) (hGF : ¬ 𝓕.Mem G) (F : Pattern) (hF : IsMinor G (underlying F))
    {N : ℕ} (hN : cfiSize G ≤ N) :
    hom K F N ∉ homSpan K 𝓕 N

end Lax461425.NonUniformClosure
