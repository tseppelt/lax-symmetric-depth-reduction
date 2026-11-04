import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
---
title: Homomorphism polynomials
type: definition
---
A *pattern* is a finite bipartite multigraph $F$ with a fixed bipartition $A \uplus B$, where
parallel edges are allowed. It is given by the multiplicity $F(a, b) \in \mathbb{N}$ of the
edge $ab$ for all $a \in A$ and $b \in B$. Its vertex set is $V(F) = A \uplus B$, and its edges
are the pairs $ab$ with $F(a,b) > 0$. The *underlying simple graph* of $F$ has vertex set
$A \uplus B$, with $a \in A$ and $b \in B$ adjacent if $F(a, b) > 0$. For $n \in \mathbb{N}$, the *homomorphism polynomial* of
$F$ is
$$
  \hom_{F,n} = \sum_{\substack{h_A \colon A \to [n] \\ h_B \colon B \to [n]}}
    \prod_{ab \in E(F)} x_{h_A(a), h_B(b)} \in \mathbb{K}[\mathcal{X}_n],
$$
where the product counts edges with multiplicity. On the bi-adjacency matrix of a bipartite
graph, it counts the homomorphisms respecting the bipartitions.
-/

namespace Lax461425.HomomorphismPolynomials

/-- A finite bipartite multigraph with bipartition `A ⊎ B`. -/
structure Pattern where
  /-- The left side of the bipartition. -/
  A : Type
  /-- The right side of the bipartition. -/
  B : Type
  [fintypeA : Fintype A]
  [decEqA : DecidableEq A]
  [fintypeB : Fintype B]
  [decEqB : DecidableEq B]
  /-- `mult a b` is the number of edges between `a` and `b`. -/
  mult : A → B → ℕ

attribute [instance] Pattern.fintypeA Pattern.decEqA Pattern.fintypeB Pattern.decEqB

/-- The underlying simple graph of a pattern: `a` and `b` are adjacent if `F.mult a b ≠ 0`. -/
def underlying (F : Pattern) : SimpleGraph (F.A ⊕ F.B) :=
  SimpleGraph.fromRel fun u v => ∃ a b, u = Sum.inl a ∧ v = Sum.inr b ∧ F.mult a b ≠ 0

/-- The homomorphism polynomial `hom_{F,n}` in the variables `x_{i,j}` for `i, j ∈ [n]`. -/
noncomputable def hom (K : Type*) [CommSemiring K] (F : Pattern) (n : ℕ) :
    MvPolynomial (Fin n × Fin n) K :=
  ∑ hA : F.A → Fin n, ∑ hB : F.B → Fin n, ∏ a, ∏ b, MvPolynomial.X (hA a, hB b) ^ F.mult a b

end Lax461425.HomomorphismPolynomials
