import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Function.Iterate
import Lax461425.HomomorphismPolynomials

/-!
---
title: Δ-forestwidth
type: definition
---
A *tree decomposition* of a graph $F$ is a tree $T$ with bags $\beta(t) \subseteq V(F)$ for
$t \in V(T)$ such that every vertex of $F$ lies in some bag, both endpoints of every edge lie
in a common bag, and, for every vertex $v$ of $F$, the nodes whose bags contain $v$ induce a
connected subtree of $T$. Edge multiplicities play no role.

Let $\Delta \geq 1$. The *$\Delta$-forestwidth* $\mathrm{fw}_\Delta(F)$ of $F$ is the least
$w \geq 0$ such that $F$ admits a tree decomposition $(T, \beta)$ with root $r$ such that $T$
has depth at most $\Delta$, $\beta(r) = \emptyset$, and $|\beta(t)| \leq w + 1$ for all
$t \in V(T)$. Equivalently, deleting $r$ yields a forest decomposition of $F$ in which every
root-leaf path has at most $\Delta$ nodes. This is a modification of the $\Delta$-treewidth,
for which this forest decomposition is required to be a tree decomposition.

We formalise the statement $\mathrm{fw}_\Delta(F) \leq w$ as the existence of such a
decomposition. A rooted tree of depth at most $\Delta$ is given by its finite set of nodes,
its root $r$, and the parent map, extended by $\mathrm{parent}(r) = r$, such that
$\mathrm{parent}^\Delta(t) = r$ for every node $t$. In such a tree, a set $U$ of nodes induces
a connected subtree if, and only if, at most one node $t \in U$ is the root or has its parent
outside $U$. As the root bag is empty, it suffices to require for every vertex $v$ that at
most one node $t$ has $v \in \beta(t)$ and $v \notin \beta(\mathrm{parent}(t))$.
-/

namespace Lax461425.Forestwidth

open HomomorphismPolynomials

/-- A tree decomposition of the pattern `F` whose tree has depth at most `Δ` and an empty root
bag, and whose bags have at most `k` elements. -/
structure DepthDecomposition (F : Pattern) (Δ k : ℕ) where
  /-- The nodes of the tree. -/
  Node : Type
  [fintypeNode : Fintype Node]
  /-- The root of the tree. -/
  root : Node
  /-- The parent of each node; the root is its own parent. -/
  parent : Node → Node
  parent_root : parent root = root
  /-- Every node is at distance at most `Δ` from the root. -/
  depth_le : ∀ t, parent^[Δ] t = root
  /-- The bag of each node. -/
  bag : Node → Finset (F.A ⊕ F.B)
  bag_root : bag root = ∅
  card_bag_le : ∀ t, (bag t).card ≤ k
  /-- Every vertex lies in some bag. -/
  exists_mem_bag : ∀ v, ∃ t, v ∈ bag t
  /-- Both endpoints of every edge lie in a common bag. -/
  exists_edge_mem_bag : ∀ a b, F.mult a b ≠ 0 → ∃ t, Sum.inl a ∈ bag t ∧ Sum.inr b ∈ bag t
  /-- The nodes whose bags contain a vertex `v` induce a connected subtree: at most one of
  them has a parent whose bag does not contain `v`. -/
  connected : ∀ v t t', v ∈ bag t → v ∉ bag (parent t) → v ∈ bag t' → v ∉ bag (parent t') →
    t = t'

attribute [instance] DepthDecomposition.fintypeNode

/-- `fw_Δ(F) ≤ w`: the pattern `F` has a tree decomposition of depth at most `Δ` with empty
root bag and bags of size at most `w + 1`. -/
def ForestwidthLE (Δ w : ℕ) (F : Pattern) : Prop :=
  Nonempty (DepthDecomposition F Δ (w + 1))

end Lax461425.Forestwidth
