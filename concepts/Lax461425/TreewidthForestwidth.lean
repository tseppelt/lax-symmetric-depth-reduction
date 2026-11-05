import Lax461425.PatternWidths
import Lax461425.Forestwidth

/-!
---
title: Treewidth and Δ-forestwidth
type: theorem
---
A pattern has treewidth at most $w$ if, and only if, $\mathrm{fw}_\Delta(F) \leq w$ for some
$\Delta \geq 1$. A decomposition witnessing $\mathrm{fw}_\Delta(F) \leq w$ is a tree
decomposition with bags of size at most $w + 1$. Conversely, rooting a tree decomposition of
width at most $w$ at any node and adding a new root with an empty bag gives such a
decomposition whose depth is at most the number of nodes plus one.
-/

namespace Lax461425.TreewidthForestwidth

open HomomorphismPolynomials Forestwidth PatternWidths

/-- A bounded-depth decomposition with empty root bag is a tree decomposition. -/
axiom treewidthLE_of_forestwidthLE {Δ w : ℕ} {F : Pattern} (h : ForestwidthLE Δ w F) :
    TreewidthLE w F

/-- Every tree decomposition can be rooted below a new node with an empty bag. -/
axiom exists_forestwidthLE_of_treewidthLE {w : ℕ} {F : Pattern} (h : TreewidthLE w F) :
    ∃ Δ, 1 ≤ Δ ∧ ForestwidthLE Δ w F

end Lax461425.TreewidthForestwidth
