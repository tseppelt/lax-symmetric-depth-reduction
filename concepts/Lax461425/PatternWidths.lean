import Lax228581.Treewidth
import Lax183560.TreeDepth
import Lax183560.Pathwidth
import Lax461425.HomomorphismPolynomials

/-!
---
title: Treewidth, pathwidth, and treedepth of patterns
type: definition
---
The treewidth, pathwidth, and treedepth of a pattern are those of its underlying simple graph,
so edge multiplicities play no role. A pattern has treewidth at most $k$ if it has a tree
decomposition whose bags have at most $k + 1$ vertices, and pathwidth at most $k$ if it has
such a decomposition whose tree is a path. It has treedepth at most $t$ if it has an
elimination forest in which every root-leaf path has at most $t$ vertices. The pattern without
vertices has treewidth, pathwidth, and treedepth zero.
-/

namespace Lax461425.PatternWidths

open HomomorphismPolynomials

/-- The pattern has treewidth at most `k`: its underlying simple graph has a tree decomposition
with bags of size at most `k + 1`. -/
def TreewidthLE (k : ℕ) (F : Pattern) : Prop :=
  Lax228581.Treewidth.HasTreewidthAtMost (underlying F) k

/-- The pattern has pathwidth at most `k`: its underlying simple graph has a path
decomposition with bags of size at most `k + 1`. -/
def PathwidthLE (k : ℕ) (F : Pattern) : Prop :=
  Lax183560.Pathwidth.HasPathwidthAtMost (underlying F) k

/-- The pattern has treedepth at most `t`: its underlying simple graph lies in the closure of a
rooted forest in which every root-leaf path has at most `t` vertices. -/
def TreedepthLE (t : ℕ) (F : Pattern) : Prop :=
  Lax183560.TreeDepth.HasTreedepthAtMost (underlying F) t

end Lax461425.PatternWidths
