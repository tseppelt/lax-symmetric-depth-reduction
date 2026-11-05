import Lax461425.PatternWidths
import Lax461425.Forestwidth

/-!
---
title: Treedepth and Δ-forestwidth
type: theorem
---
If $\mathrm{fw}_\Delta(F) \leq w$, then $\mathrm{td}(F) \leq (w + 1)\Delta$: placing the
vertices introduced at a node of the decomposition in a chain below those introduced at its
ancestors gives an elimination forest. Conversely, if $\mathrm{td}(F) \leq t$, then
$\mathrm{fw}_t(F) \leq t - 1$: the nodes of an elimination forest below a new root, each with
the bag of vertices on its path to the root, form such a decomposition.
-/

namespace Lax461425.TreedepthForestwidth

open HomomorphismPolynomials Forestwidth PatternWidths

/-- Bounded-depth decompositions with bags of size at most `w + 1` give elimination forests
of height at most `(w + 1) * Δ`. -/
axiom treedepthLE_of_forestwidthLE {Δ w : ℕ} {F : Pattern} (h : ForestwidthLE Δ w F) :
    TreedepthLE ((w + 1) * Δ) F

/-- Elimination forests of height at most `t` give decompositions of depth at most `t` with
bags of size at most `t`. -/
axiom forestwidthLE_of_treedepthLE {t : ℕ} {F : Pattern} (h : TreedepthLE t F) :
    ForestwidthLE t (t - 1) F

end Lax461425.TreedepthForestwidth
