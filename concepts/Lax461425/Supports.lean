import Lax461425.MatrixSymmetry

/-!
---
title: Supports and support depth
type: definition
---
Let $C$ be a circuit with variables $\mathcal{X}_n$. For $S \subseteq [n] \uplus [n]$, let
$\mathbf{Stab}^\bullet(S) \leq \Gamma_n$ be the pointwise stabiliser of $S$. The set $S$
*supports* a gate $g$ if every circuit automorphism extending an element of
$\mathbf{Stab}^\bullet(S)$ fixes $g$. If $C$ is rigid, then $\Gamma_n$ acts on the gates of
$C$, and this says that $\mathbf{Stab}^\bullet(S)$ fixes $g$. The *support size* of $C$ is the
least $k$ such that every gate of $C$ has a support of size at most $k$.

Write $\sup(g)$ for the intersection of all supports of $g$. If $g$ has a support $S$ with
$|S_L|, |S_R| < n/2$, where $S_L$ and $S_R$ are the two sides of $S$, then $\sup(g)$ is itself
a support of $g$, the unique minimal one. A wire from $h$ to $g$ is *support-changing* if
$\sup(h) \not\subseteq \sup(g)$. If the support size of $C$ is less than $n/2$, the *support
depth* of $C$ is the maximum number of support-changing wires on a path. Otherwise, the support
depth of $C$ is its depth. In either case, the support depth is at most the depth.

These notions are used for reduced circuits only, which are rigid. For an arbitrary
matrix-symmetric circuit, the support size and support depth are defined as those of an
equivalent reduced circuit, its rigidification.
-/

namespace Lax461425.Supports

open Circuits MatrixSymmetry

variable {K : Type*} {n : ℕ} (C : Circuit (Fin n × Fin n) K)

/-- `S` supports `g`: every circuit automorphism extending an element of `Γₙ` that fixes `S`
pointwise fixes `g`. -/
def IsSupport (g : C.Gate) (S : Set (Fin n ⊕ Fin n)) : Prop :=
  ∀ (γ : Γ n) (σ : C.Gate ≃ C.Gate), (∀ x ∈ S, actPoint γ x = x) → Extends C σ (actVar γ) → σ g = g

/-- The least `k` such that every gate has a support of size at most `k`. -/
noncomputable def supportSize : ℕ :=
  sInf {k | ∀ g, ∃ S, IsSupport C g S ∧ S.ncard ≤ k}

/-- `sup(g)`, the intersection of all supports of `g`. -/
def minSupport (g : C.Gate) : Set (Fin n ⊕ Fin n) :=
  {x | ∀ S, IsSupport C g S → x ∈ S}

/-- The number of support-changing wires on the path `p 0, …, p m`. -/
noncomputable def supportChanges {m : ℕ} (p : Fin (m + 1) → C.Gate) : ℕ :=
  {i : Fin m | ¬ minSupport C (p i.succ) ⊆ minSupport C (p i.castSucc)}.ncard

/-- The maximum number of support-changing wires on a path if the support size is less than
`n / 2`, and the depth otherwise. -/
noncomputable def supportDepth : ℕ :=
  if 2 * supportSize C < n then
    sSup {c | ∃ (m : ℕ) (p : Fin (m + 1) → C.Gate), C.IsPath p ∧ supportChanges C p = c}
  else
    C.depth

end Lax461425.Supports
