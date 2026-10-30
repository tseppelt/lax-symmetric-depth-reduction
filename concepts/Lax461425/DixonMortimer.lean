import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.Index

/-!
---
title: Subgroups of small index in the symmetric group
type: theorem
---
Let $n \geq 20$ and $1 \leq r \leq n/2$. If $H \leq \mathrm{Sym}_n$ has index less than
$\min\{\frac12\binom{n}{\lfloor n/2\rfloor}, \binom{n}{r}\}$, then
$\mathbf{Alt}_{(T)} \leq H$ for some $T \subseteq [n]$ with $|T| < r$, where
$\mathbf{Alt}_{(T)}$ is the pointwise stabiliser of $T$ in the alternating group.

This is cf. Dixon and Mortimer, Theorem 5.2B. The paper states it for $n \geq 9$; the
case $n \geq 20$ stated here is the one used in the support theorem, which assumes
$n \geq 20$.
-/

namespace Lax461425.DixonMortimer

open Equiv

/-- A subgroup of `Sym n` of small index contains the pointwise stabiliser, in the
alternating group, of fewer than `r` points. -/
axiom exists_fixingSubgroup_inf_alternatingGroup_le {n r : ℕ} (hn : 20 ≤ n) (hr : 1 ≤ r)
    (hrn : 2 * r ≤ n) (H : Subgroup (Perm (Fin n)))
    (hhalf : 2 * H.index < n.choose (n / 2)) (hr' : H.index < n.choose r) :
    ∃ T : Set (Fin n), T.ncard < r ∧
      fixingSubgroup (Perm (Fin n)) T ⊓ alternatingGroup (Fin n) ≤ H

end Lax461425.DixonMortimer
