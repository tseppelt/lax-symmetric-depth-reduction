import Mathlib.Data.Nat.Choose.Basic
import Lax461425.Supports

/-!
---
title: Support theorem
type: theorem
---
Let $n \geq 20$ and $\kappa \in \mathbb{N}$ with $3\kappa \leq n + 2$. Then every gate of a
reduced matrix-symmetric circuit of orbit size $< \binom{n}{\kappa}$ has a support of size
$\leq \kappa - 1$, i.e. the circuit has support size $\leq \kappa - 1$.

In the paper, the orbit size is bounded by a function $f \colon \mathbb{N} \to \mathbb{N}$,
and $\kappa_f(n) = \min\{r \in \mathbb{N} : \binom{n}{r} > f(n)\}$. The statement there is
that, if $n \geq 20$ and $3\kappa_f(n) \leq n + 2$, every gate of a reduced matrix-symmetric
circuit of orbit size $\leq f(n)$ has a minimal support of size $\leq \kappa_f(n) - 1$. This
is the case $\kappa = \kappa_f(n)$ of the statement above. Conversely, the statement above for
any $\kappa$ follows from the paper's for the constant function $f$ with value the orbit size,
since then $\kappa_f(n) \leq \kappa$. As $2(\kappa - 1) < n$, the minimal supports exist and
are contained in every support of size $\leq \kappa - 1$, so bounding the support size is the
same as bounding the size of the minimal supports.

The proof rests on a classical result on subgroups of small index in the symmetric group,
cf. Dixon and Mortimer, Theorem 5.2B: for $n \geq 9$ and $1 \leq r \leq n/2$, every subgroup
of $\mathrm{Sym}_n$ of index less than
$\min\{\frac12\binom{n}{\lfloor n/2 \rfloor}, \binom{n}{r}\}$ contains the pointwise
stabiliser of some set $T \subseteq [n]$ with $|T| < r$ in the alternating group. Reducedness
upgrades the alternating to the symmetric group.
-/

namespace Lax461425.SupportTheorem

open Circuits MatrixSymmetry Supports

/-- A reduced matrix-symmetric circuit of orbit size `< n.choose κ` has support size
`≤ κ - 1`, provided `n ≥ 20` and `3κ ≤ n + 2`. -/
axiom supportSize_le {K : Type*} {n κ : ℕ} (hn : 20 ≤ n) (hκ : 3 * κ ≤ n + 2)
    (C : Circuit (Fin n × Fin n) K) (hred : C.IsReduced) (hsym : IsMatrixSymmetric C)
    (horb : orbitSize C < n.choose κ) :
    supportSize C ≤ κ - 1

end Lax461425.SupportTheorem
