import Lax461425.MatrixSymmetry

/-!
---
title: Reduced circuits are rigid
type: lemma
---
Every reduced matrix-symmetric circuit is rigid.

Two circuit automorphisms extending the same element of $\Gamma_n$ differ by a circuit
automorphism $\rho$ that fixes all input gates, since input labels are distinct. By induction
on the height, $\rho$ fixes every gate $g$: the gate $\rho(g)$ has the same label and the same
multiset of children as $g$, so $\rho(g) = g$ as $C$ is reduced.
-/

namespace Lax461425.ReducedRigid

open Circuits MatrixSymmetry

/-- Every reduced matrix-symmetric circuit is rigid. -/
axiom isRigid {K : Type*} {n : ℕ} (C : Circuit (Fin n × Fin n) K)
    (hsym : IsMatrixSymmetric C) (hred : C.IsReduced) : IsRigid C

end Lax461425.ReducedRigid
