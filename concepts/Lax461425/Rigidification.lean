import Lax461425.MatrixSymmetry

/-!
---
title: Rigidification
type: lemma
---
For every matrix-symmetric circuit $C$, there is a reduced matrix-symmetric circuit $C'$
computing the same polynomial whose size, depth, and orbit size are at most those of $C$.

The circuit $C'$ is obtained by merging equivalent gates, where equivalence is defined by
induction on the height: input gates are equivalent if they have the same label, and internal
gates $g$ and $g'$ are equivalent if they have the same height and label and send the same
total multiplicity of wires into every class of gates of smaller height. Every circuit
automorphism of $C$ preserves this equivalence and induces a circuit automorphism of $C'$
extending the same element of $\Gamma_n$. Since $C'$ is rigid, the orbits of $C'$ are the
images of the orbits of $C$.
-/

namespace Lax461425.Rigidification

open Circuits MatrixSymmetry

/-- Every matrix-symmetric circuit can be replaced by a reduced matrix-symmetric circuit
computing the same polynomial, without increasing size, depth, or orbit size. -/
axiom exists_reduced {K : Type*} [CommSemiring K] {n : ℕ}
    (C : Circuit (Fin n × Fin n) K) (hsym : IsMatrixSymmetric C)
    {p : MvPolynomial (Fin n × Fin n) K} (hp : C.Computes p) :
    ∃ C' : Circuit (Fin n × Fin n) K,
      C'.IsReduced ∧ IsMatrixSymmetric C' ∧ C'.Computes p ∧
        C'.size ≤ C.size ∧ C'.depth ≤ C.depth ∧ orbitSize C' ≤ orbitSize C

end Lax461425.Rigidification
