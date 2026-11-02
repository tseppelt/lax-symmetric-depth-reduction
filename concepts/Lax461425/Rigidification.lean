import Lax461425.MatrixSymmetry

/-!
---
title: Rigidification
type: lemma
---
For every matrix-symmetric circuit $C$, there is a reduced matrix-symmetric circuit $C'$
computing the same polynomial whose size, depth, and orbit size are at most those of $C$.
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
