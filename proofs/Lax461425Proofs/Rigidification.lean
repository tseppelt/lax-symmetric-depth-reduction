import Lax461425Proofs.RigidConstruction
import Lax461425Proofs.RigidReduced
import Lax461425Proofs.RigidSymmetric
import Lax461425Proofs.RigidComputes
import Lax461425Proofs.RigidSize
import Lax461425Proofs.RigidDepth
import Lax461425Proofs.RigidOrbit
import Lax461425.Rigidification

/-!
The rigidification theorem: every matrix-symmetric circuit can be replaced by a reduced
matrix-symmetric circuit computing the same polynomial, without increasing size, depth, or
orbit size.
-/

namespace Lax461425Proofs.Rigidification

open Lax461425.Circuits Lax461425.MatrixSymmetry

/--
---
conclusion: Lax461425.Rigidification.exists_reduced
---
Given a matrix-symmetric circuit `C`, the circuit `C' := RigidConstruction.reduced C` is
obtained by merging gates that are equivalent under a height-indexed recursive equivalence
relation (`RigidEquiv.Equiv`): input gates are equivalent iff they share a label, and internal
gates of matching height and label are equivalent iff they send the same total wire weight,
aggregated by equivalence class (`RigidWeight.W`), into every class of smaller height. `C'`
keeps only the classes (canonical representatives chosen via `RigidRep.rep`) from which the
class of the output gate can still be reached. `C'` is reduced because distinct classes are
never merged (`RigidReduced.isReduced_reduced`); it computes the same polynomial because every
gate computes what its class computes (`RigidComputes.computes_transfer`, via a determinism
lemma for `ComputesAt`); it has size and depth at most those of `C` because classes are
collapsed gates/wires (`RigidSize.size_reduced_le`) and every path of `C'` lifts to a
same-length path of `C` (`RigidDepth.depth_reduced_le`); it is matrix-symmetric because every
automorphism of `C` preserves the equivalence relation and height (`RigidSymmetric`), hence
induces an automorphism of `C'` extending the same renaming; and since `C'` is reduced and
matrix-symmetric it is rigid (`Lax461425.ReducedRigid.isRigid`), which forces every
automorphism of `C'` to be induced this way, so orbits of `C'` are images of orbits of `C` and
hence no larger (`RigidOrbit.orbitSize_reduced_le`).
-/
theorem exists_reduced {K : Type*} [CommSemiring K] {n : ℕ}
    (C : Circuit (Fin n × Fin n) K) (hsym : IsMatrixSymmetric C)
    {p : MvPolynomial (Fin n × Fin n) K} (hp : C.Computes p) :
    ∃ C' : Circuit (Fin n × Fin n) K,
      C'.IsReduced ∧ IsMatrixSymmetric C' ∧ C'.Computes p ∧
        C'.size ≤ C.size ∧ C'.depth ≤ C.depth ∧ orbitSize C' ≤ orbitSize C :=
  ⟨RigidConstruction.reduced C, RigidReduced.isReduced_reduced C,
    RigidSymmetric.isMatrixSymmetric_reduced C hsym,
    RigidComputes.computes_transfer C hp,
    RigidSize.size_reduced_le C,
    RigidDepth.depth_reduced_le C,
    RigidOrbit.orbitSize_reduced_le C hsym⟩

end Lax461425Proofs.Rigidification
