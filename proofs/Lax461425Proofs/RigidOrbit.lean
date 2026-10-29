import Lax461425Proofs.RigidSymmetric
import Lax461425Proofs.RigidReduced
import Lax461425.ReducedRigid

/-!
Helper material for the rigidification proof: the reduced circuit `C'` has orbit size at most
that of `C`. Since `C'` is reduced and matrix-symmetric, it is rigid (`Lax461425.ReducedRigid`),
so every automorphism of `C'` extending some `γ` is the one induced by (any) automorphism of `C`
extending `γ`. Hence every orbit of `C'` is the image, under the quotient map, of an orbit of
`C`, and in particular no larger.
-/

namespace Lax461425Proofs.RigidOrbit

open Lax461425.Circuits Lax461425.MatrixSymmetry RigidHeight RigidEquiv RigidWeight RigidRep
  RigidConstruction RigidSymmetric RigidReduced

open scoped Classical

variable {K : Type*} {n : ℕ}

/-- Every orbit of the reduced circuit is contained in the image, under the quotient map, of
the corresponding orbit of `C`. -/
theorem orbit_reduced_subset (C : Circuit (Fin n × Fin n) K) (hsym : IsMatrixSymmetric C)
    (b : (reduced C).Gate) :
    orbit (reduced C) b ⊆ toC' C '' orbit C b.1 := by
  rintro g' ⟨γ, σ', hext', hg'⟩
  obtain ⟨σ, hextσ⟩ := hsym γ
  have hrigid := Lax461425.ReducedRigid.isRigid (reduced C) (isMatrixSymmetric_reduced C hsym)
    (isReduced_reduced C)
  have huniq : σ' = toC'Equiv C (show Extends C σ (⇑(Equiv.prodCongr γ.1 γ.2)) from hextσ) :=
    (hrigid γ).unique hext' (extends_toC'Equiv hextσ)
  rw [← hg', huniq]
  exact ⟨σ b.1, ⟨γ, σ, hextσ, rfl⟩, rfl⟩

/-- Every orbit of the reduced circuit is no larger than the corresponding orbit of `C`. -/
theorem orbit_reduced_ncard_le (C : Circuit (Fin n × Fin n) K) (hsym : IsMatrixSymmetric C)
    (b : (reduced C).Gate) : (orbit (reduced C) b).ncard ≤ (orbit C b.1).ncard :=
  calc (orbit (reduced C) b).ncard
      ≤ (toC' C '' orbit C b.1).ncard :=
        Set.ncard_le_ncard (orbit_reduced_subset C hsym b) (Set.toFinite _)
    _ ≤ (orbit C b.1).ncard := Set.ncard_image_le (Set.toFinite _)

/-- The reduced circuit has orbit size at most that of `C`. -/
theorem orbitSize_reduced_le (C : Circuit (Fin n × Fin n) K) (hsym : IsMatrixSymmetric C) :
    orbitSize (reduced C) ≤ orbitSize C := by
  show Finset.univ.sup (fun b : (reduced C).Gate => (orbit (reduced C) b).ncard) ≤ orbitSize C
  apply Finset.sup_le
  intro b _
  calc (orbit (reduced C) b).ncard ≤ (orbit C b.1).ncard := orbit_reduced_ncard_le C hsym b
    _ ≤ Finset.univ.sup (fun g => (orbit C g).ncard) :=
      Finset.le_sup (f := fun g => (orbit C g).ncard) (Finset.mem_univ b.1)

end Lax461425Proofs.RigidOrbit
