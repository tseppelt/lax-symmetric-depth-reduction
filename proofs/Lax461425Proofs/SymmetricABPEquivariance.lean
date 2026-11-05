import Lax461425Proofs.SymmetricABPPaths
import Lax461425.SymmetricABPs

/-!
An extending ABP automorphism permutes source-to-sink paths and renames their weights.
Consequently every polynomial computed by a matrix-symmetric ABP is matrix invariant.
-/

namespace Lax461425Proofs.SymmetricABPEquivariance

open Lax461425.SymmetricABPs Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies
open SymmetricABPPaths

variable {V K : Type*} (G : ABP V K)

/-- Transport a path through an endpoint-fixing graph automorphism. -/
def mapPath (σ : G.Vertex ≃ G.Vertex) (hs : σ G.source = G.source)
    (ht : σ G.sink = G.sink)
    (he : ∀ u v, G.edge (σ u) (σ v) ↔ G.edge u v) (p : G.Path) : G.Path :=
  ⟨⟨p.1.1, σ ∘ p.1.2⟩, by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Function.comp_apply, p.2.1] using hs
    · simpa only [Function.comp_apply, p.2.2.1] using ht
    · intro i
      exact (he _ _).2 (p.2.2.2 i)⟩

variable [Fintype V] [CommSemiring K]

/-- An extending automorphism acts bijectively on the literal finite path set. -/
def pathEquiv {σ : G.Vertex ≃ G.Vertex} {π : V → V} (hσ : G.Extends σ π) :
    G.Path ≃ G.Path where
  toFun := mapPath G σ hσ.1 hσ.2.1 hσ.2.2.1
  invFun := mapPath G σ.symm
    (by simpa using (congrArg σ.symm hσ.1).symm)
    (by simpa using (congrArg σ.symm hσ.2.1).symm)
    (fun u v => by simpa using (hσ.2.2.1 (σ.symm u) (σ.symm v)).symm)
  left_inv p := by
    apply path_ext G
    · rfl
    · intro i j hij
      change σ.symm (σ (p.1.2 i)) = p.1.2 j
      rw [σ.symm_apply_apply]
      exact congrArg p.1.2 (Fin.ext hij)
  right_inv p := by
    apply path_ext G
    · rfl
    · intro i j hij
      change σ (σ.symm (p.1.2 i)) = p.1.2 j
      rw [σ.apply_symm_apply]
      exact congrArg p.1.2 (Fin.ext hij)

end Lax461425Proofs.SymmetricABPEquivariance
