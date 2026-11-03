import Lax461425Proofs.SymmetricABPPaths
import Lax461425.SymmetricABPFamilies

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

theorem pathWeight_rename {σ : G.Vertex ≃ G.Vertex} {π : V → V}
    (hσ : G.Extends σ π) (p : G.Path) :
    G.pathWeight (pathEquiv G hσ p) = MvPolynomial.rename π (G.pathWeight p) := by
  classical
  change (∏ i : Fin p.1.1.val,
    (G.label (σ (p.1.2 i.castSucc)) (σ (p.1.2 i.succ))).polynomial) =
    MvPolynomial.rename π (∏ i : Fin p.1.1.val,
      (G.label (p.1.2 i.castSucc) (p.1.2 i.succ)).polynomial)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact hσ.2.2.2 _ _ (p.2.2.2 i)

theorem polynomial_rename {σ : G.Vertex ≃ G.Vertex} {π : V → V}
    (hσ : G.Extends σ π) : MvPolynomial.rename π G.polynomial = G.polynomial := by
  classical
  change MvPolynomial.rename π (∑ p : G.Path, G.pathWeight p) =
    ∑ p : G.Path, G.pathWeight p
  rw [map_sum]
  calc
    (∑ p : G.Path, MvPolynomial.rename π (G.pathWeight p)) =
        ∑ p : G.Path, G.pathWeight (pathEquiv G hσ p) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (pathWeight_rename G hσ p).symm
    _ = _ := (pathEquiv G hσ).sum_comp _

theorem matrixInvariant {n : ℕ} (G : ABP (Fin n × Fin n) K)
    (hG : G.IsMatrixSymmetric) : MatrixInvariant G.polynomial := by
  intro γ
  obtain ⟨σ, hσ⟩ := hG γ
  exact polynomial_rename G hσ

theorem inSymVBP_matrixInvariant {K : Type*} [CommSemiring K] {f : MatrixFamily K}
    (hf : InSymVBP f) : ∀ n, MatrixInvariant (f n) := by
  rcases hf with ⟨b, hb, hf⟩
  intro n
  obtain ⟨G, hcomp, hsym, hbound⟩ := hf n
  rw [← hcomp]
  exact matrixInvariant G hsym

end Lax461425Proofs.SymmetricABPEquivariance
