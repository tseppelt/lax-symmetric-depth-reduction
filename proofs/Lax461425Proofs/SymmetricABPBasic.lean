import Lax461425.SymmetricABPs
import Mathlib.Tactic

/-!
Basic facts about the Section 6 ABPs. The layer lemma applies to every extending
automorphism; no uniqueness of the chosen extensions is assumed.
-/

namespace Lax461425Proofs.SymmetricABPBasic

open Lax461425.SymmetricABPs Lax461425.MatrixSymmetry

variable {V K : Type*} [Fintype V] [CommSemiring K]

theorem extends_refl (G : ABP V K) : G.Extends (Equiv.refl _) id := by
  refine ⟨rfl, rfl, fun _ _ => Iff.rfl, ?_⟩
  intro u v _
  simp

/-- A layer number increasing by one on each edge is fixed by every source-fixing
graph automorphism. -/
theorem layer_preserved (G : ABP V K) (layer : G.Vertex → ℕ)
    (hstep : ∀ u v, G.edge u v → layer v = layer u + 1)
    {σ : G.Vertex ≃ G.Vertex} {π : V → V} (hσ : G.Extends σ π) (v : G.Vertex) :
    layer (σ v) = layer v := by
  induction G.source_reaches v with
  | refl => rw [hσ.1]
  | @tail b c _ hbc ih =>
    rw [hstep _ _ ((hσ.2.2.1 b c).2 hbc), hstep _ _ hbc, ih]

variable {n : ℕ} (G : ABP (Fin n × Fin n) K)

theorem source_mem_orbit : G.source ∈ G.orbit G.source := by
  refine ⟨1, Equiv.refl _, ?_, rfl⟩
  have h : actVar (1 : Γ n) = id := by ext x <;> rfl
  rw [h]
  exact extends_refl G

theorem orbit_source : G.orbit G.source = {G.source} := by
  ext v
  constructor
  · rintro ⟨γ, σ, hσ, rfl⟩
    exact hσ.1
  · intro h
    rcases h with rfl
    exact source_mem_orbit G

theorem orbit_sink : G.orbit G.sink = {G.sink} := by
  ext v
  constructor
  · rintro ⟨γ, σ, hσ, rfl⟩
    exact hσ.2.1
  · intro h
    rcases h with rfl
    refine ⟨1, Equiv.refl _, ?_, rfl⟩
    have h : actVar (1 : Γ n) = id := by ext x <;> rfl
    rw [h]
    exact extends_refl G

end Lax461425Proofs.SymmetricABPBasic
