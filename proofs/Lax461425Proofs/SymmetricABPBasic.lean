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

theorem orbitSize_le_card : G.orbitSize ≤ Fintype.card G.Vertex := by
  apply Finset.sup_le
  intro v _
  simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card (G.orbit v)

/-- Every extending automorphism preserves the layer, so an orbit fits inside a layer. -/
theorem orbit_subset_layer (layer : G.Vertex → ℕ)
    (hstep : ∀ u v, G.edge u v → layer v = layer u + 1) (v : G.Vertex) :
    G.orbit v ⊆ {w | layer w = layer v} := by
  rintro w ⟨γ, σ, hσ, rfl⟩
  exact layer_preserved G layer hstep hσ v

/-- Section 6's layer bound, with all extending automorphisms quantified. -/
theorem orbitSize_le_of_layer_bound (layer : G.Vertex → ℕ)
    (hstep : ∀ u v, G.edge u v → layer v = layer u + 1) (B : ℕ)
    (hB : ∀ i, ({v | layer v = i} : Set G.Vertex).ncard ≤ B) : G.orbitSize ≤ B := by
  apply Finset.sup_le
  intro v _
  exact (Set.ncard_le_ncard (orbit_subset_layer G layer hstep v)).trans (hB _)

end Lax461425Proofs.SymmetricABPBasic
