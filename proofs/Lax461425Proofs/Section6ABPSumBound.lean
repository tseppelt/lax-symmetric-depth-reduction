import Lax461425Proofs.Section6ABPSumOrbits

/-! All-automorphism orbit bounds for finite sums with fixed branch endpoints. -/

namespace Lax461425Proofs.Section6ABPSum

open Lax461425.SymmetricABPs Lax461425.MatrixSymmetry
open scoped Classical

noncomputable section

variable {I : Type} {K : Type*} [Fintype I] [Nonempty I] [Field K] {n : ℕ}
variable (G : I → ABP (Fin n × Fin n) K) (c : I → K)

variable (hfixed : ∀ (σ : Vertex G ≃ Vertex G) (π : Equiv.Perm (Fin n × Fin n)),
  (abp G c).Extends σ π →
    (∀ i, σ (.entry i) = .entry i) ∧ (∀ i, σ (.exit i) = .exit i))

include hfixed

theorem orbit_entry_le (i : I) : ((abp G c).orbit (.entry i)).ncard ≤ 1 := by
  have hs : (abp G c).orbit (.entry i) ⊆ {Vertex.entry i} := by
    rintro w ⟨γ, σ, hσ, rfl⟩
    exact (hfixed σ (Equiv.prodCongr γ.1 γ.2) hσ).1 i
  calc
    _ ≤ ({Vertex.entry i} : Set (Vertex G)).ncard := Set.ncard_le_ncard hs
    _ = 1 := Set.ncard_singleton _

theorem orbit_exit_le (i : I) : ((abp G c).orbit (.exit i)).ncard ≤ 1 := by
  have hs : (abp G c).orbit (.exit i) ⊆ {Vertex.exit i} := by
    rintro w ⟨γ, σ, hσ, rfl⟩
    exact (hfixed σ (Equiv.prodCongr γ.1 γ.2) hσ).2 i
  calc
    _ ≤ ({Vertex.exit i} : Set (Vertex G)).ncard := Set.ncard_le_ncard hs
    _ = 1 := Set.ncard_singleton _

theorem orbit_branch_le (i : I) (v : (G i).Vertex) :
    ((abp G c).orbit (.branch i v)).ncard ≤ (G i).orbitSize := by
  have hs : (abp G c).orbit (.branch i v) ⊆
      (Vertex.branch (G := G) i) '' (G i).orbit v := by
    rintro w ⟨γ, σ, hσ, rfl⟩
    let π : Equiv.Perm (Fin n × Fin n) := Equiv.prodCongr γ.1 γ.2
    refine ⟨restrict G c σ π hσ (hfixed σ π hσ).1 (hfixed σ π hσ).2 i v, ?_, ?_⟩
    · exact ⟨γ, restrict G c σ π hσ (hfixed σ π hσ).1 (hfixed σ π hσ).2 i,
        restrict_extends G c σ π hσ (hfixed σ π hσ).1 (hfixed σ π hσ).2 i, rfl⟩
    · exact (restrictVertex_spec G c σ π hσ (hfixed σ π hσ).1 (hfixed σ π hσ).2 i v).symm
  have hi : ((Vertex.branch (G := G) i) '' (G i).orbit v).ncard ≤ ((G i).orbit v).ncard :=
    Set.ncard_image_le
  exact (Set.ncard_le_ncard hs).trans (hi.trans
    (Finset.le_sup (f := fun w => ((G i).orbit w).ncard) (Finset.mem_univ v)))

/-- The number of summands does not enter the orbit bound. -/
theorem orbitSize_le (B : ℕ) (hB : 1 ≤ B) (hG : ∀ i, (G i).orbitSize ≤ B) :
    (abp G c).orbitSize ≤ B := by
  apply Finset.sup_le
  intro v _
  cases v with
  | source =>
    change ((abp G c).orbit (abp G c).source).ncard ≤ B
    rw [SymmetricABPBasic.orbit_source, Set.ncard_singleton]
    exact hB
  | sink =>
    change ((abp G c).orbit (abp G c).sink).ncard ≤ B
    rw [SymmetricABPBasic.orbit_sink, Set.ncard_singleton]
    exact hB
  | entry i => exact (orbit_entry_le G c hfixed i).trans hB
  | exit i => exact (orbit_exit_le G c hfixed i).trans hB
  | branch i v => exact (orbit_branch_le G c hfixed i v).trans (hG i)

end

end Lax461425Proofs.Section6ABPSum
