import Lax461425Proofs.Section6ABPSum
import Lax461425Proofs.SymmetricABPBasic

/-! Once the branch endpoints are fixed, every extending automorphism restricts to each branch. -/

namespace Lax461425Proofs.Section6ABPSum

open Lax461425.SymmetricABPs Lax461425.MatrixSymmetry
open scoped Classical

noncomputable section

variable {I V : Type} {K : Type*} [Fintype I] [Nonempty I] [Fintype V] [Field K]
variable (G : I → ABP V K) (c : I → K)
variable (σ : Vertex G ≃ Vertex G) (π : Equiv.Perm V)
variable (hσ : (abp G c).Extends σ π)

variable (hentry : ∀ i, σ (.entry i) = .entry i)
variable (hexit : ∀ i, σ (.exit i) = .exit i)

include hσ hentry hexit

theorem branch_source_fixed (i : I) : σ (.branch i (G i).source) = .branch i (G i).source := by
  have he := (hσ.2.2.1 (.entry i) (.branch i (G i).source)).2 ⟨rfl, rfl⟩
  rw [hentry i] at he
  cases hv : σ (.branch i (G i).source) with
  | source => simp [hv, edge] at he
  | entry _ => simp [hv, edge] at he
  | exit _ => simp [hv, edge] at he
  | sink => simp [hv, edge] at he
  | branch j v =>
    rw [hv] at he
    change ∃ h : i = j, h.symm ▸ v = (G i).source at he
    rcases he with ⟨rfl, rfl⟩
    rfl

theorem branch_image_exists (i : I) (v : (G i).Vertex) :
    ∃ w : (G i).Vertex, σ (.branch i v) = .branch i w := by
  induction (G i).source_reaches v with
  | refl => exact ⟨_, branch_source_fixed G c σ π hσ hentry hexit i⟩
  | @tail u v _ huv ih =>
    obtain ⟨w, hw⟩ := ih
    have he := (hσ.2.2.1 (.branch i u) (.branch i v)).2 ⟨rfl, huv⟩
    rw [hw] at he
    cases hv : σ (.branch i v) with
    | source => simp [hv, edge] at he
    | entry _ => simp [hv, edge] at he
    | sink => simp [hv, edge] at he
    | exit j =>
      have hf := hexit j
      have hh := σ.injective (hv.trans hf.symm)
      cases hh
    | branch j v' =>
      rw [hv] at he
      change ∃ h : i = j, (G i).edge w (h.symm ▸ v') at he
      rcases he with ⟨rfl, he⟩
      exact ⟨v', rfl⟩

def restrictVertex (i : I) (v : (G i).Vertex) : (G i).Vertex :=
  Classical.choose (branch_image_exists G c σ π hσ hentry hexit i v)

theorem restrictVertex_spec (i : I) (v : (G i).Vertex) :
    σ (.branch i v) = .branch i (restrictVertex G c σ π hσ hentry hexit i v) :=
  Classical.choose_spec (branch_image_exists G c σ π hσ hentry hexit i v)

omit hσ hentry hexit in
theorem branch_injective (i : I) : Function.Injective (Vertex.branch (G := G) i) := by
  intro u v huv
  cases huv
  rfl

theorem restrictVertex_injective (i : I) :
    Function.Injective (restrictVertex G c σ π hσ hentry hexit i) := by
  intro u v huv
  apply branch_injective G i
  apply σ.injective
  rw [restrictVertex_spec G c σ π hσ hentry hexit, restrictVertex_spec G c σ π hσ hentry hexit, huv]

/-- Restricting an extending automorphism to one branch gives a vertex permutation. -/
def restrict (i : I) : (G i).Vertex ≃ (G i).Vertex :=
  Equiv.ofBijective (restrictVertex G c σ π hσ hentry hexit i)
    ⟨restrictVertex_injective G c σ π hσ hentry hexit i,
      Finite.surjective_of_injective (restrictVertex_injective G c σ π hσ hentry hexit i)⟩

theorem restrict_extends (i : I) : (G i).Extends (restrict G c σ π hσ hentry hexit i) π := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply branch_injective G i
    exact (restrictVertex_spec G c σ π hσ hentry hexit i (G i).source).symm.trans
      (branch_source_fixed G c σ π hσ hentry hexit i)
  · have he := (hσ.2.2.1 (.branch i (G i).sink) (.exit i)).2 ⟨rfl, rfl⟩
    rw [restrictVertex_spec G c σ π hσ hentry hexit, hexit i] at he
    exact he.2
  · intro u v
    have he := hσ.2.2.1 (.branch i u) (.branch i v)
    rw [restrictVertex_spec G c σ π hσ hentry hexit, restrictVertex_spec G c σ π hσ hentry hexit] at he
    simpa [edge, restrict, Equiv.ofBijective] using he
  · intro u v huv
    have hl := hσ.2.2.2 (.branch i u) (.branch i v) ⟨rfl, huv⟩
    rw [restrictVertex_spec G c σ π hσ hentry hexit, restrictVertex_spec G c σ π hσ hentry hexit] at hl
    simpa [label, restrict, Equiv.ofBijective] using hl

end
end Lax461425Proofs.Section6ABPSum
