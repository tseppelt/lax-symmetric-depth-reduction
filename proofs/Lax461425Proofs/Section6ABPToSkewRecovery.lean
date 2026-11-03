import Lax461425Proofs.Section6ABPToSkewComputes
import Lax461425Proofs.Section6ABPToSkewSymmetry

/-!
Recovering ABP structure from every extending automorphism of the constructed circuit.
This direction is needed because orbit bounds cannot be inferred just from the extensions
constructed in the forward direction.
-/

namespace Lax461425Proofs.Section6ABPToSkew

open Lax461425.Circuits Lax461425.SymmetricABPs Lax461425.MatrixSymmetry
open scoped Classical

noncomputable section

variable {V : Type} {K : Type*} [Fintype V] [CommSemiring K]
variable (G : ABP V K) (τ : Gate G ≃ Gate G) (π : Equiv.Perm V)
variable (hτ : Extends (circuit G) τ π)

include hτ

/-- State wire preservation on the explicit gate type, keeping coercion instances stable. -/
theorem preserves_wire (g h : Gate G) :
    wire G (τ g) (τ h) = wire G g h := hτ.2 g h

theorem vertex_image_exists (v : G.Vertex) :
    ∃ w, τ (.vertex v) = .vertex w := by
  have hl : label G (τ (.vertex v)) = .add := hτ.1 (.vertex v)
  cases he : τ (.vertex v) with
  | vertex w => exact ⟨w, rfl⟩
  | term _ _ => simp [he, label] at hl
  | coeff _ _ => simp [he, label] at hl
  | inputVar _ _ => simp [he, label] at hl
  | sourceOne => simp [he, label] at hl

/-- The induced map on ABP vertices, recovered from the sum-gate labels. -/
def recoverVertex (v : G.Vertex) : G.Vertex :=
  Classical.choose (vertex_image_exists G τ π hτ v)

theorem recoverVertex_spec (v : G.Vertex) :
    τ (.vertex v) = .vertex (recoverVertex G τ π hτ v) :=
  Classical.choose_spec (vertex_image_exists G τ π hτ v)

theorem recoverVertex_injective : Function.Injective (recoverVertex G τ π hτ) := by
  intro u v huv
  have h : τ (.vertex u) = τ (.vertex v) := by
    rw [recoverVertex_spec G τ π hτ, recoverVertex_spec G τ π hτ, huv]
  exact Gate.vertex.inj (τ.injective h)

/-- Every extending circuit automorphism permutes the ABP vertex sum gates. -/
def recoverVertices : G.Vertex ≃ G.Vertex :=
  Equiv.ofBijective (recoverVertex G τ π hτ)
    ⟨recoverVertex_injective G τ π hτ,
      Finite.surjective_of_injective (recoverVertex_injective G τ π hτ)⟩

omit hτ in
theorem input_child_vertex {v : G.Vertex} {g : Gate G}
    (hi : (label G g).IsInput) (hw : 0 < wire G (.vertex v) g) :
    v = G.source ∧ g = .sourceOne := by
  cases g with
  | vertex _ => simp [label, GateLabel.IsInput] at hi
  | term _ _ => simp [label, GateLabel.IsInput] at hi
  | coeff _ _ => simp [wire] at hw
  | inputVar _ _ => simp [wire] at hw
  | sourceOne =>
    have hv : v = G.source := by by_contra hn; simp [wire, hn] at hw
    exact ⟨hv, rfl⟩

theorem recover_source : recoverVertices G τ π hτ G.source = G.source := by
  have hl := hτ.1 Gate.sourceOne
  have hi : (label G (τ Gate.sourceOne)).IsInput := by
    rw [show label G (τ Gate.sourceOne) = .const 1 from hl]
    trivial
  have hw := preserves_wire G τ π hτ (.vertex G.source) Gate.sourceOne
  rw [recoverVertex_spec G τ π hτ] at hw
  have hp : 0 < wire G (.vertex (recoverVertex G τ π hτ G.source)) (τ Gate.sourceOne) := by
    rw [hw]
    simp [wire]
  exact (input_child_vertex G hi hp).1

/-- Product gates recover both endpoints of their underlying edge. -/
theorem term_image_exists (e : Edge G) (x : Option V) :
    ∃ (f : Edge G) (y : Option V), τ (.term e x) = .term f y ∧
      f.1.1 = recoverVertices G τ π hτ e.1.1 ∧
      f.1.2 = recoverVertices G τ π hτ e.1.2 := by
  have hl : label G (τ (.term e x)) = .mul := hτ.1 (.term e x)
  cases he : τ (.term e x) with
  | vertex _ => simp [he, label] at hl
  | coeff _ _ => simp [he, label] at hl
  | inputVar _ _ => simp [he, label] at hl
  | sourceOne => simp [he, label] at hl
  | term f y =>
    refine ⟨f, y, rfl, ?_, ?_⟩
    · have hw := preserves_wire G τ π hτ (.term e x) (.vertex e.1.1)
      rw [he, recoverVertex_spec G τ π hτ] at hw
      have hh : f.1.1 = recoverVertex G τ π hτ e.1.1 := by
        by_contra hn
        simp [circuit, wire, hn] at hw
      exact hh
    · have hw := preserves_wire G τ π hτ (.vertex e.1.2) (.term e x)
      rw [he, recoverVertex_spec G τ π hτ] at hw
      have hh : f.1.2 = recoverVertex G τ π hτ e.1.2 := by
        by_contra hn
        simp [circuit, wire, hn] at hw
      exact hh

theorem recover_edge_forward {u v : G.Vertex} (huv : G.edge u v) :
    G.edge (recoverVertices G τ π hτ u) (recoverVertices G τ π hτ v) := by
  obtain ⟨f, y, hy, hu, hv⟩ := term_image_exists G τ π hτ ⟨(u, v), huv⟩ none
  simpa [hu, hv] using f.2

/-- On a finite graph a vertex permutation preserving edges also reflects edges. -/
theorem recover_edges (u v : G.Vertex) :
    G.edge (recoverVertices G τ π hτ u) (recoverVertices G τ π hτ v) ↔ G.edge u v := by
  let σ := recoverVertices G τ π hτ
  let f : Edge G → Edge G := fun e =>
    ⟨(σ e.1.1, σ e.1.2), recover_edge_forward G τ π hτ e.2⟩
  have hinj : Function.Injective f := by
    intro e e' he
    apply Subtype.ext
    have hh := congrArg Subtype.val he
    exact Prod.ext (σ.injective (congrArg Prod.fst hh))
      (σ.injective (congrArg Prod.snd hh))
  constructor
  · intro h
    obtain ⟨e, he⟩ := Finite.surjective_of_injective hinj ⟨(σ u, σ v), h⟩
    have hh := congrArg Subtype.val he
    have hu : e.1.1 = u := σ.injective (congrArg Prod.fst hh)
    have hv : e.1.2 = v := σ.injective (congrArg Prod.snd hh)
    simpa [hu, hv] using e.2
  · exact recover_edge_forward G τ π hτ

end
end Lax461425Proofs.Section6ABPToSkew
