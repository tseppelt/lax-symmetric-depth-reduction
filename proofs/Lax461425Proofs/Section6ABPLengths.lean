import Lax461425Proofs.Section6ABPSumBound

/-!
The path-length argument in Lemma 6.5. Unit-labelled padding gives the layered
summands distinct lengths. Distances from the source and to the sink then fix each
branch under every extending automorphism, including automorphisms not chosen by
the matrix action. No distinguishing constants or divisions are used.
-/

namespace Lax461425Proofs.Section6ABPSum

open Lax461425.SymmetricABPs
open scoped Classical

noncomputable section

theorem layer_le_sink {V K : Type*} {G : ABP V K} (L : G.Layering) (v : G.Vertex) :
    L.layer v ≤ L.layer G.sink := by
  have hmono : ∀ {u w}, Relation.ReflTransGen G.edge u w → L.layer u ≤ L.layer w := by
    intro u w h
    induction h with
    | refl => exact le_refl _
    | @tail w z _ hwz ih =>
      have hs := L.edge_layer w z hwz
      omega
  exact hmono (G.reaches_sink v)

section BranchLengths

variable {I V : Type} {K : Type*} [Fintype I] [Nonempty I] [Fintype V] [Field K]
variable (G : I → ABP V K) (L : ∀ i, (G i).Layering)

/-- Distance from the global source, except at the common sink. -/
def forward : Vertex G → ℕ
  | .source => 0
  | .entry _ => 1
  | .branch i v => (L i).layer v + 2
  | .exit i => (L i).layer (G i).sink + 3
  | .sink => 0

/-- Distance to the global sink, except at the common source. -/
def backward : Vertex G → ℕ
  | .source => 0
  | .entry i => (L i).layer (G i).sink + 3
  | .branch i v => (L i).layer (G i).sink - (L i).layer v + 2
  | .exit _ => 1
  | .sink => 0

theorem forward_edge (u v : Vertex G) (h : edge G u v) (hv : v ≠ .sink) :
    forward G L v = forward G L u + 1 := by
  cases u <;> cases v <;> simp only [edge] at h
  all_goals try (exact False.elim h)
  case source.entry i => rfl
  case entry.branch i j v =>
    rcases h with ⟨rfl, rfl⟩
    simp [forward, (L i).source_layer]
  case branch.branch i u j v =>
    rcases h with ⟨rfl, h⟩
    have hs := (L i).edge_layer u v h
    dsimp only [forward]
    omega
  case branch.exit i u j =>
    rcases h with ⟨rfl, rfl⟩
    dsimp only [forward]
  case exit.sink i => exact (hv rfl).elim

theorem backward_edge (u v : Vertex G) (h : edge G u v) (hu : u ≠ .source) :
    backward G L u = backward G L v + 1 := by
  cases u <;> cases v <;> simp only [edge] at h
  all_goals try (exact False.elim h)
  case source.entry i => exact (hu rfl).elim
  case entry.branch i j v =>
    rcases h with ⟨rfl, rfl⟩
    dsimp only [backward]
    rw [(L i).source_layer]
    omega
  case branch.branch i u j v =>
    rcases h with ⟨rfl, h⟩
    have hs := (L i).edge_layer u v h
    have hb := layer_le_sink (L i) v
    dsimp only [backward]
    omega
  case branch.exit i u j =>
    rcases h with ⟨rfl, rfl⟩
    simp [backward]
  case exit.sink i => rfl

variable (c : I → K) (σ : Vertex G ≃ Vertex G) (π : Equiv.Perm V)
variable (hσ : (abp G c).Extends σ π)

include hσ

theorem forward_preserved (v : Vertex G) (hv : v ≠ .sink) :
    forward G L (σ v) = forward G L v := by
  revert hv
  induction (abp G c).source_reaches v with
  | refl => intro _; rw [hσ.1]
  | @tail u v _ he ih =>
    intro hv
    have hu : u ≠ .sink := by
      intro hu
      subst u
      exact (abp G c).sink_no_outgoing v he
    have hv' : σ v ≠ .sink := by
      intro hh
      exact hv (σ.injective (hh.trans hσ.2.1.symm))
    rw [forward_edge G L _ _ ((hσ.2.2.1 u v).2 he) hv',
      forward_edge G L u v he hv, ih hu]

theorem backward_preserved (v : Vertex G) (hv : v ≠ .source) :
    backward G L (σ v) = backward G L v := by
  revert hv
  induction (abp G c).reaches_sink v using Relation.ReflTransGen.head_induction_on with
  | refl => intro _; rw [hσ.2.1]
  | @head u v he _ ih =>
    intro hu
    have hv : v ≠ .source := by
      intro hv
      subst v
      exact (abp G c).source_no_incoming u he
    have hu' : σ u ≠ .source := by
      intro hh
      exact hu (σ.injective (hh.trans hσ.1.symm))
    rw [backward_edge G L _ _ ((hσ.2.2.1 u v).2 he) hu',
      backward_edge G L u v he hu, ih hv]

/-- Distinct source-to-sink branch lengths fix both endpoints of every branch.
The extra four edges in the sum are common to all branches. -/
theorem endpoints_fixed_of_lengths
    (hL : Function.Injective (fun i => (L i).layer (G i).sink)) :
    (∀ i, σ (.entry i) = .entry i) ∧ (∀ i, σ (.exit i) = .exit i) := by
  constructor
  · intro i
    have he := (hσ.2.2.1 .source (.entry i)).2 (show edge G .source (.entry i) from trivial)
    rw [hσ.1] at he
    cases hi : σ (.entry i) <;> simp only [hi, edge] at he
    all_goals try contradiction
    rename_i j
    have hd := backward_preserved G L c σ π hσ (.entry i) (by intro h; cases h)
    rw [hi] at hd
    dsimp only [backward] at hd
    exact congrArg (Vertex.entry (G := G)) (hL (Nat.add_right_cancel hd))
  · intro i
    have he := (hσ.2.2.1 (.exit i) .sink).2 (show edge G (.exit i) .sink from trivial)
    rw [hσ.2.1] at he
    cases hi : σ (.exit i) <;> simp only [hi, edge] at he
    all_goals try contradiction
    rename_i j
    have hd := forward_preserved G L c σ π hσ (.exit i) (by intro h; cases h)
    rw [hi] at hd
    dsimp only [forward] at hd
    exact congrArg (Vertex.exit (G := G)) (hL (Nat.add_right_cancel hd))

end BranchLengths

end
end Lax461425Proofs.Section6ABPSum
