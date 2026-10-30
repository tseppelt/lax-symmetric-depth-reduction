import Lax461425.NonUniformClosure
import Lax871432.ConnectedPartitions
import Lax871432.HomomorphismCounts
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
Definitions shared by the proof of `Lax461425.NonUniformClosure.hom_not_mem_homSpan`
(CFI graphs, bipartite homomorphism counts, the pattern without isolated vertices).
-/

namespace Lax461425Proofs.NU

open Lax461425.HomomorphismPolynomials Lax461425.NonUniformClosure
open Lax871432.ConnectedPartitions Lax871432.HomomorphismCounts

open scoped Classical

/-- The bipartite graph `B(H)` as a relation between its left side `X` and right side `X`:
`(u,0)` and `(v,1)` are adjacent iff `u = v` or `uv ∈ E(H)`. -/
def BRel {X : Type*} (H : SimpleGraph X) : X → X → Prop := fun u v => u = v ∨ H.Adj u v

/-- The number of bipartition-respecting homomorphisms of the pattern `F` into the bipartite
graph with left side `X`, right side `Y` and adjacency relation `R`. -/
noncomputable def homBip (F : Pattern) {X Y : Type*} (R : X → Y → Prop) : ℕ :=
  Nat.card {p : (F.A → X) × (F.B → Y) // ∀ a b, F.mult a b ≠ 0 → R (p.1 a) (p.2 b)}

/-- Vertices of the CFI graph `G_W`: a vertex `v` of `G` and a labelling `T` of the edges at `v`
(indexed by the neighbours of `v`) with `∑ T = W v`. -/
structure CfiV {V : Type} [Fintype V] (G : SimpleGraph V) (W : V → ZMod 2) where
  vertex : V
  label : G.neighborSet vertex → ZMod 2
  sum_label : ∑ u, label u = W vertex

/-- The CFI graph `G_W`: `(u,S) ~ (v,T)` iff `uv ∈ E(G)` and `S(uv) = T(uv)`. -/
def cfi {V : Type} [Fintype V] (G : SimpleGraph V) (W : V → ZMod 2) : SimpleGraph (CfiV G W) where
  Adj p q := ∃ h : G.Adj p.vertex q.vertex,
    p.label ⟨q.vertex, h⟩ = q.label ⟨p.vertex, h.symm⟩
  symm := ⟨fun _ _ ⟨h, h'⟩ => ⟨h.symm, h'.symm⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => G.irrefl h⟩

/-- The filled CFI graph `Ĝ_W`: additionally, all vertices over distinct non-adjacent vertices
of `G` are adjacent. -/
def cfiHat {V : Type} [Fintype V] (G : SimpleGraph V) (W : V → ZMod 2) : SimpleGraph (CfiV G W) where
  Adj p q := (cfi G W).Adj p q ∨ (p.vertex ≠ q.vertex ∧ ¬ G.Adj p.vertex q.vertex)
  symm := ⟨fun _ _ h => by
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨h1.symm, fun h => h2 h.symm⟩⟩
  loopless := ⟨fun p h => by
    rcases h with h | ⟨h1, _⟩
    · exact (cfi G W).loopless.irrefl p h
    · exact h1 rfl⟩

/-- Number of homomorphisms `F → G_W` lying over the homomorphism `ψ : F → G`. -/
noncomputable def cntOver {U V : Type} [Fintype V] {F : SimpleGraph U} {G : SimpleGraph V} (ψ : F →g G)
    (W : V → ZMod 2) : ℕ :=
  Nat.card {h : F →g cfi G W // ∀ x, (h x).vertex = ψ x}

/-- The spanning subgraph `F_ψ` of `F` of the edges `ab` with `ψ a ψ b ∈ E(G)`. -/
def Fpsi {U V : Type} (F : SimpleGraph U) (G : SimpleGraph V) (ψ : U → V) : SimpleGraph U :=
  F ⊓ G.comap ψ

/-- `ψ` as a homomorphism `F_ψ → G`. -/
def psiHom {U V : Type} (F : SimpleGraph U) (G : SimpleGraph V) (ψ : U → V) :
    Fpsi F G ψ →g G :=
  ⟨ψ, fun h => h.2⟩

/-- The pattern `F` with its isolated vertices removed. -/
def _root_.Lax461425.HomomorphismPolynomials.Pattern.nz (F : Pattern) : Pattern where
  A := {a // ∃ b, F.mult a b ≠ 0}
  B := {b // ∃ a, F.mult a b ≠ 0}
  mult a b := F.mult a b

end Lax461425Proofs.NU
