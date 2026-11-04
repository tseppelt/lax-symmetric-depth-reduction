import Lax461425.MatrixSymmetry
import Lax461425.SymmetricFamilies
import Lax461425.HomomorphismPolynomials
import Lax183560.Pathwidth
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.MvPolynomial.Rename

/-!
---
title: Symmetric algebraic branching programs
type: definition
---
Definitions for Section 6. An ABP is a finite simple directed acyclic graph with affine
edge labels, a unique source and a unique sink. Vertex orbits range over all extending
automorphisms, rather than over a selected action of the symmetry group.

The pathwidth of a pattern is the pathwidth of its underlying simple graph.
-/

namespace Lax461425.SymmetricABPs

open Circuits MatrixSymmetry HomomorphismPolynomials

/-- An affine linear form, with an explicit coefficient for every variable. -/
structure AffineForm (V K : Type*) where
  constant : K
  coeff : V → K

/-- The polynomial represented by an affine form. -/
noncomputable def AffineForm.polynomial {V K : Type*} [Fintype V] [CommSemiring K]
    (a : AffineForm V K) : MvPolynomial V K :=
  MvPolynomial.C a.constant + ∑ x, MvPolynomial.C (a.coeff x) * MvPolynomial.X x

/-- A finite directed acyclic ABP. Every vertex occurs on a source-to-sink path. -/
structure ABP (V K : Type*) where
  Vertex : Type
  [fintypeVertex : Fintype Vertex]
  [decEqVertex : DecidableEq Vertex]
  edge : Vertex → Vertex → Prop
  [decEdge : DecidableRel edge]
  label : Vertex → Vertex → AffineForm V K
  source : Vertex
  sink : Vertex
  source_no_incoming : ∀ v, ¬ edge v source
  sink_no_outgoing : ∀ v, ¬ edge sink v
  acyclic : ∀ v, ¬ Relation.TransGen edge v v
  source_reaches : ∀ v, Relation.ReflTransGen edge source v
  reaches_sink : ∀ v, Relation.ReflTransGen edge v sink

attribute [instance] ABP.fintypeVertex ABP.decEqVertex ABP.decEdge

namespace ABP

variable {V K : Type*} (G : ABP V K)

/-- A bounded vertex sequence. Acyclic paths have fewer edges than there are vertices. -/
abbrev PathData := (l : Fin (Fintype.card G.Vertex)) × (Fin (l.val + 1) → G.Vertex)

/-- A vertex sequence traverses directed edges from the source to `v`. -/
def IsPathTo (v : G.Vertex) (p : G.PathData) : Prop :=
  p.2 0 = G.source ∧ p.2 (Fin.last p.1.val) = v ∧
    ∀ i : Fin p.1.val, G.edge (p.2 i.castSucc) (p.2 i.succ)

/-- All directed paths from the source to a specified vertex. -/
abbrev PathTo (v : G.Vertex) := {p : G.PathData // G.IsPathTo v p}

/-- A vertex sequence traverses directed edges from the source to the sink. -/
abbrev IsPath := G.IsPathTo G.sink

/-- All source-to-sink paths, including the empty path when source and sink coincide. -/
abbrev Path := G.PathTo G.sink

noncomputable instance (v : G.Vertex) : Fintype (G.PathTo v) := Fintype.ofFinite _

/-- The product of the labels along a path with any endpoint. -/
noncomputable def pathWeightTo [Fintype V] [CommSemiring K] {v : G.Vertex}
    (p : G.PathTo v) : MvPolynomial V K :=
  ∏ i : Fin p.1.1.val,
    (G.label (p.1.2 i.castSucc) (p.1.2 i.succ)).polynomial

/-- The product of the labels along a source-to-sink path. -/
noncomputable def pathWeight [Fintype V] [CommSemiring K] (p : G.Path) : MvPolynomial V K :=
  G.pathWeightTo p

/-- The sum of all source-to-`v` path weights. -/
noncomputable def polynomialAt [Fintype V] [CommSemiring K] (v : G.Vertex) :
    MvPolynomial V K := ∑ p : G.PathTo v, G.pathWeightTo p

/-- The sum of the weights of all source-to-sink paths. -/
noncomputable def polynomial [Fintype V] [CommSemiring K] : MvPolynomial V K :=
  G.polynomialAt G.sink

/-- The ABP computes the given polynomial. -/
def Computes [Fintype V] [CommSemiring K] (p : MvPolynomial V K) : Prop :=
  G.polynomial = p

/-- An ABP automorphism extending a renaming of the variables. Values of labels on
nonedges are immaterial. -/
def Extends [Fintype V] [CommSemiring K] (σ : G.Vertex ≃ G.Vertex) (π : V → V) : Prop :=
  σ G.source = G.source ∧ σ G.sink = G.sink ∧
    (∀ u v, G.edge (σ u) (σ v) ↔ G.edge u v) ∧
    ∀ u v, G.edge u v →
      (G.label (σ u) (σ v)).polynomial = MvPolynomial.rename π (G.label u v).polynomial

variable {n : ℕ} (G : ABP (Fin n × Fin n) K)

/-- Every matrix-variable permutation extends to an ABP automorphism. -/
def IsMatrixSymmetric [CommSemiring K] : Prop :=
  ∀ γ : Γ n, ∃ σ : G.Vertex ≃ G.Vertex, G.Extends σ (actVar γ)

/-- The vertex orbit under all extending ABP automorphisms. -/
def orbit [CommSemiring K] (v : G.Vertex) : Set G.Vertex :=
  {w | ∃ (γ : Γ n) (σ : G.Vertex ≃ G.Vertex), G.Extends σ (actVar γ) ∧ σ v = w}

/-- The largest vertex orbit under all extending ABP automorphisms. -/
noncomputable def orbitSize [CommSemiring K] : ℕ :=
  Finset.univ.sup fun v => (G.orbit v).ncard

end ABP

/-- The pattern has pathwidth at most `k`: its underlying simple graph has a path
decomposition with bags of size at most `k + 1`. -/
def PathwidthLE (k : ℕ) (F : Pattern) : Prop :=
  Lax183560.Pathwidth.HasPathwidthAtMost (underlying F) k

open SymmetricFamilies

/-- Families computed by matrix-symmetric ABPs of polynomial vertex-orbit size. No bound on
the total size or the degree is imposed. -/
def InSymVBP {K : Type*} [CommSemiring K] (f : MatrixFamily K) : Prop :=
  ∃ b : ℕ → ℕ, PolynomiallyBounded b ∧ ∀ n, ∃ G : ABP (Fin n × Fin n) K,
    G.Computes (f n) ∧ G.IsMatrixSymmetric ∧ G.orbitSize ≤ b n

end Lax461425.SymmetricABPs
