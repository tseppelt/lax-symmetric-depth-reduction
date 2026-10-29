import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Function.Iterate
import Lax461425.HomomorphismPolynomials

/-!
---
title: Labelled graphs (Appendix C)
type: definition
---
An *$(\ell,r)$-labelled graph* is a `Pattern` `F` together with tuples
$\boldsymbol a \in A^\ell$, $\boldsymbol b \in B^r$ of labels. We write `F.A ⊕ F.B` for the
vertex set, call a vertex *isolated* if it has no incident edge, write $F^+$ for `F` with all
isolated vertices deleted, and $L^+(\boldsymbol F)$ for the set of non-isolated vertices that
carry at least one label (the labelled vertices of $F^+$).

For $k \geq 1$, $\Delta \geq 0$, a *root-exact decomposition* of $\boldsymbol F$ of depth
$\leq \Delta$ and width $\leq k$ is a rooted tree decomposition of $F^+$ (covering only the
non-isolated vertices, isolated vertices need not appear in any bag) of depth $\leq \Delta$
with bags of size $\leq k$ whose root bag is exactly $L^+(\boldsymbol F)$. This is *not* simply
`Forestwidth.DepthDecomposition` applied to `F`, since that structure requires covering *all*
vertices of `F` (including isolated ones) in some bag, which would force an oversized root bag
for an edgeless graph with many labels; see `PatternsLabelledUnlabelled` for the precise
relationship between the two notions when $\ell = r = 0$.

$\mathfrak T^{\Delta,k}_n(\ell,r)$ (resp. the $P$-restricted version, for a set of label
positions $P \subseteq \mathrm{Fin}\,\ell \oplus \mathrm{Fin}\,r$) is the $\mathbb K$-linear
span of the homomorphism polynomials `labelledHom K G n` of labelled graphs `G` admitting such a
decomposition (resp. such that every vertex of $L^+(G)$ carries a label at a position in $P$).
-/

namespace Lax461425Proofs.PatternsLabelledBasic

open Lax461425.HomomorphismPolynomials

/-- An `(ℓ, r)`-labelled graph: a `Pattern` together with label tuples on each side. A vertex
may carry several labels (several entries of `a`/`b` may coincide), and the pattern need not be
injectively labelled. -/
structure LabelledPattern (ℓ r : ℕ) where
  /-- The underlying bipartite multigraph. -/
  F : Pattern
  /-- The labels on the `A`-side. -/
  a : Fin ℓ → F.A
  /-- The labels on the `B`-side. -/
  b : Fin r → F.B

variable {ℓ r : ℕ}

/-- A vertex of a pattern is isolated if it has no incident edge. -/
def isIsolated (F : Pattern) : F.A ⊕ F.B → Prop
  | Sum.inl x => ∀ y, F.mult x y = 0
  | Sum.inr y => ∀ x, F.mult x y = 0

instance (F : Pattern) : DecidablePred (isIsolated F) := by
  intro v
  cases v with
  | inl x => unfold isIsolated; infer_instance
  | inr y => unfold isIsolated; infer_instance

/-- The (named, once-and-for-all) `Finset` of isolated vertices of `F`. We route every use of
"remove the isolated vertices from a bag" through `Finset.sdiff` with this *fixed* finset,
rather than through a fresh `Finset.filter (fun v => ¬ isIsolated F v) ⋯` at each use site:
`Finset.sdiff` only needs `DecidableEq`, so this sidesteps any possible mismatch between
differently-elaborated `DecidablePred (fun v => ¬ isIsolated F v)` instances (which are
propositionally but not always syntactically equal, and on which `Finset.filter` is
sensitive). -/
def isolatedSet (F : Pattern) : Finset (F.A ⊕ F.B) := Finset.univ.filter (isIsolated F)

theorem mem_isolatedSet {F : Pattern} {v : F.A ⊕ F.B} : v ∈ isolatedSet F ↔ isIsolated F v := by
  rw [isolatedSet, Finset.mem_filter]; simp

theorem not_isIsolated_iff_notMem {F : Pattern} {v : F.A ⊕ F.B} :
    ¬ isIsolated F v ↔ v ∉ isolatedSet F := by
  rw [mem_isolatedSet]

/-- The vertex (if any) labelled by a given label position. -/
def LabelledPattern.labelVertex (G : LabelledPattern ℓ r) : Fin ℓ ⊕ Fin r → G.F.A ⊕ G.F.B :=
  Sum.elim (fun i => Sum.inl (G.a i)) (fun j => Sum.inr (G.b j))

/-- $L^+(\boldsymbol F)$: the non-isolated vertices that carry at least one label. -/
def LabelledPattern.labelSupport (G : LabelledPattern ℓ r) : Finset (G.F.A ⊕ G.F.B) :=
  (Finset.univ.image G.labelVertex) \ isolatedSet G.F

theorem LabelledPattern.labelSupport_subset_image (G : LabelledPattern ℓ r) :
    G.labelSupport ⊆ Finset.univ.image G.labelVertex :=
  Finset.sdiff_subset

/-- A root-exact tree decomposition of `F⁺` (the non-isolated vertices of `F` alone), of depth
at most `Δ` and bags of size at most `k`, whose root bag is exactly `L⁺(G)`. -/
structure RootExactDecomposition (G : LabelledPattern ℓ r) (Δ k : ℕ) where
  /-- The nodes of the tree. -/
  Node : Type
  [fintypeNode : Fintype Node]
  /-- The root of the tree. -/
  root : Node
  /-- The parent of each node; the root is its own parent. -/
  parent : Node → Node
  parent_root : parent root = root
  /-- Every node is at distance at most `Δ` from the root. -/
  depth_le : ∀ t, parent^[Δ] t = root
  /-- The bag of each node. -/
  bag : Node → Finset (G.F.A ⊕ G.F.B)
  /-- The root bag is exactly the set of labelled non-isolated vertices. -/
  bag_root : bag root = G.labelSupport
  card_bag_le : ∀ t, (bag t).card ≤ k
  /-- Every non-isolated vertex lies in some bag (isolated vertices need not be covered). -/
  exists_mem_bag : ∀ v, ¬ isIsolated G.F v → ∃ t, v ∈ bag t
  /-- Both endpoints of every edge lie in a common bag. -/
  exists_edge_mem_bag : ∀ x y, G.F.mult x y ≠ 0 → ∃ t, Sum.inl x ∈ bag t ∧ Sum.inr y ∈ bag t
  /-- The nodes whose bags contain a vertex `v` induce a connected subtree: at most one node
  `t` is the root or has a parent whose bag does not contain `v`. (Unlike
  `Forestwidth.DepthDecomposition`, the root bag here need not be empty, so the disjunct
  `t = root` cannot be dropped: without it, the root could never be witnessed as an "entry
  point" for `v`, even when `v ∈ bag root`, breaking the intended connectivity meaning.) -/
  connected : ∀ v t t', v ∈ bag t → (t = root ∨ v ∉ bag (parent t)) → v ∈ bag t' →
    (t' = root ∨ v ∉ bag (parent t')) → t = t'

attribute [instance] RootExactDecomposition.fintypeNode

/-- `G ∈ 𝒯^{Δ,k}(ℓ,r)`: `G` admits a root-exact decomposition of depth `≤ Δ` and width `≤ k`. -/
def InClass (Δ k : ℕ) (G : LabelledPattern ℓ r) : Prop :=
  Nonempty (RootExactDecomposition G Δ k)

/-- `G ∈ 𝒯^{Δ,k}_P(ℓ,r)`: `G ∈ 𝒯^{Δ,k}(ℓ,r)` and every labelled non-isolated vertex of `G`
carries a label at a position in `P`. We take `P` to be a `Finset` of label positions (rather
than an arbitrary `Set`, as in the paper): since `Fin ℓ ⊕ Fin r` is finite this loses no
generality (every `Set` of positions is the coercion of some `Finset`), and keeps cardinality
bounds on `P` (used throughout `PatternsLabelledOps`) free of `Set.ncard`/`Set.Finite`
bookkeeping. -/
def InClassP (Δ k : ℕ) (P : Finset (Fin ℓ ⊕ Fin r)) (G : LabelledPattern ℓ r) : Prop :=
  InClass Δ k G ∧ G.labelSupport ⊆ Finset.univ.image (fun p : P => G.labelVertex p)

theorem InClassP.toInClass {Δ k : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)} {G : LabelledPattern ℓ r}
    (h : InClassP Δ k P G) : InClass Δ k G := h.1

/-- If `G ∈ 𝒯^{Δ,k}_P(ℓ,r)`, `|L⁺(G)| ≤ |P|`. -/
theorem InClassP.card_labelSupport_le {Δ k : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)}
    {G : LabelledPattern ℓ r} (h : InClassP Δ k P G) :
    G.labelSupport.card ≤ P.card := by
  calc G.labelSupport.card ≤ (Finset.univ.image (fun p : P => G.labelVertex p)).card :=
        Finset.card_le_card h.2
    _ ≤ (Finset.univ : Finset P).card := Finset.card_image_le
    _ = P.card := by rw [Finset.card_univ, Fintype.card_coe]

/-- The `(ℓ,r)`-labelled homomorphism polynomial $\boldsymbol F_n$, as a curried function of the
label images `v : Fin ℓ → Fin n` and `w : Fin r → Fin n`. -/
noncomputable def labelledHom (K : Type*) [CommSemiring K] (G : LabelledPattern ℓ r) (n : ℕ)
    (v : Fin ℓ → Fin n) (w : Fin r → Fin n) : MvPolynomial (Fin n × Fin n) K :=
  ∑ hA : G.F.A → Fin n, ∑ hB : G.F.B → Fin n,
    if (∀ i, hA (G.a i) = v i) ∧ (∀ j, hB (G.b j) = w j) then
      ∏ x, ∏ y, MvPolynomial.X (hA x, hB y) ^ G.F.mult x y
    else 0

end Lax461425Proofs.PatternsLabelledBasic
