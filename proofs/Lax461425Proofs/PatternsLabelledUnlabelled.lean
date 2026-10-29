import Lax461425.Forestwidth
import Lax461425Proofs.PatternsLabelledBasic

/-!
---
title: Unlabelled graphs are the Δ-forestwidth-bounded ones (lem:labelled-unlabelled)
type: definition
---
For $\ell = r = 0$, an `(0,0)`-labelled graph is just a `Pattern` `F` with the (unique, empty)
label tuples; since `Fin 0 ⊕ Fin 0` is empty, `L⁺(F) = ∅` always. We show that, for
$k, \Delta \geq 1$, `F` (packaged as a `(0,0)`-labelled graph) admits a root-exact decomposition
of depth `≤ Δ` and width `≤ k` iff `Forestwidth.ForestwidthLE Δ (k - 1) F` holds, i.e. iff `F`
admits a `Forestwidth.DepthDecomposition F Δ k` (covering *all* vertices, including isolated
ones, with an empty root bag).

The two notions differ only in how isolated vertices are treated: a root-exact decomposition of
`F⁺` need not mention them at all, while a `DepthDecomposition` of `F` must place every vertex
in some bag. We pass between the two by removing isolated vertices from (resp. attaching a
singleton leaf bag for each isolated vertex to) the decomposition, using `Finset.sdiff` against
the fixed finset `isolatedSet F` throughout (never a fresh `Finset.filter`).

To avoid Lean having to reconcile the pattern `(ofPattern F).F` (appearing inside the type of a
`RootExactDecomposition (ofPattern F) Δ k`) with the literal pattern `F` at every step of a
tactic proof (the two are definitionally but not syntactically equal, since `ofPattern F` is a
`LabelledPattern` wrapping `F`), the main work is done for an *arbitrary* `G : LabelledPattern
0 0`, phrased entirely in terms of `G.F` (never introducing a separate `F`); only the very last
step specialises `G` to `ofPattern F`, which is then a harmless substitution.
-/

namespace Lax461425Proofs.PatternsLabelledUnlabelled

open Lax461425.HomomorphismPolynomials Lax461425.Forestwidth Lax461425Proofs.PatternsLabelledBasic

/-- The unique `(0,0)`-labelled graph structure on a pattern `F` (both label tuples are the
unique function out of `Fin 0`). -/
def ofPattern (F : Pattern) : LabelledPattern 0 0 := ⟨F, Fin.elim0, Fin.elim0⟩

/-- `L⁺` of a `(0,0)`-labelled graph is empty: there are no label positions at all. -/
theorem labelSupport_zero (G : LabelledPattern 0 0) : G.labelSupport = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  have hsub := G.labelSupport_subset_image
  obtain ⟨p, -, -⟩ := Finset.mem_image.mp (hsub hv)
  exact p.elim Fin.elim0 Fin.elim0

variable {G : LabelledPattern 0 0} {Δ k : ℕ}

/-- Isolated vertices, as a subtype. -/
abbrev IsolatedVertex (G : LabelledPattern 0 0) := {v : G.F.A ⊕ G.F.B // isIsolated G.F v}

theorem IsolatedVertex.val_mem_isolatedSet (v : IsolatedVertex G) : v.1 ∈ isolatedSet G.F :=
  mem_isolatedSet.mpr v.2

/-- The node type of the `DepthDecomposition` built from a root-exact decomposition: the nodes
of the root-exact decomposition, plus one new leaf (attached to the root) for every isolated
vertex. -/
abbrev AugNode (D : RootExactDecomposition G Δ k) := D.Node ⊕ IsolatedVertex G

section Forward

variable (D : RootExactDecomposition G Δ k)

/-- The parent map of the augmented tree: unchanged on old nodes, and the root for every new
leaf. -/
def augParent : AugNode D → AugNode D :=
  Sum.elim (fun t => Sum.inl (D.parent t)) (fun _ => Sum.inl D.root)

@[simp] theorem augParent_inl (t : D.Node) : augParent D (Sum.inl t) = Sum.inl (D.parent t) := rfl

@[simp] theorem augParent_inr (v : IsolatedVertex G) :
    augParent D (Sum.inr v) = Sum.inl D.root := rfl

/-- The bag map of the augmented tree: the old bags with isolated vertices removed, and a
singleton `{v}` for the new leaf attached for `v`. -/
def augBag : AugNode D → Finset (G.F.A ⊕ G.F.B) :=
  Sum.elim (fun t => D.bag t \ isolatedSet G.F) (fun v => {v.1})

@[simp] theorem augBag_inl (t : D.Node) : augBag D (Sum.inl t) = D.bag t \ isolatedSet G.F := rfl

@[simp] theorem augBag_inr (v : IsolatedVertex G) : augBag D (Sum.inr v) = {v.1} := rfl

theorem augParent_iterate_root : ∀ m, (augParent D)^[m] (Sum.inl D.root) = Sum.inl D.root := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, augParent_inl, D.parent_root]

theorem augParent_iterate_inl : ∀ (m : ℕ) (t : D.Node),
    (augParent D)^[m] (Sum.inl t) = Sum.inl (D.parent^[m] t) := by
  intro m
  induction m with
  | zero => intro t; rfl
  | succ n ih =>
    intro t
    rw [Function.iterate_succ_apply', ih t, augParent_inl, Function.iterate_succ_apply']

theorem augParent_iterate_succ_inr (m : ℕ) (v : IsolatedVertex G) :
    (augParent D)^[m + 1] (Sum.inr v) = Sum.inl D.root := by
  rw [Function.iterate_succ_apply, augParent_inr, augParent_iterate_root]

theorem augParent_depth_le (hΔ : 1 ≤ Δ) : ∀ t, (augParent D)^[Δ] t = Sum.inl D.root := by
  intro t
  match t with
  | Sum.inl t => rw [augParent_iterate_inl, D.depth_le]
  | Sum.inr v =>
    have hΔ' : Δ = (Δ - 1) + 1 := (Nat.succ_pred_eq_of_pos hΔ).symm
    have h := augParent_iterate_succ_inr D (Δ - 1) v
    rwa [← hΔ'] at h

/-- (→) A root-exact decomposition of `G` yields a `DepthDecomposition` of `G.F`: attach a
singleton leaf `{v}` below the root for every isolated vertex `v`, after first removing all
isolated vertices from the existing bags (so that no vertex is ever covered by two different
"entry points", which would break connectedness). -/
theorem depthDecomposition_of_rootExact (D : RootExactDecomposition G Δ k)
    (hΔ : 1 ≤ Δ) (hk : 1 ≤ k) : Nonempty (DepthDecomposition G.F Δ k) := by
  refine ⟨{ Node := AugNode D
            root := Sum.inl D.root
            parent := augParent D
            parent_root := by rw [augParent_inl, D.parent_root]
            depth_le := augParent_depth_le D hΔ
            bag := augBag D
            bag_root := by
              rw [augBag_inl, D.bag_root, labelSupport_zero]
              exact Finset.empty_sdiff _
            card_bag_le := fun t => by
              match t with
              | Sum.inl t =>
                rw [augBag_inl]
                exact (Finset.card_le_card Finset.sdiff_subset).trans (D.card_bag_le t)
              | Sum.inr v => rw [augBag_inr]; simpa using hk
            exists_mem_bag := fun v => by
              by_cases hv : isIsolated G.F v
              · exact ⟨Sum.inr ⟨v, hv⟩, by rw [augBag_inr]; exact Finset.mem_singleton_self _⟩
              · obtain ⟨t, ht⟩ := D.exists_mem_bag v hv
                exact ⟨Sum.inl t,
                  by rw [augBag_inl]; exact Finset.mem_sdiff.mpr ⟨ht, mem_isolatedSet.not.mpr hv⟩⟩
            exists_edge_mem_bag := fun x y hxy => by
              have hx : ¬ isIsolated G.F (Sum.inl x) := fun h => absurd (h y) hxy
              have hy : ¬ isIsolated G.F (Sum.inr y) := fun h => absurd (h x) hxy
              obtain ⟨t, htx, hty⟩ := D.exists_edge_mem_bag x y hxy
              exact ⟨Sum.inl t,
                by rw [augBag_inl]; exact Finset.mem_sdiff.mpr ⟨htx, mem_isolatedSet.not.mpr hx⟩,
                by rw [augBag_inl]; exact Finset.mem_sdiff.mpr ⟨hty, mem_isolatedSet.not.mpr hy⟩⟩
            connected := fun v t t' ht hpt ht' hpt' => by
              match t, t' with
              | Sum.inl t, Sum.inl t' =>
                rw [augBag_inl, Finset.mem_sdiff] at ht ht'
                have hvni : v ∉ D.bag (D.parent t) := by
                  intro hmem; apply hpt
                  rw [augParent_inl, augBag_inl]; exact Finset.mem_sdiff.mpr ⟨hmem, ht.2⟩
                have hvni' : v ∉ D.bag (D.parent t') := by
                  intro hmem; apply hpt'
                  rw [augParent_inl, augBag_inl]; exact Finset.mem_sdiff.mpr ⟨hmem, ht'.2⟩
                rw [D.connected v t t' ht.1 (Or.inr hvni) ht'.1 (Or.inr hvni')]
              | Sum.inl t, Sum.inr v' =>
                exfalso
                rw [augBag_inl, Finset.mem_sdiff] at ht
                rw [augBag_inr, Finset.mem_singleton] at ht'
                exact ht.2 (ht' ▸ v'.val_mem_isolatedSet)
              | Sum.inr v', Sum.inl t =>
                exfalso
                rw [augBag_inl, Finset.mem_sdiff] at ht'
                rw [augBag_inr, Finset.mem_singleton] at ht
                exact ht'.2 (ht ▸ v'.val_mem_isolatedSet)
              | Sum.inr v1, Sum.inr v2 =>
                rw [augBag_inr, Finset.mem_singleton] at ht ht'
                congr 1
                exact Subtype.ext (ht ▸ ht') }⟩

end Forward

section Backward

variable (D : DepthDecomposition G.F Δ k)

/-- The bag map of the root-exact decomposition built from a `DepthDecomposition`: the old bags
with isolated vertices removed. -/
def invBag : D.Node → Finset (G.F.A ⊕ G.F.B) := fun t => D.bag t \ isolatedSet G.F

@[simp] theorem invBag_apply (t : D.Node) : invBag D t = D.bag t \ isolatedSet G.F := rfl

/-- (←) A `DepthDecomposition` of `G.F` yields a root-exact decomposition of `G`: simply remove
the isolated vertices from every bag. -/
theorem rootExact_of_depthDecomposition (D : DepthDecomposition G.F Δ k) :
    Nonempty (RootExactDecomposition G Δ k) := by
  refine ⟨{ Node := D.Node
            root := D.root
            parent := D.parent
            parent_root := D.parent_root
            depth_le := D.depth_le
            bag := invBag D
            bag_root := by rw [invBag_apply, D.bag_root, labelSupport_zero]; exact Finset.empty_sdiff _
            card_bag_le := fun t => by
              rw [invBag_apply]; exact (Finset.card_le_card Finset.sdiff_subset).trans (D.card_bag_le t)
            exists_mem_bag := fun v hv => by
              obtain ⟨t, ht⟩ := D.exists_mem_bag v
              exact ⟨t, by rw [invBag_apply]; exact Finset.mem_sdiff.mpr ⟨ht, mem_isolatedSet.not.mpr hv⟩⟩
            exists_edge_mem_bag := fun x y hxy => by
              have hx : ¬ isIsolated G.F (Sum.inl x) := fun h => absurd (h y) hxy
              have hy : ¬ isIsolated G.F (Sum.inr y) := fun h => absurd (h x) hxy
              obtain ⟨t, htx, hty⟩ := D.exists_edge_mem_bag x y hxy
              exact ⟨t, by rw [invBag_apply]; exact Finset.mem_sdiff.mpr ⟨htx, mem_isolatedSet.not.mpr hx⟩,
                by rw [invBag_apply]; exact Finset.mem_sdiff.mpr ⟨hty, mem_isolatedSet.not.mpr hy⟩⟩
            connected := fun v t t' ht hpt ht' hpt' => by
              rw [invBag_apply, Finset.mem_sdiff] at ht ht'
              -- `D` is a genuine `Forestwidth.DepthDecomposition`, whose root bag is always
              -- `∅`; so the root can never satisfy `v ∈ bag t`, ruling out the `t = root`
              -- (resp. `t' = root`) disjunct of `hpt` (resp. `hpt'`).
              rcases hpt with rfl | hpt
              · exfalso; rw [D.bag_root] at ht; exact Finset.notMem_empty v ht.1
              rcases hpt' with rfl | hpt'
              · exfalso; rw [D.bag_root] at ht'; exact Finset.notMem_empty v ht'.1
              have hvni : v ∉ D.bag (D.parent t) := by
                intro hmem; apply hpt; rw [invBag_apply]; exact Finset.mem_sdiff.mpr ⟨hmem, ht.2⟩
              have hvni' : v ∉ D.bag (D.parent t') := by
                intro hmem; apply hpt'; rw [invBag_apply]; exact Finset.mem_sdiff.mpr ⟨hmem, ht'.2⟩
              exact D.connected v t t' ht.1 hvni ht'.1 hvni' }⟩

end Backward

/-- **lem:labelled-unlabelled**, for an arbitrary `(0,0)`-labelled graph `G`: for `k, Δ ≥ 1`,
`G` lies in `𝒯^{Δ,k}(0,0)` iff `fw_Δ(G.F) ≤ k - 1`. -/
theorem inClass_iff (hΔ : 1 ≤ Δ) (hk : 1 ≤ k) :
    InClass Δ k G ↔ ForestwidthLE Δ (k - 1) G.F := by
  have hk1 : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk
  unfold ForestwidthLE InClass
  rw [hk1]
  constructor
  · rintro ⟨D⟩; exact depthDecomposition_of_rootExact D hΔ hk
  · rintro ⟨D⟩; exact rootExact_of_depthDecomposition D

/-- **lem:labelled-unlabelled.** For `k, Δ ≥ 1`, the unlabelled pattern `F` (packaged as the
`(0,0)`-labelled graph `ofPattern F`) lies in `𝒯^{Δ,k}(0,0)` iff `fw_Δ(F) ≤ k - 1`. -/
theorem inClass_ofPattern_iff {F : Pattern} {Δ k : ℕ} (hΔ : 1 ≤ Δ) (hk : 1 ≤ k) :
    InClass Δ k (ofPattern F) ↔ ForestwidthLE Δ (k - 1) F :=
  inClass_iff hΔ hk

end Lax461425Proofs.PatternsLabelledUnlabelled
