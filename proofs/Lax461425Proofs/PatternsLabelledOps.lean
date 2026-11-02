import Lax461425Proofs.PatternsLabelledBasic
import Mathlib.LinearAlgebra.Span.Defs

/-!
---
title: Operations on labelled graphs (lem:labelled-ops)
type: definition
---
We establish the four closure properties of Appendix C's `lem:labelled-ops` for the classes
`𝒯^{Δ,k}(ℓ,r)` and `𝒯^{Δ,k}_P(ℓ,r)` of `PatternsLabelledBasic`:

1. Every edgeless `(ℓ,r)`-labelled graph lies in `𝒯^{0,k}_P(ℓ,r)`, for every `k` and every `P`
   (no hypothesis on `ℓ + r` vs `k` is needed: deleting the isolated vertices of an edgeless
   graph deletes *all* of its vertices, so `L⁺ = ∅` and the single-node tree with empty bag
   witnesses membership regardless of how many labels there are).
2. (deferred; needs the "gluing multiplies" fact)
3. Permuting the labels of a graph, or adding labels on fresh isolated vertices, preserves
   membership in `𝒯^{Δ,k}` (the same decomposition witnesses it).
4. Deleting some labels of a graph increases the depth bound by at most `1` (attach a new root
   above the old one, with bag = the remaining labelled non-isolated vertices).
-/

namespace Lax461425Proofs.PatternsLabelledOps

open Lax461425.HomomorphismPolynomials Lax461425Proofs.PatternsLabelledBasic
open scoped Classical

variable {ℓ r : ℕ}

/-! ### Item 1: edgeless graphs -/

/-- A pattern is edgeless if it has no edges at all. -/
def isEdgeless (F : Pattern) : Prop := ∀ x y, F.mult x y = 0

theorem isEdgeless.isIsolated {F : Pattern} (hF : isEdgeless F) (v : F.A ⊕ F.B) :
    isIsolated F v := by
  cases v with
  | inl x => intro y; exact hF x y
  | inr y => intro x; exact hF x y

/-- An edgeless pattern's label support is empty: deleting the isolated vertices of an edgeless
graph deletes *all* vertices (there is nothing left to label). -/
theorem labelSupport_eq_empty_of_edgeless {G : LabelledPattern ℓ r} (hG : isEdgeless G.F) :
    G.labelSupport = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  simp only [LabelledPattern.labelSupport, Finset.mem_sdiff] at hv
  exact hv.2 (mem_isolatedSet.mpr (hG.isIsolated v))

/-- Every edgeless `(ℓ,r)`-labelled graph lies in `𝒯^{Δ,k}_P(ℓ,r)`, for *every* `Δ, k` and every
set `P` of label positions: no hypothesis relating `ℓ + r` to `k` (nor `Δ ≥ 0`) is needed. The
single-node tree (depth `0`, hence depth `≤ Δ` for any `Δ`) with empty bag witnesses it. -/
theorem inClassP_of_edgeless' {G : LabelledPattern ℓ r} (hG : isEdgeless G.F) (Δ k : ℕ)
    (P : Finset (Fin ℓ ⊕ Fin r)) : InClassP Δ k P G := by
  have hempty := labelSupport_eq_empty_of_edgeless hG
  refine ⟨⟨{ Node := Unit
             root := ()
             parent := id
             parent_root := rfl
             depth_le := fun _ => rfl
             bag := fun _ => ∅
             bag_root := hempty.symm
             card_bag_le := fun _ => Nat.zero_le k
             exists_mem_bag := fun v hv => absurd (hG.isIsolated v) hv
             exists_edge_mem_bag := fun x y hxy => absurd (hG x y) hxy
             connected := fun v t t' _ht hpt _ht' _hpt' => by
               cases t; cases t'; rfl }⟩, ?_⟩
  rw [hempty]
  exact Finset.empty_subset _

/-! ### Item 3a: permuting labels -/

/-- Relabelling `G` by permuting the label positions on each side. -/
def relabel (G : LabelledPattern ℓ r) (σ : Equiv.Perm (Fin ℓ)) (τ : Equiv.Perm (Fin r)) :
    LabelledPattern ℓ r :=
  ⟨G.F, G.a ∘ σ, G.b ∘ τ⟩

/-! ### Item 3b: adding labels on fresh isolated vertices -/

/-- `G` extended by `m` fresh `A`-side and `m'` fresh `B`-side isolated vertices, carrying the
new label positions (the last `m`/`m'` positions, via `Fin.natAdd`): no new edges are added, so
the fresh vertices are genuinely isolated and the old vertices keep exactly their old
multiplicities. -/
def addFreshIsolated (G : LabelledPattern ℓ r) (m m' : ℕ) : LabelledPattern (ℓ + m) (r + m') where
  F := { A := G.F.A ⊕ Fin m
         B := G.F.B ⊕ Fin m'
         mult := fun x y => Sum.elim (fun x0 => Sum.elim (G.F.mult x0) (fun _ => 0))
           (fun _ => fun _ => 0) x y }
  a := Fin.addCases (fun i => Sum.inl (G.a i)) (fun i => Sum.inr i)
  b := Fin.addCases (fun j => Sum.inl (G.b j)) (fun j => Sum.inr j)

variable (G : LabelledPattern ℓ r) {m m' : ℕ}

/-- The natural embedding of `G`'s vertices into `addFreshIsolated G m m'`. -/
def embAdd (G : LabelledPattern ℓ r) (m m' : ℕ) :
    G.F.A ⊕ G.F.B → (addFreshIsolated G m m').F.A ⊕ (addFreshIsolated G m m').F.B :=
  Sum.map Sum.inl Sum.inl

/-! ### Item 4: deleting labels -/

variable {ℓ' r' : ℕ}

/-- Restricting the labels of `G` to fewer positions, via embeddings picking out which
positions survive. -/
def restrict (G : LabelledPattern ℓ r) (ι : Fin ℓ' ↪ Fin ℓ) (j : Fin r' ↪ Fin r) :
    LabelledPattern ℓ' r' :=
  ⟨G.F, G.a ∘ ι, G.b ∘ j⟩

theorem restrict_labelVertex_apply (G : LabelledPattern ℓ r) (ι : Fin ℓ' ↪ Fin ℓ)
    (j : Fin r' ↪ Fin r) (p : Fin ℓ' ⊕ Fin r') :
    (restrict G ι j).labelVertex p = G.labelVertex (Sum.map ι j p) := by
  cases p <;> rfl

/-- Restricting labels can only shrink the label support. -/
theorem labelSupport_restrict_subset (G : LabelledPattern ℓ r) (ι : Fin ℓ' ↪ Fin ℓ)
    (j : Fin r' ↪ Fin r) : (restrict G ι j).labelSupport ⊆ G.labelSupport := by
  intro v hv
  obtain ⟨hv1, hv2⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hv1
  rw [restrict_labelVertex_apply] at hp
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨Sum.map ι j p, Finset.mem_univ _, hp⟩, hv2⟩

variable {G : LabelledPattern ℓ r} {Δ k : ℕ}

/-- The node type for item 4: a fresh root, above all the nodes of the old decomposition. -/
abbrev DelNode (D : RootExactDecomposition G Δ k) := Unit ⊕ D.Node

/-- The parent map for item 4: the fresh root is its own parent, and the old root's parent
becomes the fresh root (every other old node keeps its old parent). -/
noncomputable def delParent (D : RootExactDecomposition G Δ k) : DelNode D → DelNode D :=
  Sum.elim (fun _ => Sum.inl ())
    (fun t => if t = D.root then Sum.inl () else Sum.inr (D.parent t))

@[simp] theorem delParent_inl (D : RootExactDecomposition G Δ k) (u : Unit) :
    delParent D (Sum.inl u) = Sum.inl () := rfl

theorem delParent_inr_root (D : RootExactDecomposition G Δ k) :
    delParent D (Sum.inr D.root) = Sum.inl () := by simp [delParent]

theorem delParent_inr_of_ne (D : RootExactDecomposition G Δ k) {t : D.Node} (h : t ≠ D.root) :
    delParent D (Sum.inr t) = Sum.inr (D.parent t) := by simp [delParent, h]

theorem delParent_iterate_inl (D : RootExactDecomposition G Δ k) :
    ∀ m, (delParent D)^[m] (Sum.inl ()) = Sum.inl () := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, delParent_inl]

theorem delParent_iterate_of_parent_eq_root (D : RootExactDecomposition G Δ k) :
    ∀ (m : ℕ) (t : D.Node), D.parent^[m] t = D.root →
      (delParent D)^[m + 1] (Sum.inr t) = Sum.inl () := by
  intro m
  induction m with
  | zero =>
    intro t ht
    rw [Function.iterate_zero_apply] at ht
    subst ht
    exact delParent_inr_root D
  | succ m ih =>
    intro t ht
    rw [Function.iterate_succ_apply]
    by_cases h : t = D.root
    · subst h; rw [delParent_inr_root]; exact delParent_iterate_inl D m
    · rw [delParent_inr_of_ne D h]
      have : D.parent^[m] (D.parent t) = D.root := by
        rwa [Function.iterate_succ_apply] at ht
      exact ih (D.parent t) this

/-- **Item 4.** Deleting labels (restricting to fewer positions) increases the depth bound by
exactly `1`: attach a fresh root above the old one, with bag equal to the label support of the
restricted graph (a subset of the old root bag, of the same size bound). -/
theorem inClass_restrict {G : LabelledPattern ℓ r} {Δ k : ℕ} (h : InClass Δ k G)
    (ι : Fin ℓ' ↪ Fin ℓ) (j : Fin r' ↪ Fin r) : InClass (Δ + 1) k (restrict G ι j) := by
  obtain ⟨D⟩ := h
  have hsub : (restrict G ι j).labelSupport ⊆ G.labelSupport := labelSupport_restrict_subset G ι j
  set delBag : DelNode D → Finset (G.F.A ⊕ G.F.B) :=
    Sum.elim (fun _ => (restrict G ι j).labelSupport) (fun t => D.bag t) with hdelBag
  have delBag_inl : ∀ u : Unit, delBag (Sum.inl u) = (restrict G ι j).labelSupport := fun _ => rfl
  have delBag_inr : ∀ t : D.Node, delBag (Sum.inr t) = D.bag t := fun _ => rfl
  refine ⟨{ Node := DelNode D
            root := Sum.inl ()
            parent := delParent D
            parent_root := rfl
            depth_le := fun t => by
              match t with
              | Sum.inl () => exact delParent_iterate_inl D (Δ + 1)
              | Sum.inr t => exact delParent_iterate_of_parent_eq_root D Δ t (D.depth_le t)
            bag := delBag
            bag_root := rfl
            card_bag_le := fun t => by
              match t with
              | Sum.inl () =>
                show (restrict G ι j).labelSupport.card ≤ k
                exact (Finset.card_le_card hsub).trans
                  (by rw [← D.bag_root]; exact D.card_bag_le D.root)
              | Sum.inr t => exact D.card_bag_le t
            exists_mem_bag := fun v hv => by
              obtain ⟨t, ht⟩ := D.exists_mem_bag v hv
              exact ⟨Sum.inr t, ht⟩
            exists_edge_mem_bag := fun x y hxy => by
              obtain ⟨t, htx, hty⟩ := D.exists_edge_mem_bag x y hxy
              exact ⟨Sum.inr t, htx, hty⟩
            connected := fun v t1 t2 ht1 hd1 ht2 hd2 => by
              -- `hd : Sum.inr t' = Sum.inl () ∨ ⋯` always forces the right disjunct, since the
              -- two `Sum` tags never agree.
              have simp_disj : ∀ t' : D.Node,
                  (Sum.inr t' = (Sum.inl () : DelNode D) ∨
                    v ∉ delBag (delParent D (Sum.inr t'))) →
                  v ∉ delBag (delParent D (Sum.inr t')) :=
                fun t' h => h.resolve_left (by simp)
              match t1, t2 with
              | Sum.inl (), Sum.inl () => rfl
              | Sum.inl (), Sum.inr t2' =>
                exfalso
                rw [delBag_inl] at ht1
                have hd2 := simp_disj t2' hd2
                by_cases hroot : t2' = D.root
                · subst hroot
                  rw [delParent_inr_root, delBag_inl] at hd2
                  exact hd2 ht1
                · rw [delParent_inr_of_ne D hroot, delBag_inr] at hd2
                  have hmem2 : v ∈ D.bag t2' := by rw [← delBag_inr]; exact ht2
                  have hroot' : D.root = t2' :=
                    D.connected v D.root t2' (by rw [D.bag_root]; exact hsub ht1) (Or.inl rfl)
                      hmem2 (Or.inr hd2)
                  exact hroot hroot'.symm
              | Sum.inr t1', Sum.inl () =>
                exfalso
                rw [delBag_inl] at ht2
                have hd1 := simp_disj t1' hd1
                by_cases hroot : t1' = D.root
                · subst hroot
                  rw [delParent_inr_root, delBag_inl] at hd1
                  exact hd1 ht2
                · rw [delParent_inr_of_ne D hroot, delBag_inr] at hd1
                  have hmem1 : v ∈ D.bag t1' := by rw [← delBag_inr]; exact ht1
                  have hroot' : t1' = D.root :=
                    D.connected v t1' D.root hmem1 (Or.inr hd1)
                      (by rw [D.bag_root]; exact hsub ht2) (Or.inl rfl)
                  exact hroot hroot'
              | Sum.inr t1', Sum.inr t2' =>
                rw [delBag_inr] at ht1 ht2
                have hd1 := simp_disj t1' hd1
                have hd2 := simp_disj t2' hd2
                have hd1' : t1' = D.root ∨ v ∉ D.bag (D.parent t1') := by
                  by_cases hroot : t1' = D.root
                  · exact Or.inl hroot
                  · exact Or.inr (by rwa [delParent_inr_of_ne D hroot, delBag_inr] at hd1)
                have hd2' : t2' = D.root ∨ v ∉ D.bag (D.parent t2') := by
                  by_cases hroot : t2' = D.root
                  · exact Or.inl hroot
                  · exact Or.inr (by rwa [delParent_inr_of_ne D hroot, delBag_inr] at hd2)
                congr 1
                exact D.connected v t1' t2' ht1 hd1' ht2 hd2' }⟩

/-! ### The base case for the concluding part: `J_n ≡ 1` -/

/-- `J`: the edgeless `(ℓ,r)`-labelled graph with labels on `ℓ + r` pairwise-distinct vertices,
one per position. By item 1 (`inClassP_of_edgeless`), `J ∈ 𝒯^{0,k}_P(ℓ,r)` for every `k, P`. -/
def J (ℓ r : ℕ) : LabelledPattern ℓ r where
  F := { A := Fin ℓ, B := Fin r, mult := fun _ _ => 0 }
  a := id
  b := id

theorem J_isEdgeless (ℓ r : ℕ) : isEdgeless (J ℓ r).F := fun _ _ => rfl

/-- **`J_n ≡ 1`.** The homomorphism polynomial of `J` is the constant function `1`: this is the
generator witnessing `1 ∈ 𝔗^{Δ,k}_{n,P}(ℓ,r)` (for `ℓ + r ≤ k`, via item 1 applied to `J`) in
the concluding part of `lem:labelled-ops`. -/
theorem labelledHom_J (K : Type*) [CommSemiring K] (n : ℕ) (v : Fin ℓ → Fin n)
    (w : Fin r → Fin n) : labelledHom K (J ℓ r) n v w = 1 := by
  have hcond : ∀ hA : Fin ℓ → Fin n, ∀ hB : Fin r → Fin n,
      ((∀ i, hA (id i) = v i) ∧ ∀ j, hB (id j) = w j) ↔ (hA = v ∧ hB = w) := by
    intro hA hB
    simp only [id_eq, funext_iff]
  show (∑ hA : Fin ℓ → Fin n, ∑ hB : Fin r → Fin n,
      if (∀ i, hA (id i) = v i) ∧ (∀ j, hB (id j) = w j) then
        (∏ x, ∏ y, MvPolynomial.X (hA x, hB y) ^ (0 : ℕ) : MvPolynomial (Fin n × Fin n) K)
      else 0) = 1
  simp only [hcond, pow_zero, Finset.prod_const_one]
  rw [Finset.sum_eq_single v]
  · rw [Finset.sum_eq_single w]
    · simp
    · intro hB _ hne; exact if_neg (fun h => hne h.2)
    · intro h; exact absurd (Finset.mem_univ w) h
  · intro hA _ hne
    apply Finset.sum_eq_zero
    intro hB _
    exact if_neg (fun h => hne h.1)
  · intro h; exact absurd (Finset.mem_univ v) h

/-- $\mathfrak T^{\Delta,k}_{n,P}(\ell,r)$: the `K`-linear span of the homomorphism polynomials
of labelled graphs in `𝒯^{Δ,k}_P(ℓ,r)`. -/
noncomputable def span𝔗P (K : Type*) [Field K] (Δ k n : ℕ) (P : Finset (Fin ℓ ⊕ Fin r)) :
    Submodule K ((Fin ℓ → Fin n) → (Fin r → Fin n) → MvPolynomial (Fin n × Fin n) K) :=
  Submodule.span K {f | ∃ G : LabelledPattern ℓ r, InClassP Δ k P G ∧ f = labelledHom K G n}

/-- **Part of the concluding fact of `lem:labelled-ops`: `1 ∈ 𝔗^{Δ,k}_{n,P}(ℓ,r)`**, via item 1
applied to `J` (no hypothesis on `ℓ + r` vs `k`, nor on `P`, is needed, matching
`inClassP_of_edgeless`). -/
theorem one_mem_span𝔗P (K : Type*) [Field K] (Δ k n : ℕ) (P : Finset (Fin ℓ ⊕ Fin r)) :
    (fun (_ : Fin ℓ → Fin n) (_ : Fin r → Fin n) => (1 : MvPolynomial (Fin n × Fin n) K)) ∈
      span𝔗P K Δ k n P := by
  apply Submodule.subset_span
  exact ⟨J ℓ r, inClassP_of_edgeless' (J_isEdgeless ℓ r) Δ k P,
    funext fun v => funext fun w => (labelledHom_J K n v w).symm⟩

end Lax461425Proofs.PatternsLabelledOps
