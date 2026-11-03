import Lax461425Proofs.PathRefinementClass
import Lax461425Proofs.PatternsInductionReindex
import Lax461425Proofs.PatternsRestrictedDelete

/-!
Expose Tim's existing padding and label-deletion constructions as decomposition data,
and carry the extra linear certificate through them. The record proofs below are the
existing constructions, with their outer Nonempty wrapper removed; their semantics are
reused from the original labelledHom_padGraph and labelledHom_restrict_eq_sum lemmas.
-/

namespace Lax461425Proofs.PathRefinementOperations

open PatternsLabelledBasic PatternsLabelledOps PatternsInductionReindex
open PatternsRestrictedDelete PathRefinementClass PathRefinementDecomposition
open PathRefinementSchedule
open scoped Classical

noncomputable section

variable {ℓ r ℓ' r' ℓ₀ r₀ ℓ₁ r₁ Δ k : ℕ}

def padTree {G : LabelledPattern ℓ₀ r₀} (D : RootExactDecomposition G Δ k)
    (ι : Fin ℓ₀ ↪ Fin ℓ₁) (κ : Fin r₀ ↪ Fin r₁) :
    RootExactDecomposition (padGraph G ι κ) Δ k := by
  refine  { Node := D.Node
            root := D.root
            parent := D.parent
            parent_root := D.parent_root
            depth_le := D.depth_le
            bag := fun t => (D.bag t).image (embPad G ι κ)
            bag_root := by rw [D.bag_root, labelSupport_padGraph]
            card_bag_le := fun t => Finset.card_image_le.trans (D.card_bag_le t)
            exists_mem_bag := ?_
            exists_edge_mem_bag := ?_
            connected := ?_ }
  · rintro v hv
    rcases v with (x0 | i) | (y0 | j)
    · obtain ⟨t, ht⟩ := D.exists_mem_bag (Sum.inl x0)
        (fun h => hv ((isIsolated_embPad_iff G ι κ).mpr h))
      exact ⟨t, Finset.mem_image.mpr ⟨Sum.inl x0, ht, rfl⟩⟩
    · exact absurd (isIsolated_fresh_inl G ι κ i) hv
    · obtain ⟨t, ht⟩ := D.exists_mem_bag (Sum.inr y0)
        (fun h => hv ((isIsolated_embPad_iff G ι κ).mpr h))
      exact ⟨t, Finset.mem_image.mpr ⟨Sum.inr y0, ht, rfl⟩⟩
    · exact absurd (isIsolated_fresh_inr G ι κ j) hv
  · rintro (x0 | i) (y0 | j) hxy
    · obtain ⟨t, htx, hty⟩ := D.exists_edge_mem_bag x0 y0 hxy
      exact ⟨t, Finset.mem_image.mpr ⟨Sum.inl x0, htx, rfl⟩,
        Finset.mem_image.mpr ⟨Sum.inr y0, hty, rfl⟩⟩
    · exact absurd rfl hxy
    · exact absurd rfl hxy
    · exact absurd rfl hxy
  · rintro v t1 t2 ht1 hd1 ht2 hd2
    rcases v with (x0 | i) | (y0 | j)
    · obtain ⟨w1, hw1mem, hw1eq⟩ := Finset.mem_image.mp ht1
      obtain ⟨w2, hw2mem, hw2eq⟩ := Finset.mem_image.mp ht2
      have hweq : w1 = w2 := embPad_injective G ι κ (hw1eq.trans hw2eq.symm)
      subst hweq
      refine D.connected w1 t1 t2 hw1mem ?_ hw2mem ?_
      · rcases hd1 with hd1 | hd1
        · exact Or.inl hd1
        · exact Or.inr (fun hc => hd1 (by rw [← hw1eq]; exact Finset.mem_image.mpr ⟨w1, hc, rfl⟩))
      · rcases hd2 with hd2 | hd2
        · exact Or.inl hd2
        · exact Or.inr (fun hc => hd2 (by rw [← hw2eq]; exact Finset.mem_image.mpr ⟨w1, hc, rfl⟩))
    · obtain ⟨w1, -, hw1eq⟩ := Finset.mem_image.mp ht1
      cases w1 with
      | inl x1 => exact absurd (Sum.inl_injective hw1eq) Sum.inl_ne_inr
      | inr y1 => exact absurd hw1eq.symm Sum.inl_ne_inr
    · obtain ⟨w1, hw1mem, hw1eq⟩ := Finset.mem_image.mp ht1
      obtain ⟨w2, hw2mem, hw2eq⟩ := Finset.mem_image.mp ht2
      have hweq : w1 = w2 := embPad_injective G ι κ (hw1eq.trans hw2eq.symm)
      subst hweq
      refine D.connected w1 t1 t2 hw1mem ?_ hw2mem ?_
      · rcases hd1 with hd1 | hd1
        · exact Or.inl hd1
        · exact Or.inr (fun hc => hd1 (by rw [← hw1eq]; exact Finset.mem_image.mpr ⟨w1, hc, rfl⟩))
      · rcases hd2 with hd2 | hd2
        · exact Or.inl hd2
        · exact Or.inr (fun hc => hd2 (by rw [← hw2eq]; exact Finset.mem_image.mpr ⟨w1, hc, rfl⟩))
    · obtain ⟨w1, -, hw1eq⟩ := Finset.mem_image.mp ht1
      cases w1 with
      | inl x1 => exact absurd hw1eq Sum.inl_ne_inr
      | inr y1 => exact absurd (Sum.inr_injective hw1eq) Sum.inl_ne_inr

def restrictTree {G : LabelledPattern ℓ r} (D : RootExactDecomposition G Δ k)
    (ι : Fin ℓ' ↪ Fin ℓ) (j : Fin r' ↪ Fin r) :
    RootExactDecomposition (restrict G ι j) (Δ + 1) k := by
  have hsub : (restrict G ι j).labelSupport ⊆ G.labelSupport := labelSupport_restrict_subset G ι j
  set delBag : DelNode D → Finset (G.F.A ⊕ G.F.B) :=
    Sum.elim (fun _ => (restrict G ι j).labelSupport) (fun t => D.bag t) with hdelBag
  have delBag_inl : ∀ u : Unit, delBag (Sum.inl u) = (restrict G ι j).labelSupport := fun _ => rfl
  have delBag_inr : ∀ t : D.Node, delBag (Sum.inr t) = D.bag t := fun _ => rfl
  refine  { Node := DelNode D
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
                exact D.connected v t1' t2' ht1 hd1' ht2 hd2' }

def padLinear {G : LabelledPattern ℓ₀ r₀} (D : LinearDecomposition G Δ k)
    (ι : Fin ℓ₀ ↪ Fin ℓ₁) (κ : Fin r₀ ↪ Fin r₁) :
    LinearDecomposition (padGraph G ι κ) Δ k where
  tree := padTree D.tree ι κ
  schedule := D.schedule

def restrictLinear {G : LabelledPattern ℓ r} (D : LinearDecomposition G Δ k)
    (ι : Fin ℓ' ↪ Fin ℓ) (j : Fin r' ↪ Fin r) :
    LinearDecomposition (restrict G ι j) (Δ + 1) k where
  tree := restrictTree D.tree ι j
  schedule := by
    change Schedule (delParent D.tree) (Sum.inl ())
    exact newRoot D.schedule

theorem pad_class {G : LabelledPattern ℓ₀ r₀} {P : Finset (Fin ℓ₀ ⊕ Fin r₀)}
    (h : InLinearClassP Δ k P G) (ι : Fin ℓ₀ ↪ Fin ℓ₁) (κ : Fin r₀ ↪ Fin r₁) :
    InLinearClassP Δ k (P.image (Sum.map (⇑ι) (⇑κ))) (padGraph G ι κ) := by
  obtain ⟨D⟩ := h.1
  exact ⟨⟨padLinear D ι κ⟩, (inClassP_padGraph (forget h) ι κ).2⟩

theorem restrict_class {G : LabelledPattern ℓ r} {P : Finset (Fin ℓ ⊕ Fin r)}
    (h : InLinearClassP Δ k P G) (ι : Fin ℓ' ↪ Fin ℓ) (j : Fin r' ↪ Fin r) :
    InLinearClassP (Δ + 1) k Finset.univ (restrict G ι j) := by
  obtain ⟨D⟩ := h.1
  let E := restrictLinear D ι j
  exact ⟨⟨E⟩, (inClassP_univ_of_inClass (show InClass (Δ + 1) k (restrict G ι j) from ⟨E.tree⟩)).2⟩

end

end Lax461425Proofs.PathRefinementOperations
