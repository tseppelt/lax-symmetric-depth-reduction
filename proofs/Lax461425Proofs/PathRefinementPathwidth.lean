import Lax461425Proofs.PathRefinementDecomposition
import Lax461425Proofs.SymmetricPathDecomposition

/-!
The linear certificate implies the actual pathwidth predicate used in Section 6. Isolated
vertices are handled by singleton bags after the non-isolated part. Empty endpoint bags
are added explicitly; this argument uses no padding or homomorphism-spanning assumption.
-/

namespace Lax461425Proofs.PathRefinementPathwidth

open Lax461425.SymmetricABPs PatternsLabelledBasic PathRefinementSchedule
open Lax461425.PatternWidths
open PathRefinementDecomposition
open scoped Classical

noncomputable section

variable {ℓ r depth width : ℕ} {G : LabelledPattern ℓ r}
variable (D : RootExactDecomposition G depth width) (S : Schedule D.parent D.root)

abbrev Iso := {v : G.F.A ⊕ G.F.B // isIsolated G.F v}

def pathBag (i : Fin (S.length + Fintype.card (Iso (G := G)) + 3)) : Finset (G.F.A ⊕ G.F.B) :=
  if h : 0 < i.val ∧ i.val ≤ S.length + 1 then
    composedBag D S ⟨i.val - 1, by omega⟩ \ isolatedSet G.F
  else if h' : S.length + 2 ≤ i.val ∧ i.val ≤ S.length + 1 + Fintype.card (Iso (G := G)) then
    {((Fintype.equivFin (Iso (G := G))).symm ⟨i.val - (S.length + 2), by omega⟩).val}
  else ∅

theorem pathBag_noniso {v : G.F.A ⊕ G.F.B} (hv : ¬ isIsolated G.F v)
    (i : Fin (S.length + Fintype.card (Iso (G := G)) + 3)) :
    v ∈ pathBag D S i ↔
      if h : 0 < i.val ∧ i.val ≤ S.length + 1 then
        v ∈ composedBag D S ⟨i.val - 1, by omega⟩ else False := by
  unfold pathBag
  split_ifs
  · simp [Finset.mem_sdiff, mem_isolatedSet, hv]
  · simp only [Finset.mem_singleton]
    constructor
    · intro he
      exact hv (he ▸ ((Fintype.equivFin (Iso (G := G))).symm _).property)
    · exact False.elim
  · simp

theorem pathBag_iso {v : G.F.A ⊕ G.F.B} (hv : isIsolated G.F v)
    (i : Fin (S.length + Fintype.card (Iso (G := G)) + 3)) :
    v ∈ pathBag D S i ↔
      i.val = S.length + 2 + (Fintype.equivFin (Iso (G := G)) ⟨v, hv⟩).val := by
  unfold pathBag
  split_ifs with h h'
  · simp only [Finset.mem_sdiff, mem_isolatedSet, hv, not_true_eq_false, and_false]
    constructor
    · exact False.elim
    · intro he; omega
  · simp only [Finset.mem_singleton]
    constructor
    · intro he
      have he' : (⟨v, hv⟩ : Iso (G := G)) = (Fintype.equivFin (Iso (G := G))).symm
          ⟨i.val - (S.length + 2), by omega⟩ := Subtype.ext he
      have hh := congrArg (fun t => (Fintype.equivFin (Iso (G := G)) t).val) he'
      simp only [Equiv.apply_symm_apply] at hh
      omega
    · intro he
      have ht : (⟨v, hv⟩ : Iso (G := G)) = (Fintype.equivFin (Iso (G := G))).symm
          ⟨i.val - (S.length + 2), by omega⟩ := by
        apply (Fintype.equivFin (Iso (G := G))).injective
        simp only [Equiv.apply_symm_apply]
        apply Fin.ext
        change (Fintype.equivFin (Iso (G := G)) ⟨v, hv⟩).val = i.val - (S.length + 2)
        omega
      exact congrArg Subtype.val ht
  · simp only [Finset.notMem_empty]
    constructor
    · exact False.elim
    · intro he
      have hi := (Fintype.equivFin (Iso (G := G)) ⟨v, hv⟩).isLt
      omega

/-- A node schedule of width one doubles the decomposition's bag bound. -/
def pathDecomposition : PaddedPathDecomposition G.F (2 * width) where
  length := S.length + Fintype.card (Iso (G := G)) + 2
  bag := pathBag D S
  bag_first := by simp [pathBag]
  bag_last := by simp [pathBag]; omega
  card_bag_le i := by
    unfold pathBag
    split_ifs
    · exact (Finset.card_le_card Finset.sdiff_subset).trans
        ((composedBag_card D S _).trans (by omega))
    · simp
    · simp
  covers_vertex v := by
    by_cases hv : isIsolated G.F v
    · let j := Fintype.equivFin (Iso (G := G)) ⟨v, hv⟩
      refine ⟨⟨S.length + 2 + j.val, by have hj := j.isLt; omega⟩, ?_⟩
      exact (pathBag_iso D S hv _).mpr rfl
    · obtain ⟨i, hi⟩ := composedBag_cover D S v hv
      let j : Fin (S.length + Fintype.card (Iso (G := G)) + 3) :=
        ⟨i.val + 1, by have hi' := i.isLt; omega⟩
      have hj : 0 < j.val ∧ j.val ≤ S.length + 1 := by
        have hi' := i.isLt
        dsimp [j]
        omega
      refine ⟨j, ?_⟩
      rw [pathBag_noniso D S hv, dif_pos hj]
      simpa [j] using hi
  covers_edge a b hab := by
    obtain ⟨i, ha, hb⟩ := composedBag_edge D S a b hab
    let j : Fin (S.length + Fintype.card (Iso (G := G)) + 3) :=
      ⟨i.val + 1, by have hi := i.isLt; omega⟩
    have hj : 0 < j.val ∧ j.val ≤ S.length + 1 := by
      have hi := i.isLt
      dsimp [j]
      omega
    refine ⟨j, ?_, ?_⟩
    · have hn : ¬ isIsolated G.F (Sum.inl a) := fun hz => hab (hz b)
      rw [pathBag_noniso D S hn, dif_pos hj]
      simpa [j] using ha
    · have hn : ¬ isIsolated G.F (Sum.inr b) := fun hz => hab (hz a)
      rw [pathBag_noniso D S hn, dif_pos hj]
      simpa [j] using hb
  interval v i j l hij hjl hi hl := by
    have h₁ := hij; have h₂ := hjl
    change i.val ≤ j.val at h₁
    change j.val ≤ l.val at h₂
    by_cases hv : isIsolated G.F v
    · rw [pathBag_iso D S hv] at hi hl ⊢
      omega
    · rw [pathBag_noniso D S hv] at hi hl ⊢
      have hi' : 0 < i.val ∧ i.val ≤ S.length + 1 := by
        by_contra hh; rw [dif_neg hh] at hi; exact hi
      have hl' : 0 < l.val ∧ l.val ≤ S.length + 1 := by
        by_contra hh; rw [dif_neg hh] at hl; exact hl
      have hj' : 0 < j.val ∧ j.val ≤ S.length + 1 := by omega
      rw [dif_pos hi'] at hi
      rw [dif_pos hl'] at hl
      rw [dif_pos hj']
      exact composedBag_interval D S v _ _ _
        (by change i.val - 1 ≤ j.val - 1; omega)
        (by change j.val - 1 ≤ l.val - 1; omega) hi hl

include D S in
theorem pathwidthLE : PathwidthLE (2 * width) G.F :=
  SymmetricPathDecomposition.pathwidthLE_iff.2 ⟨pathDecomposition D S⟩

end

end Lax461425Proofs.PathRefinementPathwidth
