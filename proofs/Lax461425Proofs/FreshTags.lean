import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
Fresh constant tags used in Section 7. In an infinite field, a finite set of constants can
be avoided by a nonzero tag and its inverse, with the two constants distinct.
-/

namespace Lax461425Proofs.FreshTags

open scoped Classical

variable {K : Type*} [Field K] [Infinite K]

/-- A tag and its inverse can both be chosen fresh and distinct. -/
theorem exists_fresh_inverse_pair (s : Finset K) :
    ∃ t : K, t ≠ 0 ∧ t ∉ s ∧ t⁻¹ ∉ s ∧ t ≠ t⁻¹ := by
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset
    (s ∪ s.image Inv.inv ∪ {0, 1, -1})
  have hs : t ∉ s := fun h => ht (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hi : t ∉ s.image Inv.inv :=
    fun h => ht (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have ht0 : t ≠ 0 := by
    intro h; apply ht; simp [h]
  have ht1 : t ≠ 1 := by
    intro h; apply ht; simp [h]
  have htm1 : t ≠ -1 := by
    intro h; apply ht; simp [h]
  refine ⟨t, ht0, hs, ?_, ?_⟩
  · intro h
    exact hi (Finset.mem_image.mpr ⟨t⁻¹, h, inv_inv t⟩)
  · intro h
    rcases inv_eq_self₀.mp h.symm with h | h | h
    · exact htm1 h
    · exact ht0 h
    · exact ht1 h

/-- A finite set of pairwise distinct tags whose inverses are also distinct and do not
coincide with any tag; all chosen constants avoid the prescribed finite set. -/
theorem exists_fresh_tag_set (s : Finset K) (m : ℕ) :
    ∃ tags : Finset K, tags.card = m ∧
      (∀ t ∈ tags, t ≠ 0 ∧ t ∉ s ∧ t⁻¹ ∉ s) ∧
      Disjoint tags (tags.image Inv.inv) := by
  induction m with
  | zero => exact ⟨∅, rfl, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨tags, hcard, hgood, hdis⟩ := ih
    obtain ⟨t, ht0, ht, hti, hne⟩ :=
      exists_fresh_inverse_pair (s ∪ tags ∪ tags.image Inv.inv)
    have hts : t ∉ s := by intro h; exact ht (by simp [h])
    have htis : t⁻¹ ∉ s := by intro h; exact hti (by simp [h])
    have htt : t ∉ tags := by intro h; exact ht (by simp [h])
    have htit : t⁻¹ ∉ tags := by intro h; exact hti (by simp [h])
    have htim : t ∉ tags.image Inv.inv := by intro h; exact ht (by simp [h])
    refine ⟨insert t tags, by simp [htt, hcard], ?_, ?_⟩
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact ⟨ht0, hts, htis⟩
      · exact hgood a ha
    · rw [Finset.image_insert]
      apply Finset.disjoint_left.mpr
      intro a ha hb
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rcases Finset.mem_insert.mp hb with heq | hb
        · exact hne heq
        · exact htim hb
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · exact htit ha
        · exact Finset.disjoint_left.mp hdis ha hb

end Lax461425Proofs.FreshTags
