import Lax461425.SymmetricABPs
import Lax461425.PatternWidths
import Mathlib.Tactic

/-!
Elementary facts about path decompositions of patterns, as used in Section 6. The
constructions work with padded decompositions, whose first and last bags are empty; these
exist exactly when the underlying simple graph has a path decomposition of the same width.
The one-full-bag decomposition supplies the finite-exception bound in the family proof.
-/

namespace Lax461425Proofs

open Lax461425.SymmetricABPs Lax461425.HomomorphismPolynomials
open Lax461425.PatternWidths

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A finite path decomposition with empty endpoint bags and width at most `k`.
The interval condition is the connectedness condition for occurrences of each vertex. -/
structure PaddedPathDecomposition (F : Pattern) (k : ℕ) where
  length : ℕ
  bag : Fin (length + 1) → Finset (F.A ⊕ F.B)
  bag_first : bag 0 = ∅
  bag_last : bag (Fin.last length) = ∅
  card_bag_le : ∀ i, (bag i).card ≤ k + 1
  covers_vertex : ∀ v, ∃ i, v ∈ bag i
  covers_edge : ∀ a b, F.mult a b ≠ 0 → ∃ i, Sum.inl a ∈ bag i ∧ Sum.inr b ∈ bag i
  interval : ∀ v i j l, i ≤ j → j ≤ l → v ∈ bag i → v ∈ bag l → v ∈ bag j

namespace SymmetricPathDecomposition

/-- Empty endpoint bags do not change pathwidth. -/
theorem pathwidthLE_iff {F : Pattern} {k : ℕ} :
    PathwidthLE k F ↔ Nonempty (PaddedPathDecomposition F k) := by
  constructor
  · rintro ⟨D, hD⟩
    let bag : Fin (D.length + 1 + 1) → Finset (F.A ⊕ F.B) := fun i =>
      if h : 0 < i.val ∧ i.val ≤ D.length then D.bag ⟨i.val - 1, by omega⟩ else ∅
    have mem_bag : ∀ v i, v ∈ bag i →
        ∃ h : 0 < i.val ∧ i.val ≤ D.length, v ∈ D.bag ⟨i.val - 1, by omega⟩ := by
      intro v i hv
      by_cases h : 0 < i.val ∧ i.val ≤ D.length
      · exact ⟨h, by rwa [show bag i = _ from dif_pos h] at hv⟩
      · rw [show bag i = ∅ from dif_neg h] at hv
        simp at hv
    have bag_succ : ∀ j : Fin D.length, bag ⟨j.val + 1, by omega⟩ = D.bag j := by
      intro j
      exact dif_pos ⟨by simp, by simpa using j.isLt⟩
    refine ⟨{
      length := D.length + 1
      bag := bag
      bag_first := by simp [bag]
      bag_last := by simp [bag]
      card_bag_le := ?_
      covers_vertex := ?_
      covers_edge := ?_
      interval := ?_ }⟩
    · intro i
      unfold bag
      split_ifs
      · exact hD _
      · simp
    · intro v
      obtain ⟨j, hj⟩ := D.vertex_mem_bag v
      exact ⟨⟨j.val + 1, by omega⟩, by rwa [bag_succ]⟩
    · intro a b hab
      obtain ⟨j, hj⟩ := D.edge_mem_bag (u := Sum.inl a) (v := Sum.inr b)
        (by simp [underlying, SimpleGraph.fromRel_adj, hab])
      exact ⟨⟨j.val + 1, by omega⟩, by rw [bag_succ]; exact hj⟩
    · intro v i j l hij hjl hvi hvl
      obtain ⟨hi, hvi⟩ := mem_bag v i hvi
      obtain ⟨hl, hvl⟩ := mem_bag v l hvl
      have hj : 0 < j.val ∧ j.val ≤ D.length := by
        change i.val ≤ j.val at hij; change j.val ≤ l.val at hjl; omega
      simp only [bag, dif_pos hj]
      exact D.bag_indices_interval v _ _ _ ⟨by change i.val - 1 ≤ j.val - 1; omega,
        by change j.val - 1 ≤ l.val - 1; omega, hvi, hvl⟩
  · rintro ⟨D⟩
    refine ⟨{
      length := D.length + 1
      bag := D.bag
      vertex_mem_bag := D.covers_vertex
      edge_mem_bag := ?_
      bag_indices_interval := fun v i j l h => D.interval v i j l h.1 h.2.1 h.2.2.1 h.2.2.2 },
      D.card_bag_le⟩
    intro u v huv
    simp only [underlying, SimpleGraph.fromRel_adj] at huv
    rcases huv.2 with ⟨a, b, rfl, rfl, hab⟩ | ⟨a, b, rfl, rfl, hab⟩
    · exact D.covers_edge a b hab
    · obtain ⟨i, hi⟩ := D.covers_edge a b hab
      exact ⟨i, hi.2, hi.1⟩

theorem pathwidthLE_mono {F : Pattern} {k l : ℕ} (hkl : k ≤ l)
    (hF : PathwidthLE k F) : PathwidthLE l F := by
  obtain ⟨D⟩ := pathwidthLE_iff.1 hF
  exact pathwidthLE_iff.2
    ⟨{ D with card_bag_le := fun i => (D.card_bag_le i).trans (by omega) }⟩

/-- The decomposition with a single full bag between two empty bags. -/
noncomputable def fullBag (F : Pattern) :
    PaddedPathDecomposition F (Fintype.card F.A + Fintype.card F.B) := by
  classical
  refine {
    length := 2
    bag := fun i => if i.val = 1 then Finset.univ else ∅
    bag_first := by simp
    bag_last := by simp
    card_bag_le := ?_
    covers_vertex := ?_
    covers_edge := ?_
    interval := ?_ }
  · intro i
    split_ifs <;> simp [Fintype.card_sum]
  · intro v
    exact ⟨⟨1, by omega⟩, by simp⟩
  · intro a b hab
    exact ⟨⟨1, by omega⟩, by simp, by simp⟩
  · intro v i j l hij hjl hvi hvl
    have hi : i.val = 1 := by by_contra h; simpa [h] using hvi
    have hl : l.val = 1 := by by_contra h; simpa [h] using hvl
    have hj : j.val = 1 := by change i.val ≤ j.val at hij; change j.val ≤ l.val at hjl; omega
    simp [hj]

theorem pathwidthLE_card (F : Pattern) :
    PathwidthLE (Fintype.card F.A + Fintype.card F.B) F := pathwidthLE_iff.2 ⟨fullBag F⟩

theorem pathwidthLE_two_mul {F : Pattern} {n : ℕ}
    (hA : Fintype.card F.A ≤ n) (hB : Fintype.card F.B ≤ n) : PathwidthLE (2 * n) F :=
  pathwidthLE_mono (by omega) (pathwidthLE_card F)

end SymmetricPathDecomposition

end Lax461425Proofs
