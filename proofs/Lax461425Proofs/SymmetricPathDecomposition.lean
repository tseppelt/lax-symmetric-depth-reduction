import Lax461425.SymmetricABPs
import Mathlib.Tactic

/-!
Elementary facts about the actual path-decomposition definition used in Section 6.
The one-full-bag decomposition supplies the finite-exception bound in the family proof.
-/

namespace Lax461425Proofs.SymmetricPathDecomposition

open Lax461425.SymmetricABPs Lax461425.HomomorphismPolynomials

theorem pathwidthLE_mono {F : Pattern} {k l : ℕ} (hkl : k ≤ l)
    (hF : PathwidthLE k F) : PathwidthLE l F := by
  obtain ⟨D⟩ := hF
  exact ⟨{ D with card_bag_le := fun i => (D.card_bag_le i).trans (by omega) }⟩

/-- The decomposition with a single full bag between two empty bags. -/
noncomputable def fullBag (F : Pattern) :
    PathDecomposition F (Fintype.card F.A + Fintype.card F.B) := by
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
    PathwidthLE (Fintype.card F.A + Fintype.card F.B) F := ⟨fullBag F⟩

theorem pathwidthLE_two_mul {F : Pattern} {n : ℕ}
    (hA : Fintype.card F.A ≤ n) (hB : Fintype.card F.B ≤ n) : PathwidthLE (2 * n) F :=
  pathwidthLE_mono (by omega) (pathwidthLE_card F)

end Lax461425Proofs.SymmetricPathDecomposition
