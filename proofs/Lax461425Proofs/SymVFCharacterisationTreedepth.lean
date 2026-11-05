import Lax461425.PatternWidths

/-!
Elementary treedepth facts for patterns: treedepth bounds are monotone, and a pattern has
treedepth at most its number of vertices, witnessed by a chain.
-/

namespace Lax461425Proofs.SymVFCharacterisationTreedepth

open Lax461425.HomomorphismPolynomials Lax461425.PatternWidths
open Lax183560.AncestorForest

/-- Treedepth bounds are monotone in the bound. -/
theorem treedepthLE_mono {t t' : ℕ} {F : Pattern} (h : TreedepthLE t F) (htt : t ≤ t') :
    TreedepthLE t' F := by
  obtain ⟨T, hadj, rank, hrank⟩ := h
  refine ⟨T, hadj, fun v => Fin.castLE htt (rank v), ?_⟩
  intro u v huv
  have := hrank huv
  simp only [Fin.lt_def, Fin.val_castLE] at this ⊢
  exact this

/-- A chain through all vertices witnesses treedepth at most the number of vertices. -/
theorem treedepthLE_card (F : Pattern) :
    TreedepthLE (Fintype.card F.A + Fintype.card F.B) F := by
  let e : F.A ⊕ F.B ≃ Fin (Fintype.card F.A + Fintype.card F.B) :=
    (Fintype.equivFin _).trans (finCongr (Fintype.card_sum))
  let T : AncestorForest (F.A ⊕ F.B) :=
    { ancestor := fun u v => e u < e v
      transitive := ⟨fun _ _ _ h₁ h₂ => lt_trans h₁ h₂⟩
      irreflexive := ⟨fun _ h => lt_irrefl _ h⟩
      ancestors_linearly_ordered := by
        intro u v w _
        rcases lt_trichotomy (e u) (e v) with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl (e.injective h)
        · exact Or.inr (Or.inr h) }
  refine ⟨T, ?_, e, fun _ _ h => h⟩
  intro u v huv
  have hne : u ≠ v := (underlying F).ne_of_adj huv
  rcases lt_or_gt_of_ne (fun h => hne (e.injective h)) with h | h
  · exact Or.inl h
  · exact Or.inr h

end Lax461425Proofs.SymVFCharacterisationTreedepth
