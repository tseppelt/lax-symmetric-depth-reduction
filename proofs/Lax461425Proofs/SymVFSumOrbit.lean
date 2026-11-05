import Lax461425Proofs.TreeFormulaOrbit
import Lax461425Proofs.ComputedFormulaOrbit
import Lax461425Proofs.PatternsSupportAction
import Mathlib.Data.Set.Card.Arithmetic

/-!
Orbit bounds for an unbounded operation whose child occurrences may be permuted by the
automorphisms. Every automorphism maps a child occurrence onto some child occurrence, so a
gate orbit meets each child occurrence in at most one translate of an orbit of the child.
-/

namespace Lax461425Proofs.SymVFSumOrbit

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.SymmetricVNP
open TreeFormulaCircuit TreeFormulaOperations TreeFormulaOrbit
open scoped Classical

variable {V K : Type*} {A : Type*} [Group A] (ρ : A →* Equiv.Perm V)

theorem extends_symm {C : Circuit V K} {σ : C.Gate ≃ C.Gate} {γ : A}
    (h : Extends C σ (ρ γ)) : Extends C σ.symm (ρ γ⁻¹) := by
  refine ⟨fun g => ?_, fun g g' => ?_⟩
  · have hl := h.1 (σ.symm g)
    rw [Equiv.apply_symm_apply] at hl
    rw [hl, PatternsSupportAction.label_map_map]
    have hid : (⇑(ρ γ⁻¹) ∘ ⇑(ρ γ)) = id := by
      funext x
      simp [map_inv]
    rw [hid, PatternsSupportAction.label_map_id]
  · have hw := h.2 (σ.symm g) (σ.symm g')
    simpa using hw.symm

theorem extends_mul {C : Circuit V K} {σ₁ σ₂ : C.Gate ≃ C.Gate} {γ₁ γ₂ : A}
    (h₁ : Extends C σ₁ (ρ γ₁)) (h₂ : Extends C σ₂ (ρ γ₂)) :
    Extends C (σ₁.trans σ₂) (ρ (γ₂ * γ₁)) := by
  have h := PatternsSupportAction.extends_comp h₂ h₁
  have he : (⇑(ρ γ₂) ∘ ⇑(ρ γ₁)) = ⇑(ρ (γ₂ * γ₁)) := by
    funext x
    simp
  rw [he] at h
  exact h

variable [CommSemiring K] {I : Type} [Fintype I] (T : I → Tree V K) (mul : Bool)

/-- Every extending automorphism maps a child root to a child root. -/
theorem maps_child_root {σ : (join T mul).Gate ≃ (join T mul).Gate} {π : V → V}
    (hσ : Extends (circuit (join T mul)) σ π) (i : I) :
    ∃ j, σ (embed T mul i (T i).out) = embed T mul j (T j).out := by
  have hroot : σ (.inl ()) = .inl () := PatternsSupportBasic.extends_fixes_out hσ
  have hedge : 0 < (circuit (join T mul)).wire (.inl ())
      (embed T mul i (T i).out) := by
    simp [circuit, embed, joinParent, (T i).parent_out]
  have hedge' : 0 < (circuit (join T mul)).wire (.inl ())
      (σ (embed T mul i (T i).out)) := by
    rw [← hroot, hσ.2]
    exact hedge
  exact ComputedFormulaOrbit.join_child_cases T mul _ hedge'

/-- A gate orbit in a sum or product of permutable children. -/
theorem join_orbitSize_le_card_mul (B : ℕ) (hI : 1 ≤ Fintype.card I) (hB : 1 ≤ B)
    (hchild : ∀ i, orbitSize ρ (circuit (T i)) ≤ B) :
    orbitSize ρ (circuit (join T mul)) ≤ Fintype.card I * B := by
  apply Finset.sup_le
  intro g _
  cases g with
  | inl u =>
    cases u
    exact (orbit_root_le_one T mul ρ).trans (le_trans hB (Nat.le_mul_of_pos_left B hI))
  | inr p =>
    rcases p with ⟨i, g₀⟩
    let C := circuit (join T mul)
    let P : I → Prop := fun j => ∃ (γ : A) (σ : C.Gate ≃ C.Gate), Extends C σ (ρ γ) ∧
      σ (embed T mul i (T i).out) = embed T mul j (T j).out
    let Y : I → Set C.Gate := fun j =>
      if hj : P j then Set.image (⇑(Classical.choose (Classical.choose_spec hj) : C.Gate ≃ C.Gate))
        ((embed T mul i) '' orbit ρ (circuit (T i)) g₀) else ∅
    have hsub : orbit ρ C (embed T mul i g₀) ⊆ ⋃ j, Y j := by
      rintro w ⟨γ, σ, hσ, rfl⟩
      obtain ⟨j, hj⟩ := maps_child_root T mul hσ i
      have hP : P j := ⟨γ, σ, hσ, hj⟩
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      simp only [Y, dif_pos hP]
      let γj := Classical.choose hP
      let σj := Classical.choose (Classical.choose_spec hP)
      have hσj : Extends C σj (ρ γj) ∧ σj (embed T mul i (T i).out) = embed T mul j (T j).out :=
        Classical.choose_spec (Classical.choose_spec hP)
      -- `τ = σj⁻¹ ∘ σ` fixes the root of child `i`.
      let τ : C.Gate ≃ C.Gate := σ.trans σj.symm
      have hτ : Extends C τ (ρ (γj⁻¹ * γ)) := extends_mul ρ hσ (extends_symm ρ hσj.1)
      have hfix : τ (embed T mul i (T i).out) = embed T mul i (T i).out := by
        change σj.symm (σ (embed T mul i (T i).out)) = _
        rw [hj, ← hσj.2, Equiv.symm_apply_apply]
      let e := restrict T mul τ (ρ (γj⁻¹ * γ)) hτ i hfix
      refine ⟨embed T mul i (e g₀), ⟨e g₀, ⟨γj⁻¹ * γ, e,
        restrict_extends T mul τ (ρ (γj⁻¹ * γ)) hτ i hfix, rfl⟩, rfl⟩, ?_⟩
      have hspec := restrictMap_spec T mul τ (ρ (γj⁻¹ * γ)) hτ i hfix g₀
      change σj (embed T mul i (restrictMap T mul τ (ρ (γj⁻¹ * γ)) hτ i hfix g₀)) = σ _
      rw [← hspec]
      change σj (σj.symm (σ (embed T mul i g₀))) = _
      rw [Equiv.apply_symm_apply]
    have hY : ∀ j, (Y j).ncard ≤ B := by
      intro j
      by_cases hj : P j
      · simp only [Y, dif_pos hj]
        refine (Set.ncard_image_le).trans ((Set.ncard_image_le).trans ?_)
        exact (Finset.le_sup (f := fun h => (orbit ρ (circuit (T i)) h).ncard)
          (Finset.mem_univ g₀)).trans (hchild i)
      · simp only [Y, dif_neg hj, Set.ncard_empty]
        exact Nat.zero_le _
    calc (orbit ρ C (embed T mul i g₀)).ncard ≤ (⋃ j, Y j).ncard := Set.ncard_le_ncard hsub
      _ ≤ ∑ j, (Y j).ncard := Set.ncard_iUnion_le_of_fintype Y
      _ ≤ ∑ _j : I, B := Finset.sum_le_sum (fun j _ => hY j)
      _ = Fintype.card I * B := by simp

end Lax461425Proofs.SymVFSumOrbit
