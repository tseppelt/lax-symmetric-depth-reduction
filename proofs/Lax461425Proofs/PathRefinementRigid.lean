import Lax461425Proofs.RigidConstruction
import Lax461425.CircuitProperties

/-! Rigidification preserves the total multiplicity of noninput children. -/
namespace Lax461425Proofs.PathRefinementRigid
open Lax461425.Circuits Lax461425.CircuitProperties
open RigidConstruction RigidWeight RigidEquiv RigidRep
open scoped Classical

theorem skew_reduced {V K : Type*} (C : Circuit V K) (hs : IsSkew C) :
    IsSkew (reduced C) := by
  intro a ha
  change C.label a.val = .mul at ha
  have he : (∑ b : (reduced C).Gate,
      if (C.label b.val).IsInput then 0 else W C a.val b.val) =
      ∑ x : C.Gate, if (C.label x).IsInput then 0 else C.wire a.val x := by
    calc
      _ = ∑ b : (reduced C).Gate, ∑ x : C.Gate,
          if Equiv C x b.val then
            (if (C.label x).IsInput then 0 else C.wire a.val x) else 0 := by
        apply Finset.sum_congr rfl
        intro b _
        by_cases hi : (C.label b.val).IsInput
        · rw [if_pos hi]
          symm
          apply Finset.sum_eq_zero
          intro x _
          by_cases hx : Equiv C x b.val
          · rw [if_pos hx, equiv_label_eq C hx, if_pos hi]
          · simp only [if_neg hx]
        · rw [if_neg hi]
          unfold W
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : Equiv C x b.val
          · simp only [if_pos hx, equiv_label_eq C hx, if_neg hi]
          · simp only [if_neg hx]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_eq_single (toC' C x)]
        · change (if Equiv C x (rep C x) then _ else 0) = _
          rw [if_pos (rep_equiv C x)]
        · intro b _ hb
          exact if_neg (fun he => hb (toC'_eq_of_equiv C he).symm)
        · simp
  change (∑ b : (reduced C).Gate,
    if (C.label b.val).IsInput then 0 else W C a.val b.val) ≤ 1
  rw [he]
  exact hs a.val ha

end Lax461425Proofs.PathRefinementRigid
