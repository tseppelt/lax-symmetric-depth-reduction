import Lax461425Proofs.RigidComputes

/-!
Helper material for the rigidification proof: the reduced circuit `C'` has size at most that
of `C`.
-/

namespace Lax461425Proofs.RigidSize

open Lax461425.Circuits RigidHeight RigidEquiv RigidWeight RigidRep RigidConstruction
  RigidComputes

open scoped Classical

variable {V K : Type*} (C : Circuit V K)

/-- A sum over a subtype is at most the sum over the whole (finite) type, for nonnegative
natural-number-valued summands. -/
theorem sum_subtype_le {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] (g : α → ℕ) :
    ∑ a : {x // p x}, g a.1 ≤ ∑ a, g a := by
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp) g]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => Nat.zero_le _)

/-- The total aggregated weight that `a` sends into all classes equals the total weight `a`
sends to all gates of `C`: every gate belongs to exactly one class, and that class's
representative is always live. -/
theorem sum_W_eq_sum_wire (a : C.Gate) :
    ∑ b : (reduced C).Gate, W C a b.1 = ∑ h : C.Gate, C.wire a h := by
  unfold W
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  have hcond : ∀ b : (reduced C).Gate, (Equiv C h b.1) = (b = toC' C h) := fun b =>
    propext (toC'_eq_iff).symm
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ (Finset.univ : Finset (reduced C).Gate)) =>
    by rw [hcond b])]
  exact Fintype.sum_ite_eq' (toC' C h) (fun _ => C.wire a h)

/-- The reduced circuit has size at most that of the original circuit. -/
theorem size_reduced_le : (reduced C).size ≤ C.size := by
  show Fintype.card (reduced C).Gate + ∑ a : (reduced C).Gate, ∑ b : (reduced C).Gate,
      (reduced C).wire a b ≤ Fintype.card C.Gate + ∑ a : C.Gate, ∑ h : C.Gate, C.wire a h
  have hcard : Fintype.card (reduced C).Gate ≤ Fintype.card C.Gate :=
    Fintype.card_subtype_le _
  have hwires : ∑ a : (reduced C).Gate, ∑ b : (reduced C).Gate, (reduced C).wire a b ≤
      ∑ a : C.Gate, ∑ h : C.Gate, C.wire a h := by
    calc ∑ a : (reduced C).Gate, ∑ b : (reduced C).Gate, (reduced C).wire a b
        = ∑ a : (reduced C).Gate, ∑ h : C.Gate, C.wire a.1 h := by
          apply Finset.sum_congr rfl
          intro a _
          calc ∑ b : (reduced C).Gate, (reduced C).wire a b
              = ∑ b : (reduced C).Gate, W C a.1 b.1 := by
                apply Finset.sum_congr rfl; intro b _; exact reduced_wire C a b
            _ = ∑ h : C.Gate, C.wire a.1 h := sum_W_eq_sum_wire C a.1
      _ ≤ ∑ a : C.Gate, ∑ h : C.Gate, C.wire a h :=
        sum_subtype_le (IsLive C) (fun a => ∑ h, C.wire a h)
  omega

end Lax461425Proofs.RigidSize
