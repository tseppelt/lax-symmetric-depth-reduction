import Lax461425Proofs.RigidConstruction

/-!
Helper material for the rigidification proof: the reduced circuit `C'` has depth at most that
of `C`. Every path of `C'` lifts to a path of `C` of the same length, by replacing each step
(a positive aggregated weight between classes) with an actual witnessing wire.
-/

namespace Lax461425Proofs.RigidDepth

open Lax461425.Circuits RigidHeight RigidEquiv RigidWeight RigidRep RigidConstruction

open scoped Classical

variable {V K : Type*} (C : Circuit V K)

/-- Every prefix of a path of `C'` lifts to a path of `C` of the same length, ending in a gate
equivalent to the corresponding gate of the original path. -/
theorem lift_prefix {m : ℕ} {p : Fin (m + 1) → (reduced C).Gate} (hp : (reduced C).IsPath p) :
    ∀ (n : ℕ) (hn : n ≤ m), ∃ q : Fin (n + 1) → C.Gate, C.IsPath q ∧
      Equiv C (q (Fin.last n)) (p ⟨n, Nat.lt_succ_of_le hn⟩).1 := by
  intro n
  induction n with
  | zero =>
    intro hn
    exact ⟨fun _ => (p ⟨0, Nat.lt_succ_of_le hn⟩).1, fun i => absurd i.2 (by omega),
      equiv_refl C _⟩
  | succ n ih =>
    intro hn
    obtain ⟨q, hq, hqlast⟩ := ih (by omega)
    have hstep : 0 < (reduced C).wire (p ⟨n, Nat.lt_succ_of_le (by omega)⟩)
        (p ⟨n + 1, Nat.lt_succ_of_le hn⟩) := hp ⟨n, by omega⟩
    have hW : 0 < W C (q (Fin.last n)) (p ⟨n + 1, Nat.lt_succ_of_le hn⟩).1 := by
      have hstep' : 0 < W C (p ⟨n, Nat.lt_succ_of_le (by omega)⟩).1
          (p ⟨n + 1, Nat.lt_succ_of_le hn⟩).1 := hstep
      rwa [← W_eq_of_equiv C hqlast] at hstep'
    obtain ⟨h, heq, hwpos⟩ := exists_of_W_pos C hW
    refine ⟨Fin.snoc q h, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last =>
        rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
        exact hwpos
      | cast j =>
        rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
        exact hq j
    · rw [Fin.snoc_last]
      exact heq

/-- Every path of `C'` lifts to a path of `C` of the same length. -/
theorem exists_lift {m : ℕ} {p : Fin (m + 1) → (reduced C).Gate} (hp : (reduced C).IsPath p) :
    ∃ q : Fin (m + 1) → C.Gate, C.IsPath q := by
  obtain ⟨q, hq, _⟩ := lift_prefix C hp m (le_refl m)
  exact ⟨q, hq⟩

/-- The set of achievable path lengths of `C'` is contained in that of `C`. -/
theorem depth_set_subset :
    {m : ℕ | ∃ p : Fin (m + 1) → (reduced C).Gate, (reduced C).IsPath p} ⊆
      {m : ℕ | ∃ q : Fin (m + 1) → C.Gate, C.IsPath q} := by
  rintro m ⟨p, hp⟩
  exact exists_lift C hp

/-- The reduced circuit has depth at most that of the original circuit. -/
theorem depth_reduced_le : (reduced C).depth ≤ C.depth :=
  csSup_le_csSup' (bddAbove_depth_set C) (depth_set_subset C)

end Lax461425Proofs.RigidDepth
