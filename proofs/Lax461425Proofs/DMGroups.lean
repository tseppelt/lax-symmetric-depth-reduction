import Lax461425Proofs.DMBochert

/-!
Counting lemmas for permutation groups: groups with small orbits, and groups with a
nontrivial block system.
-/

open scoped Pointwise

namespace Lax461425Proofs.DM

open Nat Equiv

theorem card_le_ker_mul {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (ρ : G →* G') : Nat.card G ≤ Nat.card ρ.ker * Nat.card G' := by
  have h := Subgroup.card_mul_index ρ.ker
  rw [Subgroup.index_ker] at h
  rw [← h]
  apply Nat.mul_le_mul_left
  exact Nat.card_le_card_of_injective (Subtype.val : ρ.range → G') Subtype.val_injective

theorem card_subgroup_le_ncard {Γ : Type*} [Finite Γ] (K : Subgroup (Perm Γ))
    (S : Set (Perm Γ)) (h : ∀ k ∈ K, k ∈ S) : Nat.card K ≤ S.ncard := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective (fun k : K => (⟨k.1, h k.1 k.2⟩ : S))
    (fun a b hab => Subtype.ext (congrArg (Subtype.val : S → Perm Γ) hab))

/-- A permutation group all of whose orbits have at most `B` points has order at most
`B ! * (g - B)!`. -/
theorem card_le_of_orbits_le {Γ : Type*} [Fintype Γ] (K : Subgroup (Perm Γ)) (B : ℕ)
    (hB : B ≤ Fintype.card Γ) (h : ∀ x : Γ, (MulAction.orbit K x).ncard ≤ B) :
    Nat.card K ≤ B ! * (Fintype.card Γ - B)! := by
  classical
  let f : Γ → MulAction.orbitRel.Quotient K Γ := fun x => Quotient.mk'' x
  have hf : ∀ k ∈ K, f ∘ (k : Perm Γ) = f := by
    intro k hk
    funext x
    exact Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit x (⟨k, hk⟩ : K)))
  have h1 : Nat.card K ≤ Set.ncard {g : Perm Γ | f ∘ g = f} :=
    card_subgroup_le_ncard K _ hf
  rw [DomMulAct.stabilizer_ncard f] at h1
  have hfib : ∀ i, Set.ncard {a | f a = i} ≤ B := by
    intro i
    induction i using Quotient.inductionOn' with
    | h x =>
      have : {a | f a = Quotient.mk'' x} = MulAction.orbit K x := by
        ext a
        simp only [Set.mem_setOf_eq, f]
        rw [Quotient.eq'']
        exact MulAction.orbitRel_apply
      rw [this]
      exact h x
  have hsum : ∑ i, Set.ncard {a | f a = i} = Fintype.card Γ := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset Γ))
      (t := (Finset.univ : Finset (MulAction.orbitRel.Quotient K Γ))) (f := f)
      (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ] at this
    rw [this]
    apply Finset.sum_congr rfl
    intro i _
    rw [Set.ncard_eq_toFinset_card']
    simp
  have h2 := prod_factorial_le (fun i => Set.ncard {a | f a = i}) B Finset.univ
    (fun i _ => hfib i) (by rw [hsum]; exact hB)
  rw [hsum] at h2
  exact h1.trans h2

end Lax461425Proofs.DM
