import Lax461425Proofs.DMGroups

/-!
A transitive permutation group with a nontrivial block has small order.
-/

open scoped Pointwise

namespace Lax461425Proofs.DM

open Nat Equiv MulAction

theorem imprim_card_le {Γ : Type*} [Fintype Γ] (K : Subgroup (Perm Γ))
    [IsPretransitive K Γ] {B : Set Γ} (hB : IsBlock K B) (hne : B.Nonempty)
    (hnt : ¬ B.Subsingleton) (huniv : B ≠ Set.univ) :
    ∃ b m : ℕ, 2 ≤ b ∧ 2 ≤ m ∧ b * m = Fintype.card Γ ∧ Nat.card K ≤ b ! * (m !) ^ b := by
  classical
  set O : Set (Set Γ) := orbit K B with hO
  have hOfin : O.Finite := Set.toFinite O
  haveI : Fintype O := hOfin.fintype
  -- uniqueness of the block through a point
  have uniq : ∀ T ∈ O, ∀ T' ∈ O, ∀ x, x ∈ T → x ∈ T' → T = T' := by
    intro T hT T' hT' x hx hx'
    obtain ⟨k, rfl⟩ := hT
    obtain ⟨k', rfl⟩ := hT'
    by_contra hne'
    exact Set.disjoint_left.mp (hB hne') hx hx'
  have exist : ∀ x : Γ, ∃ T ∈ O, x ∈ T := by
    intro x
    obtain ⟨b0, hb0⟩ := hne
    obtain ⟨k, hk⟩ := exists_smul_eq K b0 x
    exact ⟨k • B, mem_orbit B k, hk ▸ Set.smul_mem_smul_set hb0⟩
  let c : Γ → O := fun x => ⟨(exist x).choose, (exist x).choose_spec.1⟩
  have hc1 : ∀ x, x ∈ (c x : Set Γ) := fun x => (exist x).choose_spec.2
  have hc2 : ∀ x (T : O), x ∈ (T : Set Γ) → c x = T := by
    intro x T hT
    exact Subtype.ext (uniq _ (c x).2 _ T.2 x (hc1 x) hT)
  let ρ : K →* Perm O := MulAction.toPermHom K O
  have hker : ∀ k ∈ ρ.ker, c ∘ (k : Perm Γ) = c := by
    intro k hk
    funext x
    have h1 : ρ k = 1 := hk
    have h2 : k • (c x) = c x := by
      have := congrArg (fun e : Perm O => e (c x)) h1
      simpa [ρ] using this
    have h3 : (k : Perm Γ) x ∈ ((c x : O) : Set Γ) := by
      have : k • x ∈ k • ((c x : O) : Set Γ) := Set.smul_mem_smul_set (hc1 x)
      have h4 : k • ((c x : O) : Set Γ) = ((c x : O) : Set Γ) := congrArg Subtype.val h2
      rw [h4] at this
      exact this
    exact hc2 _ _ h3
  have hker_card : Nat.card ρ.ker ≤ Set.ncard {g : Perm Γ | c ∘ g = c} := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_le_card_of_injective
      (fun k : ρ.ker => (⟨((k : K) : Perm Γ), hker k k.2⟩ : {g : Perm Γ | c ∘ g = c})) ?_
    intro a b hab
    have := congrArg (Subtype.val : {g : Perm Γ | c ∘ g = c} → Perm Γ) hab
    exact Subtype.ext (Subtype.ext this)
  rw [DomMulAct.stabilizer_ncard c] at hker_card
  -- the fibres of `c` are the blocks
  have hfib : ∀ i : O, Set.ncard {a | c a = i} = B.ncard := by
    intro i
    have : {a | c a = i} = (i : Set Γ) := by
      ext a
      constructor
      · intro h; rw [Set.mem_setOf_eq] at h; rw [← h]; exact hc1 a
      · intro h; exact hc2 a i h
    rw [this]
    obtain ⟨k, hk⟩ := i.2
    rw [← hk, Set.ncard_smul_set]
  simp only [hfib, Finset.prod_const, Finset.card_univ] at hker_card
  have hcardO : Fintype.card O = O.ncard := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  rw [hcardO] at hker_card
  have hmain : Nat.card K ≤ (B.ncard ! ) ^ O.ncard * O.ncard ! := by
    refine (card_le_ker_mul ρ).trans ?_
    have : Nat.card (Perm O) = O.ncard ! := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, hcardO]
    rw [this]
    exact Nat.mul_le_mul_right _ hker_card
  have hprod := hB.ncard_block_mul_ncard_orbit_eq hne
  rw [Nat.card_eq_fintype_card] at hprod
  have hmlt : B.ncard < Fintype.card Γ := by
    have h1 : B ⊂ Set.univ := Set.ssubset_univ_iff.mpr huniv
    have := Set.ncard_lt_ncard h1 (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  have hm2 : 2 ≤ B.ncard := by
    by_contra hlt
    apply hnt
    have : B.ncard ≤ 1 := by omega
    exact (Set.ncard_le_one_iff_subsingleton).mp this
  have hb2 : 2 ≤ O.ncard := by
    by_contra hlt
    have hO1 : O.ncard ≤ 1 := by omega
    interval_cases h : O.ncard
    · rw [mul_zero] at hprod; omega
    · rw [mul_one] at hprod; omega
  exact ⟨O.ncard, B.ncard, hb2, hm2, by rw [mul_comm]; exact hprod, by
    rw [mul_comm]; exact hmain⟩

end Lax461425Proofs.DM
