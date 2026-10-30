import Lax461425Proofs.DMImprimitive

/-!
Core dichotomy: a subgroup of `Perm Γ` (`|Γ| ≥ 11`) whose point orbits are permuted
transitively by the normaliser either contains `Alt Γ` or is small.
-/

open scoped Pointwise

namespace Lax461425Proofs.DM

open Nat Equiv MulAction

theorem core_dichotomy {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (hg : 11 ≤ Fintype.card Γ)
    (K : Subgroup (Perm Γ))
    (hK : ∀ x y : Γ, ∃ ψ : Perm Γ, ψ x = y ∧ ∀ k ∈ K, ψ * k * ψ⁻¹ ∈ K) :
    alternatingGroup Γ ≤ K ∨
      Nat.card K ≤ 2 * (Fintype.card Γ / 2)! * (Fintype.card Γ - Fintype.card Γ / 2)! := by
  classical
  by_cases htrans : ∀ x y : Γ, ∃ k : K, k • x = y
  · haveI : IsPretransitive K Γ := ⟨htrans⟩
    by_cases hprim : IsPreprimitive K Γ
    · by_cases h3 : ∃ t ∈ K, t.IsThreeCycle
      · obtain ⟨t, htK, ht3⟩ := h3
        exact Or.inl (Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim ht3 htK)
      · push Not at h3
        exact Or.inr (card_le_of_no_three_cycle K hg h3)
    · right
      have : ¬ ∀ {B : Set Γ}, IsBlock K B → IsTrivialBlock B := fun h =>
        hprim ⟨fun {B} hB => h hB⟩
      push Not at this
      obtain ⟨B, hB, hBt⟩ := this
      unfold IsTrivialBlock at hBt
      push Not at hBt
      obtain ⟨hnt', huniv⟩ := hBt
      have hnt : ¬ B.Subsingleton := Set.not_subsingleton_iff.mpr hnt'
      have hne : B.Nonempty := hnt'.nonempty
      obtain ⟨b, m, hb, hm, hbm, hcard⟩ := imprim_card_le K hB hne hnt huniv
      refine hcard.trans ?_
      rw [← hbm]
      exact imprim_bound hb hm
  · right
    push Not at htrans
    obtain ⟨x, y, hxy⟩ := htrans
    have hle : ∀ u v : Γ, (orbit K u).ncard ≤ (orbit K v).ncard := by
      intro u v
      obtain ⟨ψ, hψ, hψK⟩ := hK u v
      apply Set.ncard_le_ncard_of_injOn (fun z => ψ z)
      · intro z hz
        obtain ⟨k, rfl⟩ := hz
        refine ⟨⟨ψ * (k : Perm Γ) * ψ⁻¹, hψK k k.2⟩, ?_⟩
        show (ψ * (k : Perm Γ) * ψ⁻¹) v = ψ ((k : Perm Γ) u)
        rw [← hψ]
        simp [Perm.mul_apply]
      · exact ψ.injective.injOn
    have hEq : ∀ u v : Γ, (orbit K u).ncard = (orbit K v).ncard :=
      fun u v => le_antisymm (hle u v) (hle v u)
    have hdisj : Disjoint (orbit K x) (orbit K y) := by
      rcases orbit.eq_or_disjoint (G := K) x y with h | h
      · exfalso
        have : y ∈ orbit K x := by
          rw [h]; exact mem_orbit_self y
        obtain ⟨k, hk⟩ := this
        exact hxy k hk
      · exact h
    have h2 : 2 * (orbit K x).ncard ≤ Fintype.card Γ := by
      have h1 := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
      have h3 := Set.ncard_le_card (orbit K x ∪ orbit K y)
      rw [Nat.card_eq_fintype_card] at h3
      rw [← hEq x y] at h1
      omega
    have hB : Fintype.card Γ - Fintype.card Γ / 2 ≤ Fintype.card Γ := Nat.sub_le _ _
    have := card_le_of_orbits_le K (Fintype.card Γ - Fintype.card Γ / 2) hB (by
      intro u
      rw [hEq u x]
      omega)
    rw [show Fintype.card Γ - (Fintype.card Γ - Fintype.card Γ / 2) = Fintype.card Γ / 2 by omega]
      at this
    calc Nat.card K ≤ _ := this
      _ ≤ 2 * (Fintype.card Γ / 2)! * (Fintype.card Γ - Fintype.card Γ / 2)! := by
        rw [mul_comm]
        nlinarith [Nat.factorial_pos (Fintype.card Γ / 2),
          Nat.factorial_pos (Fintype.card Γ - Fintype.card Γ / 2)]

end Lax461425Proofs.DM
