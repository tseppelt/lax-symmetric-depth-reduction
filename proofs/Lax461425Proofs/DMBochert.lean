import Lax461425Proofs.DMNumerics

/-!
Bochert's argument: a permutation group without 3-cycles has a base of size at most half the
degree, hence small order.
-/

namespace Lax461425Proofs.DM

open Nat Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem perm_inv_fix (f : Perm α) (z : α) : f⁻¹ z = z ↔ f z = z := by
  rw [Equiv.Perm.inv_eq_iff_eq, eq_comm]

/-- The commutator of two permutations whose supports meet in exactly one point, which is moved
by both, is a 3-cycle. -/
theorem isThreeCycle_commutator {x y : Perm α} {a : α} (hxa : x a ≠ a) (hya : y a ≠ a)
    (hxy : ∀ b, x b ≠ b → y b ≠ b → b = a) : IsThreeCycle (x * y * x⁻¹ * y⁻¹) := by
  have hsupp : ∀ β, ((x * y * x⁻¹ * y⁻¹) : Perm α) β ≠ β → β = a ∨ β = x a ∨ β = y a := by
    intro β hβ
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    apply hβ
    simp only [Perm.mul_apply]
    by_cases hby : y β = β
    · have e1 : y⁻¹ β = β := (perm_inv_fix y β).2 hby
      rw [e1]
      by_cases hbx : x β = β
      · have e2 : x⁻¹ β = β := (perm_inv_fix x β).2 hbx
        rw [e2, hby, hbx]
      · obtain ⟨β2, hxβ2⟩ : ∃ β2, x β2 = β := ⟨x⁻¹ β, by simp⟩
        have e2 : x⁻¹ β = β2 := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hxβ2.symm
        rw [e2]
        have hne : x β2 ≠ β2 := by
          intro h
          apply hbx
          have hb : β = β2 := by rw [← hxβ2]; exact h
          exact (congrArg x hb).trans (h.trans hb.symm)
        by_cases hyβ2 : y β2 = β2
        · rw [hyβ2, hxβ2]
        · exfalso
          have := hxy β2 hne hyβ2
          apply h2
          rw [← hxβ2, this]
    · obtain ⟨β1, hyβ1⟩ : ∃ β1, y β1 = β := ⟨y⁻¹ β, by simp⟩
      have e1 : y⁻¹ β = β1 := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hyβ1.symm
      rw [e1]
      have hyne : y β1 ≠ β1 := by
        intro h
        apply hby
        have hb : β = β1 := by rw [← hyβ1]; exact h
        exact (congrArg y hb).trans (h.trans hb.symm)
      by_cases hxβ1 : x β1 = β1
      · have e2 : x⁻¹ β1 = β1 := (perm_inv_fix x β1).2 hxβ1
        rw [e2, hyβ1]
        by_contra hxβ
        exact h1 (hxy β hxβ hby)
      · exfalso
        have := hxy β1 hxβ1 hyne
        apply h3
        rw [← hyβ1, this]
  have hsub : ((x * y * x⁻¹ * y⁻¹) : Perm α).support ⊆ {a, x a, y a} := by
    intro β hβ
    rw [Equiv.Perm.mem_support] at hβ
    rcases hsupp β hβ with h | h | h <;> simp [h]
  have hcard : ((x * y * x⁻¹ * y⁻¹) : Perm α).support.card ≤ 3 :=
    (Finset.card_le_card hsub).trans (Finset.card_le_three)
  have hne1 : ((x * y * x⁻¹ * y⁻¹) : Perm α) ≠ 1 := by
    intro h
    have h' : x * y = y * x := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h)
    have hyx : y a ∈ x.support := by
      rw [Equiv.Perm.mem_support]
      intro hx
      apply hxa
      have : y (x a) = y a := by
        have := congrArg (fun f : Perm α => f a) h'
        simp only [Perm.mul_apply] at this
        rw [← this, hx]
      exact y.injective this
    have hyy : y a ∈ y.support := by
      rw [Equiv.Perm.mem_support]
      intro h'
      exact hya (y.injective h')
    have := hxy (y a) (Equiv.Perm.mem_support.mp hyx) (Equiv.Perm.mem_support.mp hyy)
    exact hya this
  have hsign : Perm.sign ((x * y * x⁻¹ * y⁻¹) : Perm α) = 1 := by
    simp only [map_mul, map_inv]
    generalize Perm.sign x = u
    generalize Perm.sign y = v
    rw [mul_comm u v, mul_inv_cancel_right, mul_inv_cancel]
  rw [← card_support_eq_three_iff]
  have h0 : ((x * y * x⁻¹ * y⁻¹) : Perm α).support.card ≠ 0 := fun h => hne1 (card_support_eq_zero.mp h)
  have h1 := card_support_ne_one ((x * y * x⁻¹ * y⁻¹) : Perm α)
  have h2 : ((x * y * x⁻¹ * y⁻¹) : Perm α).support.card ≠ 2 := by
    intro h
    have := (card_support_eq_two.mp h).sign_eq
    rw [hsign] at this
    exact absurd this (by decide)
  omega

open Classical in
/-- Bochert: a subgroup with no 3-cycle has a base of size at most half the degree. -/
theorem exists_base_half (K : Subgroup (Perm α)) (hK : ∀ t ∈ K, ¬ t.IsThreeCycle) :
    ∃ S : Finset α, 2 * S.card ≤ Fintype.card α ∧
      ∀ k ∈ K, (∀ s ∈ S, k s = s) → k = 1 := by
  let Bs : Finset (Finset α) :=
    Finset.univ.filter (fun S : Finset α => ∀ k ∈ K, (∀ s ∈ S, k s = s) → k = 1)
  have hne : Bs.Nonempty := ⟨Finset.univ, by
    simp only [Bs, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k _ hk
    ext z; exact hk z (by simp)⟩
  obtain ⟨S, hSB, hmin⟩ := Finset.exists_min_image Bs Finset.card hne
  have hS : ∀ k ∈ K, (∀ s ∈ S, k s = s) → k = 1 := by
    simpa [Bs] using hSB
  refine ⟨S, ?_, hS⟩
  by_contra hcon
  have hlt : Fintype.card α < 2 * S.card := by omega
  have hmin' : ∀ T : Finset α, (∀ k ∈ K, (∀ s ∈ T, k s = s) → k = 1) → S.card ≤ T.card := by
    intro T hT
    exact hmin T (by simpa [Bs] using hT)
  -- the complement is not a base
  have hD : ¬ ∀ k ∈ K, (∀ s ∈ Sᶜ, k s = s) → k = 1 := by
    intro h
    have := hmin' _ h
    rw [Finset.card_compl] at this
    omega
  push Not at hD
  obtain ⟨x, hxK, hxD, hx1⟩ := hD
  obtain ⟨a, ha⟩ : ∃ a, x a ≠ a := by
    by_contra h
    push Not at h
    exact hx1 (by ext z; exact h z)
  have haS : a ∈ S := by
    by_contra h
    exact ha (hxD a (by simpa using h))
  have hE : ¬ ∀ k ∈ K, (∀ s ∈ S.erase a, k s = s) → k = 1 := by
    intro h
    have := hmin' _ h
    rw [Finset.card_erase_of_mem haS] at this
    have : 0 < S.card := Finset.card_pos.mpr ⟨a, haS⟩
    omega
  push Not at hE
  obtain ⟨y, hyK, hyE, hy1⟩ := hE
  have hya : y a ≠ a := by
    intro h
    apply hy1
    apply hS y hyK
    intro s hs
    by_cases hsa : s = a
    · rw [hsa]; exact h
    · exact hyE s (Finset.mem_erase.mpr ⟨hsa, hs⟩)
  have hxy : ∀ b, x b ≠ b → y b ≠ b → b = a := by
    intro b hb1 hb2
    by_contra hba
    have hbS : b ∈ S := by
      by_contra h
      exact hb1 (hxD b (by simpa using h))
    exact hb2 (hyE b (Finset.mem_erase.mpr ⟨hba, hbS⟩))
  have h3 := isThreeCycle_commutator ha hya hxy
  apply hK (x * y * x⁻¹ * y⁻¹) _ h3
  exact K.mul_mem (K.mul_mem (K.mul_mem hxK hyK) (K.inv_mem hxK)) (K.inv_mem hyK)

open Classical in
theorem card_mul_factorial_le_of_base (K : Subgroup (Perm α)) (S : Finset α)
    (hS : ∀ k ∈ K, (∀ s ∈ S, k s = s) → k = 1) :
    Nat.card K * (Fintype.card α - S.card)! ≤ (Fintype.card α)! := by
  let f : K → (S ↪ α) := fun k => ⟨fun s => (k : Perm α) s, fun s t h =>
    Subtype.ext ((k : Perm α).injective h)⟩
  have hf : Function.Injective f := by
    intro k1 k2 h
    have : ∀ s ∈ S, ((k1 : Perm α)⁻¹ * (k2 : Perm α)) s = s := by
      intro s hs
      have h2 : (k1 : Perm α) s = (k2 : Perm α) s := congrArg (fun e : S ↪ α => e ⟨s, hs⟩) h
      show (k1 : Perm α)⁻¹ ((k2 : Perm α) s) = s
      rw [← h2]; simp
    have h1 := hS ((k1 : Perm α)⁻¹ * (k2 : Perm α)) (K.mul_mem (K.inv_mem k1.2) k2.2) this
    apply Subtype.ext
    exact inv_mul_eq_one.mp h1
  have hle : Nat.card K ≤ Nat.card (S ↪ α) := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := (S ↪ α)), Fintype.card_embedding_eq] at hle
  simp only [Fintype.card_coe] at hle
  have hSle : S.card ≤ Fintype.card α := Finset.card_le_univ S
  calc Nat.card K * (Fintype.card α - S.card)!
      ≤ (Fintype.card α).descFactorial S.card * (Fintype.card α - S.card)! :=
        Nat.mul_le_mul_right _ hle
    _ = (Fintype.card α)! := by rw [mul_comm]; exact Nat.factorial_mul_descFactorial hSle

theorem card_le_of_no_three_cycle (K : Subgroup (Perm α)) (hg : 11 ≤ Fintype.card α)
    (hK : ∀ t ∈ K, ¬ t.IsThreeCycle) :
    Nat.card K ≤ 2 * (Fintype.card α / 2)! * (Fintype.card α - Fintype.card α / 2)! := by
  obtain ⟨S, hS2, hS⟩ := exists_base_half K hK
  exact bound_of_desc hg hS2 (card_mul_factorial_le_of_base K S hS)

end Lax461425Proofs.DM
