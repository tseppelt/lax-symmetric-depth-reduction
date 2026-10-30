import Mathlib.GroupTheory.SpecificGroups.Alternating
import Lax461425Proofs.PatternsSupportBasic

/-!
Upgrading the alternating group to the symmetric group (the core of the paper's proof of the
support theorem): if a subgroup `ι (Perm (Fin n)) ≤ Γₙ` stabilises, on the alternating part of
the pointwise stabiliser of `T`, an internal gate `g` of a reduced rigid circuit, and all
children of `g` have supports whose relevant side is small, then the whole pointwise stabiliser
of `T` fixes `g`.
-/

namespace Lax461425Proofs.STUpgrade

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports Equiv Equiv.Perm
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic

variable {K : Type*} {n : ℕ} {C : Circuit (Fin n × Fin n) K}

/-- Renaming does not change the label of an internal gate. -/
theorem label_map_of_not_isInput {π : Fin n × Fin n → Fin n × Fin n} {g : C.Gate}
    (hg : ¬ (C.label g).IsInput) : (C.label g).map π = C.label g := by
  cases h : C.label g <;> simp_all [GateLabel.IsInput, GateLabel.map]

/-- Two points outside a set of size at most `n - 2`. -/
theorem exists_two_not_mem {U : Set (Fin n)} (hU : U.ncard + 2 ≤ n) :
    ∃ a b, a ≠ b ∧ a ∉ U ∧ b ∉ U := by
  have h1 : 1 < Uᶜ.ncard := by
    rw [Set.ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff).mp h1
  exact ⟨a, b, hab, ha, hb⟩

/-- **Upgrade.** -/
theorem upgrade (hrig : IsRigid C) (hred : C.IsReduced) (ι : Perm (Fin n) →* Γ n)
    (P : Set (Fin n ⊕ Fin n) → Set (Fin n))
    (hι : ∀ (τ : Perm (Fin n)) (S : Set (Fin n ⊕ Fin n)), (∀ i ∈ P S, τ i = i) →
      ι τ ∈ fixingSubgroup (Γ n) S)
    {κ : ℕ} (hκ : 2 * κ ≤ n) {g : C.Gate} (hg : ¬ (C.label g).IsInput) {T : Set (Fin n)}
    (hT : T.ncard + 1 ≤ κ)
    (hAlt : ∀ α ∈ fixingSubgroup (Perm (Fin n)) T ⊓ alternatingGroup (Fin n),
      ι α ∈ gateStabilizer hrig g)
    (hchild : ∀ h, 0 < C.wire g h → ∃ S, IsSupport C h S ∧ (P S).ncard + 1 ≤ κ) :
    ∀ σ ∈ fixingSubgroup (Perm (Fin n)) T, ι σ ∈ gateStabilizer hrig g := by
  classical
  -- wires from `g` into images of children
  have step1 : ∀ σ ∈ fixingSubgroup (Perm (Fin n)) T, ∀ h, 0 < C.wire g h →
      C.wire g (σOf hrig (ι σ) h) = C.wire g h := by
    intro σ hσ h hh
    obtain ⟨S, hS, hSc⟩ := hchild h hh
    have hU : (T ∪ P S).ncard + 2 ≤ n := by
      have := Set.ncard_union_le T (P S)
      omega
    obtain ⟨a, b, hab, haU, hbU⟩ := exists_two_not_mem hU
    rw [Set.mem_union, not_or] at haU hbU
    have hτT : swap a b ∈ fixingSubgroup (Perm (Fin n)) T :=
      PatternsSupportLemma.swap_mem_fixingSubgroup haU.1 hbU.1
    have hτP : ∀ i ∈ P S, swap a b i = i := fun i hi =>
      swap_apply_of_ne_of_ne (fun h => haU.2 (h ▸ hi)) (fun h => hbU.2 (h ▸ hi))
    have hτh : σOf hrig (ι (swap a b)) h = h := by
      have := (isSupport_iff_fixingSubgroup_le hrig h S).mp hS (hι _ S hτP)
      exact this
    obtain ⟨α, hαmem, hαh⟩ : ∃ α ∈ fixingSubgroup (Perm (Fin n)) T ⊓ alternatingGroup (Fin n),
        σOf hrig (ι α) h = σOf hrig (ι σ) h := by
      by_cases hs : sign σ = 1
      · exact ⟨σ, ⟨hσ, mem_alternatingGroup.mpr hs⟩, rfl⟩
      · refine ⟨σ * swap a b, ⟨mul_mem hσ hτT, ?_⟩, ?_⟩
        · show σ * swap a b ∈ alternatingGroup (Fin n)
          rw [mem_alternatingGroup, map_mul, sign_swap hab]
          have : sign σ = -1 := by
            rcases Int.units_eq_one_or (sign σ) with h | h
            · exact absurd h hs
            · exact h
          rw [this]; rfl
        · rw [map_mul, σOf_mul, Equiv.Perm.mul_apply, hτh]
    have hαg : σOf hrig (ι α) g = g := hAlt α hαmem
    have hw := (σOf_extends hrig (ι α)).2 g h
    rw [hαg, hαh] at hw
    exact hw
  intro σ hσ
  -- children are preserved
  have step2 : ∀ σ ∈ fixingSubgroup (Perm (Fin n)) T, ∀ h,
      C.wire g (σOf hrig (ι σ) h) = C.wire g h := by
    intro σ hσ h
    by_cases hh : 0 < C.wire g h
    · exact step1 σ hσ h hh
    · rw [Nat.eq_zero_of_not_pos hh]
      by_contra hne
      have hpos : 0 < C.wire g (σOf hrig (ι σ) h) := Nat.pos_of_ne_zero hne
      have h1 := step1 σ⁻¹ (inv_mem hσ) _ hpos
      rw [map_inv, σOf_inv_σOf] at h1
      exact hh (h1 ▸ hpos)
  show σOf hrig (ι σ) g = g
  set e := σOf hrig (ι σ) with he
  have hlab : C.label (e g) = C.label g := by
    rw [(σOf_extends hrig (ι σ)).1 g]
    exact label_map_of_not_isInput hg
  have hwire : C.wire (e g) = C.wire g := by
    funext h'
    obtain ⟨h, rfl⟩ := e.surjective h'
    rw [(σOf_extends hrig (ι σ)).2 g h, step2 σ hσ h]
  exact hred.2 (e g) g (hlab ▸ hg) hlab hwire

end Lax461425Proofs.STUpgrade
