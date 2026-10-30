import Lax461425Proofs.DMCore

/-!
Restriction of a subgroup of `Perm Ω` to an invariant subset `{x // p x}`.
-/

namespace Lax461425Proofs.DM

open Nat Equiv

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (p : Ω → Prop) [DecidablePred p]

/-- The pointwise-fixing subgroup of the complement, viewed as a subgroup of `Perm {x // p x}`. -/
def restrictSub (H : Subgroup (Perm Ω)) : Subgroup (Perm (Subtype p)) :=
  H.comap (Equiv.Perm.ofSubtype : Perm (Subtype p) →* Perm Ω)

variable {p}

theorem mem_restrictSub {H : Subgroup (Perm Ω)} {k : Perm (Subtype p)} :
    k ∈ restrictSub p H ↔ (Equiv.Perm.ofSubtype k : Perm Ω) ∈ H := Iff.rfl

theorem card_le_restrict {H : Subgroup (Perm Ω)} (hinv : ∀ h ∈ H, ∀ y, p (h y) ↔ p y) :
    Nat.card H ≤ Nat.card (restrictSub p H) * (Fintype.card {y // ¬ p y})! := by
  let ρ : H →* Perm {y // ¬ p y} :=
    MonoidHom.mk' (fun h => Equiv.Perm.subtypePerm (h : Perm Ω)
      (fun x => not_congr (hinv h h.2 x))) (by
        intro a b
        ext z
        rfl)
  refine (card_le_ker_mul ρ).trans ?_
  rw [Nat.card_eq_fintype_card (α := Perm {y // ¬ p y}), Fintype.card_perm]
  refine Nat.mul_le_mul_right _ ?_
  refine Nat.card_le_card_of_injective
    (fun k : ρ.ker => (⟨Equiv.Perm.subtypePerm ((k : H) : Perm Ω) (hinv _ (k : H).2), ?_⟩ :
      restrictSub p H)) ?_
  · rw [mem_restrictSub]
    have hk : ρ k.1 = 1 := k.2
    have : ∀ x, ((k : H) : Perm Ω) x ≠ x → p x := by
      intro x hx
      by_contra hpx
      apply hx
      have := congrArg (fun e : Perm {y // ¬ p y} => (e ⟨x, hpx⟩ : Ω)) hk
      simpa [ρ] using this
    rw [Equiv.Perm.ofSubtype_subtypePerm (hinv _ (k : H).2) this]
    exact (k : H).2
  · intro a b hab
    have := congrArg (fun e : restrictSub p H => (Equiv.Perm.ofSubtype (e : Perm (Subtype p)) :
      Perm Ω)) hab
    simp only at this
    have hfix : ∀ k : ρ.ker, ∀ x, ((k : H) : Perm Ω) x ≠ x → p x := by
      intro k x hx
      by_contra hpx
      apply hx
      have hk : ρ k.1 = 1 := k.2
      have := congrArg (fun e : Perm {y // ¬ p y} => (e ⟨x, hpx⟩ : Ω)) hk
      simpa [ρ] using this
    rw [Equiv.Perm.ofSubtype_subtypePerm (hinv _ (a : H).2) (hfix a),
      Equiv.Perm.ofSubtype_subtypePerm (hinv _ (b : H).2) (hfix b)] at this
    exact Subtype.ext (Subtype.ext this)

theorem restrict_conj {H : Subgroup (Perm Ω)} {h : Perm Ω} (hh : h ∈ H)
    (hinv : ∀ y, p (h y) ↔ p y) {k : Perm (Subtype p)} (hk : k ∈ restrictSub p H) :
    Equiv.Perm.subtypePerm h hinv * k * (Equiv.Perm.subtypePerm h hinv)⁻¹ ∈ restrictSub p H := by
  rw [mem_restrictSub] at hk ⊢
  have : (Equiv.Perm.ofSubtype (Equiv.Perm.subtypePerm h hinv * k *
      (Equiv.Perm.subtypePerm h hinv)⁻¹) : Perm Ω) = h * Equiv.Perm.ofSubtype k * h⁻¹ := by
    ext z
    by_cases hz : p z
    · have hz' : p (h⁻¹ z) := by
        rw [← hinv]; simpa using hz
      rw [Equiv.Perm.ofSubtype_apply_of_mem _ hz]
      have e : (Equiv.Perm.subtypePerm h hinv)⁻¹ ⟨z, hz⟩ = ⟨h⁻¹ z, hz'⟩ := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        apply Subtype.ext
        simp [Equiv.Perm.subtypePerm_apply]
      have rhs : (h * (Equiv.Perm.ofSubtype k : Perm Ω) * h⁻¹) z = h ((k ⟨h⁻¹ z, hz'⟩ : Subtype p) : Ω) := by
        simp only [Perm.mul_apply]
        rw [Equiv.Perm.ofSubtype_apply_of_mem _ hz']
      rw [rhs]
      simp only [Perm.mul_apply]
      rw [e]
      rfl
    · have hz' : ¬ p (h⁻¹ z) := by
        rw [← hinv]; simpa using hz
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hz]
      simp only [Perm.mul_apply]
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hz']
      simp
  rw [this]
  exact H.mul_mem (H.mul_mem hh hk) (H.inv_mem hh)

theorem fixing_le {H : Subgroup (Perm Ω)}
    (hA : alternatingGroup (Subtype p) ≤ restrictSub p H) :
    fixingSubgroup (Perm Ω) {y | ¬ p y} ⊓ alternatingGroup Ω ≤ H := by
  intro σ hσ
  obtain ⟨hσfix, hσalt⟩ := hσ
  have hfix : ∀ y, ¬ p y → σ y = y := fun y hy => (mem_fixingSubgroup_iff _).mp hσfix y hy
  have hinv : ∀ y, p (σ y) ↔ p y := by
    intro y
    by_cases hy : p y
    · constructor
      · intro _; exact hy
      · intro _
        by_contra h
        have h1 := hfix _ h
        have h2 := σ.injective h1
        exact h (by rw [h2]; exact hy)
    · rw [hfix y hy]
  have hsupp : ∀ x, σ x ≠ x → p x := fun x hx => by_contra fun hpx => hx (hfix x hpx)
  have hsub : Equiv.Perm.subtypePerm σ hinv ∈ restrictSub p H := by
    apply hA
    rw [Equiv.Perm.mem_alternatingGroup, ← Equiv.Perm.sign_ofSubtype,
      Equiv.Perm.ofSubtype_subtypePerm hinv hsupp]
    exact Equiv.Perm.mem_alternatingGroup.mp hσalt
  rw [mem_restrictSub, Equiv.Perm.ofSubtype_subtypePerm hinv hsupp] at hsub
  exact hsub

end Lax461425Proofs.DM
