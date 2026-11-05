import Lax461425Proofs.PatternsSupportBasic
import Mathlib.Data.Nat.Choose.Basic

/-!
Support facts for rigid circuits of small support size, used for the support depth of
symmetric formulas: `minSupport` is itself the least small support, it is equivariant, and a
support-changing wire can be moved by a transposition fixing its parent so that the child's
support contains a point outside any prescribed small set.
-/

namespace Lax461425Proofs.SymVFSupportDepthBasic

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic

variable {K : Type*} {n : ℕ} {C : Circuit (Fin n × Fin n) K}

/-- For small support size, `minSupport` is a support of size at most the support size. -/
theorem minSupport_spec (hrig : IsRigid C) (hn : 2 * supportSize C < n) (g : C.Gate) :
    IsSupport C g (minSupport C g) ∧ (minSupport C g).ncard ≤ supportSize C := by
  obtain ⟨T, hT, hTc, hle⟩ := exists_least_small_support hrig hn g
  have heq : minSupport C g = T :=
    Set.Subset.antisymm (minSupport_subset_of_isSupport hT hTc)
      (fun x hx S hS hSc => hle S hS hSc hx)
  rw [heq]
  exact ⟨hT, hTc⟩

theorem actPoint_injective (γ : Γ n) : Function.Injective (actPoint γ) := by
  intro x y h
  have := congrArg (actPoint γ⁻¹) h
  rwa [actPoint_self_inv_apply, actPoint_self_inv_apply] at this

theorem minSupport_smul_subset (hrig : IsRigid C) (hn : 2 * supportSize C < n) (γ : Γ n)
    (g : C.Gate) : minSupport C (σOf hrig γ g) ⊆ actPoint γ '' minSupport C g := by
  obtain ⟨hS, hSc⟩ := minSupport_spec hrig hn g
  apply minSupport_subset_of_isSupport (isSupport_smul hrig γ hS)
  rwa [Set.ncard_image_of_injective _ (actPoint_injective γ)]

/-- `minSupport` is equivariant. -/
theorem minSupport_smul (hrig : IsRigid C) (hn : 2 * supportSize C < n) (γ : Γ n)
    (g : C.Gate) : minSupport C (σOf hrig γ g) = actPoint γ '' minSupport C g := by
  apply Set.Subset.antisymm (minSupport_smul_subset hrig hn γ g)
  have h := minSupport_smul_subset hrig hn γ⁻¹ (σOf hrig γ g)
  rw [σOf_inv_σOf] at h
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := h hx
  rw [← hyx, actPoint_inv_self_apply]
  exact hy

/-- A support-changing wire stays support-changing under the group action. -/
theorem not_subset_smul (hrig : IsRigid C) (hn : 2 * supportSize C < n) (γ : Γ n)
    {g g' : C.Gate} (h : ¬ minSupport C g' ⊆ minSupport C g) :
    ¬ minSupport C (σOf hrig γ g') ⊆ minSupport C (σOf hrig γ g) := by
  rw [minSupport_smul hrig hn, minSupport_smul hrig hn,
    Set.image_subset_image_iff (actPoint_injective γ)]
  exact h

/-- A gate is fixed by every group element fixing its `minSupport` pointwise. -/
theorem σOf_fix (hrig : IsRigid C) (hn : 2 * supportSize C < n) {γ : Γ n} {g : C.Gate}
    (hfix : ∀ x ∈ minSupport C g, actPoint γ x = x) : σOf hrig γ g = g :=
  (minSupport_spec hrig hn g).1 γ (σOf hrig γ) hfix (σOf_extends hrig γ)

theorem wire_σOf (hrig : IsRigid C) (γ : Γ n) (g h : C.Gate) :
    C.wire (σOf hrig γ g) (σOf hrig γ h) = C.wire g h :=
  (σOf_extends hrig γ).2 g h

theorem exists_not_mem_of_ncard_lt {s : Set (Fin n)} (hs : s.ncard < n) : ∃ j, j ∉ s := by
  by_contra hcon
  push Not at hcon
  have : s = Set.univ := Set.eq_univ_of_forall hcon
  rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hs
  omega

/-- The rerouting step: a support-changing wire from `g` into `g'` can be moved by an element
fixing `g` so that the support of the new child contains a point outside `U`. -/
theorem exists_reroute (hrig : IsRigid C) (hn : 2 * supportSize C < n) {g g' : C.Gate}
    (hch : ¬ minSupport C g' ⊆ minSupport C g) (U : Set (Fin n ⊕ Fin n))
    (hU : minSupport C g ⊆ U) (hL : (leftPart U).ncard < n) (hR : (rightPart U).ncard < n) :
    ∃ τ : Γ n, σOf hrig τ g = g ∧ ∃ z ∈ minSupport C (σOf hrig τ g'), z ∉ U := by
  obtain ⟨x, hx, hxg⟩ := Set.not_subset.mp hch
  by_cases hxU : x ∈ U
  · cases x with
    | inl i =>
      obtain ⟨j, hj⟩ := exists_not_mem_of_ncard_lt hL
      let τ : Γ n := (Equiv.swap i j, 1)
      refine ⟨τ, σOf_fix hrig hn ?_, Sum.inl j, ?_, hj⟩
      · intro z hz
        cases z with
        | inl a =>
          have hai : a ≠ i := by rintro rfl; exact hxg hz
          have haj : a ≠ j := by rintro rfl; exact hj (hU hz)
          show Sum.inl (Equiv.swap i j a) = Sum.inl a
          rw [Equiv.swap_apply_of_ne_of_ne hai haj]
        | inr b => rfl
      · rw [minSupport_smul hrig hn]
        refine ⟨Sum.inl i, hx, ?_⟩
        show Sum.inl (Equiv.swap i j i) = Sum.inl j
        rw [Equiv.swap_apply_left]
    | inr i =>
      obtain ⟨j, hj⟩ := exists_not_mem_of_ncard_lt hR
      let τ : Γ n := (1, Equiv.swap i j)
      refine ⟨τ, σOf_fix hrig hn ?_, Sum.inr j, ?_, hj⟩
      · intro z hz
        cases z with
        | inl a => rfl
        | inr a =>
          have hai : a ≠ i := by rintro rfl; exact hxg hz
          have haj : a ≠ j := by rintro rfl; exact hj (hU hz)
          show Sum.inr (Equiv.swap i j a) = Sum.inr a
          rw [Equiv.swap_apply_of_ne_of_ne hai haj]
      · rw [minSupport_smul hrig hn]
        refine ⟨Sum.inr i, hx, ?_⟩
        show Sum.inr (Equiv.swap i j i) = Sum.inr j
        rw [Equiv.swap_apply_left]
  · refine ⟨1, by rw [σOf_one]; rfl, x, ?_, hxU⟩
    rw [σOf_one]
    exact hx

/-- Binomial coefficients grow towards the middle. -/
theorem choose_le_choose_of_between {n κ a : ℕ} (h1 : κ ≤ a) (h2 : a + κ ≤ n) :
    n.choose κ ≤ n.choose a := by
  have key : ∀ d, κ + d ≤ n / 2 → n.choose κ ≤ n.choose (κ + d) := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  by_cases ha : a ≤ n / 2
  · have := key (a - κ) (by omega)
    rwa [show κ + (a - κ) = a by omega] at this
  · have := key (n - a - κ) (by omega)
    rw [show κ + (n - a - κ) = n - a by omega, Nat.choose_symm (by omega)] at this
    exact this

theorem ncard_le_left_add_right (S : Set (Fin n ⊕ Fin n)) :
    S.ncard ≤ (leftPart S).ncard + (rightPart S).ncard := by
  have hsub : S ⊆ Sum.inl '' leftPart S ∪ Sum.inr '' rightPart S := by
    intro x hx
    cases x with
    | inl i => exact Or.inl ⟨i, hx, rfl⟩
    | inr j => exact Or.inr ⟨j, hx, rfl⟩
  calc S.ncard ≤ (Sum.inl '' leftPart S ∪ Sum.inr '' rightPart S).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Sum.inl '' leftPart S).ncard + (Sum.inr '' rightPart S).ncard :=
        Set.ncard_union_le _ _
    _ = _ := by
        rw [Set.ncard_image_of_injective _ Sum.inl_injective,
          Set.ncard_image_of_injective _ Sum.inr_injective]

theorem leftPart_union (S T : Set (Fin n ⊕ Fin n)) :
    leftPart (S ∪ T) = leftPart S ∪ leftPart T := rfl

theorem rightPart_union (S T : Set (Fin n ⊕ Fin n)) :
    rightPart (S ∪ T) = rightPart S ∪ rightPart T := rfl

end Lax461425Proofs.SymVFSupportDepthBasic
