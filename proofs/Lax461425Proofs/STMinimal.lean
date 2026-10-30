import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
import Lax461425Proofs.ConverseOrbitSupport
import Lax461425Proofs.STNumerics

/-!
From supports with small sides to supports of small total size: the counting argument at the
end of the proof of the support theorem, via `⊆`-least supports with small sides.
-/

namespace Lax461425Proofs.STMinimal

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports Equiv
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic

variable {K : Type*} {n : ℕ} {C : Circuit (Fin n × Fin n) K}

/-- `S` supports `g` and both sides of `S` have size at most `κ - 1`. -/
def Good (κ : ℕ) (g : C.Gate) (S : Set (Fin n ⊕ Fin n)) : Prop :=
  IsSupport C g S ∧ (leftPart S).ncard + 1 ≤ κ ∧ (rightPart S).ncard + 1 ≤ κ

/-- `M` is the `⊆`-least good support of `g`. -/
def Least (κ : ℕ) (g : C.Gate) (M : Set (Fin n ⊕ Fin n)) : Prop :=
  Good κ g M ∧ ∀ S, Good κ g S → M ⊆ S

theorem good_inter (hrig : IsRigid C) {κ : ℕ} (hκ : 2 * κ ≤ n) {g : C.Gate}
    {S T : Set (Fin n ⊕ Fin n)} (hS : Good κ g S) (hT : Good κ g T) : Good κ g (S ∩ T) := by
  obtain ⟨hS1, hS2, hS3⟩ := hS
  obtain ⟨hT1, hT2, hT3⟩ := hT
  have hL : leftPart S ∪ leftPart T ≠ Set.univ := by
    intro hcon
    have h1 : (leftPart S ∪ leftPart T).ncard = n := by rw [hcon]; simp [Set.ncard_univ]
    have := Set.ncard_union_le (leftPart S) (leftPart T)
    omega
  have hR : rightPart S ∪ rightPart T ≠ Set.univ := by
    intro hcon
    have h1 : (rightPart S ∪ rightPart T).ncard = n := by rw [hcon]; simp [Set.ncard_univ]
    have := Set.ncard_union_le (rightPart S) (rightPart T)
    omega
  refine ⟨isSupport_inter hrig hS1 hT1 hL hR, ?_, ?_⟩
  · have := Set.ncard_le_ncard (Set.inter_subset_left : leftPart S ∩ leftPart T ⊆ leftPart S)
      (Set.toFinite _)
    rw [leftPart_inter]; omega
  · have := Set.ncard_le_ncard (Set.inter_subset_left : rightPart S ∩ rightPart T ⊆ rightPart S)
      (Set.toFinite _)
    rw [rightPart_inter]; omega

theorem exists_least (hrig : IsRigid C) {κ : ℕ} (hκ : 2 * κ ≤ n) {g : C.Gate}
    (hex : ∃ S, Good κ g S) : ∃ M, Least κ g M := by
  obtain ⟨M, hM, hmin⟩ := (measure (Set.ncard : Set (Fin n ⊕ Fin n) → ℕ)).wf.has_min
    {S | Good κ g S} hex
  refine ⟨M, hM, fun S hS => ?_⟩
  have hi := good_inter hrig hκ hM hS
  have h : M.ncard ≤ (M ∩ S).ncard := not_lt.mp (hmin _ hi)
  have heq : M ∩ S = M := Set.eq_of_subset_of_ncard_le Set.inter_subset_left h (Set.toFinite _)
  rw [← heq]
  exact Set.inter_subset_right

theorem leftPart_image (γ : Γ n) (S : Set (Fin n ⊕ Fin n)) :
    leftPart (actPoint γ '' S) = γ.1 '' leftPart S := by
  ext i
  constructor
  · rintro ⟨x, hx, h⟩
    cases x with
    | inl j => exact ⟨j, hx, Sum.inl_injective h⟩
    | inr j => exact absurd h (by simp [actPoint])
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Sum.inl j, hj, rfl⟩

theorem rightPart_image (γ : Γ n) (S : Set (Fin n ⊕ Fin n)) :
    rightPart (actPoint γ '' S) = γ.2 '' rightPart S := by
  ext i
  constructor
  · rintro ⟨x, hx, h⟩
    cases x with
    | inl j => exact absurd h (by simp [actPoint])
    | inr j => exact ⟨j, hx, Sum.inr_injective h⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Sum.inr j, hj, rfl⟩

theorem good_image (hrig : IsRigid C) (γ : Γ n) {κ : ℕ} {g : C.Gate} {S : Set (Fin n ⊕ Fin n)}
    (hS : Good κ g S) : Good κ (σOf hrig γ g) (actPoint γ '' S) := by
  refine ⟨isSupport_smul hrig γ hS.1, ?_, ?_⟩
  · rw [leftPart_image, Set.ncard_image_of_injective _ γ.1.injective]; exact hS.2.1
  · rw [rightPart_image, Set.ncard_image_of_injective _ γ.2.injective]; exact hS.2.2

theorem least_image (hrig : IsRigid C) (γ : Γ n) {κ : ℕ} {g : C.Gate}
    {M : Set (Fin n ⊕ Fin n)} (hM : Least κ g M) :
    Least κ (σOf hrig γ g) (actPoint γ '' M) := by
  refine ⟨good_image hrig γ hM.1, fun S' hS' => ?_⟩
  have h1 : Good κ g (actPoint γ⁻¹ '' S') := by
    have := good_image hrig γ⁻¹ hS'
    rwa [σOf_inv_σOf hrig γ g] at this
  have h2 := Set.image_mono (f := actPoint γ) (hM.2 _ h1)
  rwa [← Set.image_comp, show actPoint γ ∘ actPoint γ⁻¹ = id from
    funext (actPoint_inv_self_apply γ), Set.image_id] at h2

theorem least_unique {κ : ℕ} {g : C.Gate} {M M' : Set (Fin n ⊕ Fin n)} (h : Least κ g M)
    (h' : Least κ g M') : M = M' :=
  Set.Subset.antisymm (h.2 _ h'.1) (h'.2 _ h.1)

theorem exists_perm_image_eq (A B : Finset (Fin n)) (h : A.card = B.card) :
    ∃ σ : Perm (Fin n), A.image σ = B := by
  classical
  have hA : A ∈ Set.powersetCard (Fin n) A.card := Set.powersetCard.mem_iff.mpr rfl
  have hB : B ∈ Set.powersetCard (Fin n) A.card := Set.powersetCard.mem_iff.mpr h.symm
  have := Set.powersetCard.isPretransitive (α := Fin n) (n := A.card)
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Perm (Fin n))
    (⟨A, hA⟩ : Set.powersetCard (Fin n) A.card) ⟨B, hB⟩
  refine ⟨σ, ?_⟩
  have := congrArg Subtype.val hσ
  simpa [Finset.smul_finset_def] using this

/-- **Counting.** If every gate has a good support and the orbit size is `< choose n κ`, then
every gate has a support of size at most `κ - 1`. -/
theorem exists_support_le (hn : 20 ≤ n) (hrig : IsRigid C) {κ : ℕ} (hκ : 3 * κ ≤ n + 2)
    (hgood : ∀ g : C.Gate, ∃ S, Good κ g S) (horb : orbitSize C < n.choose κ) (g : C.Gate) :
    ∃ S, IsSupport C g S ∧ S.ncard + 1 ≤ κ := by
  classical
  have hκ2 : 2 * κ ≤ n := by omega
  choose Mf hMf using fun g' => exists_least hrig hκ2 (hgood g')
  have hMf_smul : ∀ (γ : Γ n) (g' : C.Gate),
      Mf (σOf hrig γ g') = actPoint γ '' Mf g' := fun γ g' =>
    least_unique (hMf _) (least_image hrig γ (hMf g'))
  set M := Mf g with hMdef
  set kL := (leftPart M).ncard with hkL
  set kR := (rightPart M).ncard with hkR
  have hgM := (hMf g).1
  let Φ : C.Gate → Finset (Fin n) × Finset (Fin n) := fun g' =>
    ((Set.toFinite (leftPart (Mf g'))).toFinset, (Set.toFinite (rightPart (Mf g'))).toFinset)
  let LF := (Set.toFinite (leftPart M)).toFinset
  let RF := (Set.toFinite (rightPart M)).toFinset
  have hLFc : LF.card = kL := by
    rw [hkL, ← Set.ncard_coe_finset]; simp [LF]
  have hRFc : RF.card = kR := by
    rw [hkR, ← Set.ncard_coe_finset]; simp [RF]
  have hsub : (((Finset.powersetCard kL (Finset.univ : Finset (Fin n))) ×ˢ
      (Finset.powersetCard kR (Finset.univ : Finset (Fin n))) :
        Finset (Finset (Fin n) × Finset (Fin n))) : Set _) ⊆ Φ '' orbit C g := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard,
      Finset.subset_univ, true_and] at hp
    obtain ⟨σ1, h1⟩ := exists_perm_image_eq LF p.1 (by rw [hLFc, hp.1])
    obtain ⟨σ2, h2⟩ := exists_perm_image_eq RF p.2 (by rw [hRFc, hp.2])
    refine ⟨σOf hrig (σ1, σ2) g, ⟨(σ1, σ2), σOf hrig _, σOf_extends hrig _, rfl⟩, ?_⟩
    simp only [Φ, hMf_smul, leftPart_image, rightPart_image]
    refine Prod.ext ?_ ?_
    · rw [← h1]; ext i; simp [LF, hMdef]
    · rw [← h2]; ext i; simp [RF, hMdef]
  have hcard : n.choose kL * n.choose kR ≤ (orbit C g).ncard := by
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_image_le (f := Φ) (s := orbit C g) (Set.toFinite _)
    rw [Set.ncard_coe_finset, Finset.card_product,
      Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin] at h1
    exact h1.trans h2
  have horbg : (orbit C g).ncard < n.choose κ :=
    lt_of_le_of_lt (Finset.le_sup (f := fun g => (orbit C g).ncard) (Finset.mem_univ g)) horb
  have hlκ : kL + 1 ≤ κ := hgM.2.1
  have hrκ : kR + 1 ≤ κ := hgM.2.2
  have hk : kL + kR + 1 ≤ κ := by
    by_contra hcon
    have h1 := STNumerics.choose_le_of_between (n := n) (κ := κ) (r := kL + kR)
      (by omega) (by omega)
    have h2 := STNumerics.choose_add_le (n := n) (a := kL) (b := kR)
    omega
  refine ⟨M, hgM.1, ?_⟩
  rw [ncard_eq_leftPart_add_rightPart]
  omega

end Lax461425Proofs.STMinimal
