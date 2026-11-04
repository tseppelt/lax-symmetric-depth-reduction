import Lax461425Proofs.ComputedFormula
import Lax461425Proofs.TreeFormulaOrbit
import Lax461425Proofs.CircuitFamilyFacts

/-!
Multiplying a noninput-rooted formula by a private constant leaf, and inverse tagging it,
preserve its orbit bound. The proof pins both children under every extending automorphism
using their different input status, and restricts to their actual private occurrences.
-/

namespace Lax461425Proofs.ComputedFormulaOrbit

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies
open TreeFormulaCircuit TreeFormulaOperations ComputedFormula
open scoped Classical

variable {V K : Type*}

theorem isInput_map (l : GateLabel V K) (π : V → V) :
    (l.map π).IsInput ↔ l.IsInput := by cases l <;> rfl

/-- The direct children of an operation root are exactly the roots of its child trees. -/
theorem join_child_cases [CommSemiring K] {I : Type} [Fintype I] (T : I → Tree V K) (mul : Bool)
    (g : (join T mul).Gate)
    (hg : 0 < (circuit (join T mul)).wire (.inl ()) g) :
    ∃ i, g = TreeFormulaOrbit.embed T mul i (T i).out := by
  cases g with
  | inl u => simp [circuit, joinParent] at hg
  | inr p =>
    rcases p with ⟨i, g⟩
    have hp : (T i).parent g = none := by
      cases he : (T i).parent g with
      | none => rfl
      | some p => simp [circuit, joinParent, he] at hg
    have hout := (TreeFormulaSemantics.parent_eq_none_iff (T i) g).mp hp
    subst g
    exact ⟨i, rfl⟩

/-- In a binary operation, different root input status pins each child occurrence. -/
theorem binary_children_fixed [CommSemiring K] (T : Bool → Tree V K) (mul : Bool)
    (hfalse : ¬ ((T false).label (T false).out).IsInput)
    (htrue : ((T true).label (T true).out).IsInput)
    {σ : (join T mul).Gate ≃ (join T mul).Gate} {π : V → V}
    (hσ : Extends (circuit (join T mul)) σ π) (b : Bool) :
    σ (TreeFormulaOrbit.embed T mul b (T b).out) =
      TreeFormulaOrbit.embed T mul b (T b).out := by
  have hroot : σ (.inl ()) = .inl () := PatternsSupportBasic.extends_fixes_out hσ
  have hedge : 0 < (circuit (join T mul)).wire (.inl ())
      (TreeFormulaOrbit.embed T mul b (T b).out) := by
    simp [circuit, TreeFormulaOrbit.embed, joinParent, (T b).parent_out]
  have hedge' : 0 < (circuit (join T mul)).wire (.inl ())
      (σ (TreeFormulaOrbit.embed T mul b (T b).out)) := by
    rw [← hroot, hσ.2]
    exact hedge
  obtain ⟨j, hj⟩ := join_child_cases T mul _ hedge'
  have hl := hσ.1 (TreeFormulaOrbit.embed T mul b (T b).out)
  rw [hj] at hl
  have hl' : (T j).label (T j).out = ((T b).label (T b).out).map π := hl
  have hin : ((T j).label (T j).out).IsInput ↔ ((T b).label (T b).out).IsInput := by
    rw [hl', isInput_map]
  have heq : j = b := by
    cases j <;> cases b <;> first | rfl | exact (hfalse (hin.mpr htrue)).elim |
      exact (hfalse (hin.mp htrue)).elim
  subst j
  exact hj

section Semiring

variable [CommSemiring K] {A : Type*} [Group A] (ρ : A →* Equiv.Perm V)

/-- A private scalar multiplication preserves a noninput formula's all-automorphism bound. -/
theorem mul_const_orbitSize_le (c : K) (F : Formula V K)
    (hroot : ¬ (F.tree.label F.tree.out).IsInput) (B : ℕ) (hB : 1 ≤ B)
    (hF : orbitSize ρ (circuit F.tree) ≤ B) :
    orbitSize ρ (circuit (mul (const c) F).tree) ≤ B := by
  let T : Bool → Tree V K := fun b => (if b then const c else F).tree
  change orbitSize ρ (circuit (join T true)) ≤ B
  apply TreeFormulaOrbit.join_orbitSize_le T true ρ B hB
  · intro j
    cases j
    · exact hF
    · have hc := CircuitFamilyFacts.orbitSize_le_card ρ (circuit (const (V := V) c).tree)
      apply hc.trans
      change Fintype.card Unit ≤ B
      simpa using hB
  · intro γ τ hτ j
    apply binary_children_fixed T true ?_ ?_ hτ j
    · exact hroot
    · trivial

end Semiring

section Field

variable [Field K] {A : Type*} [Group A] (ρ : A →* Equiv.Perm V)

/-- An inverse-tagged formula has the same orbit bound as its noninput core. The value
of the tag is irrelevant to this structural bound. -/
theorem tag_orbitSize_le (t : K) (F : Formula V K)
    (hroot : ¬ (F.tree.label F.tree.out).IsInput) (B : ℕ) (hB : 1 ≤ B)
    (hF : orbitSize ρ (circuit F.tree) ≤ B) :
    orbitSize ρ (circuit (tag t F).tree) ≤ B := by
  change orbitSize ρ (circuit (mul (const t⁻¹) (mul (const t) F)).tree) ≤ B
  have hinner : ¬ ((mul (const t) F).tree.label (mul (const t) F).tree.out).IsInput := by
    change ¬ False
    trivial
  exact mul_const_orbitSize_le ρ t⁻¹ (mul (const t) F) hinner B hB
    (mul_const_orbitSize_le ρ t F hroot B hB hF)

end Field
end Lax461425Proofs.ComputedFormulaOrbit
