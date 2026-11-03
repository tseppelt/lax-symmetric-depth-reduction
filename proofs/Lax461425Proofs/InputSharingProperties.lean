import Lax461425.CircuitProperties
import Lax461425Proofs.InputSharingConstruction
import Lax461425.SymmetricFamilies

open Lax461425.CircuitProperties

/-!
The input-only quotient does not increase gate count, preserves skewness, and preserves
the formula predicate when equal-labelled input siblings are absent.
-/

namespace Lax461425Proofs.InputSharingProperties

open Lax461425.Circuits InputSharingConstruction
open scoped Classical

variable {V K : Type*} (C : Circuit V K)

theorem card_gate_le (hout : ¬ (C.label C.out).IsInput) :
    Fintype.card (circuit C hout).Gate ≤ Fintype.card C.Gate :=
  Fintype.card_le_of_surjective (project C) (project_surjective C)

theorem sum_oldGate {M : Type*} [AddCommMonoid M] (f : C.Gate → M) :
    ∑ g, f g = (∑ g : Internal C, f g.val) + ∑ g : Input C, f g.val := by
  calc
    _ = ∑ g : Internal C ⊕ Input C, f ((oldGateEquiv C).symm g) :=
      ((oldGateEquiv C).symm.sum_comp f).symm
    _ = ∑ g : Internal C ⊕ Input C,
        Sum.elim (fun g => f g.val) (fun g => f g.val) g :=
      Finset.sum_congr rfl (fun g _ => by cases g <;> rfl)
    _ = _ := Fintype.sum_sum_type _

theorem prod_oldGate {M : Type*} [CommMonoid M] (f : C.Gate → M) :
    ∏ g, f g = (∏ g : Internal C, f g.val) * ∏ g : Input C, f g.val := by
  calc
    _ = ∏ g : Internal C ⊕ Input C, f ((oldGateEquiv C).symm g) :=
      ((oldGateEquiv C).symm.prod_comp f).symm
    _ = ∏ g : Internal C ⊕ Input C,
        Sum.elim (fun g => f g.val) (fun g => f g.val) g :=
      Finset.prod_congr rfl (fun g _ => by cases g <;> rfl)
    _ = _ := Fintype.prod_sum_type _

theorem wire_input_le_one (hC : (IsFormula C)) (hs : (InputSiblingsDistinct C))
    (p : Internal C) (q : InputClass C) : wire C (.inl p) (.inr q) ≤ 1 := by
  change (∑ g : Input C, if inputClass C g = q then C.wire p.val g.val else 0) ≤ 1
  by_cases hex : ∃ g : Input C, inputClass C g = q ∧ 0 < C.wire p.val g.val
  · obtain ⟨g, hg, hpos⟩ := hex
    rw [Finset.sum_eq_single g]
    · simpa only [hg, ↓reduceIte] using hC.1 p.val g.val
    · intro i hi hne
      by_cases hclass : inputClass C i = q
      · have hz : C.wire p.val i.val = 0 := by
          by_contra hw
          apply hne
          apply Subtype.ext
          exact hs p.val i.val g.val i.property g.property (Nat.pos_of_ne_zero hw) hpos
            ((inputClass_eq_iff C i g).mp (hclass.trans hg.symm))
        simp only [hclass, ↓reduceIte, hz]
      · simp only [hclass, ↓reduceIte]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  · have hz : ∀ g : Input C, (if inputClass C g = q then C.wire p.val g.val else 0) = 0 := by
      intro g
      by_cases hg : inputClass C g = q
      · have hw : C.wire p.val g.val = 0 := by
          by_contra hw
          exact hex ⟨g, hg, Nat.pos_of_ne_zero hw⟩
        simp [hg, hw]
      · simp [hg]
    simp only [hz, Finset.sum_const_zero, Nat.zero_le]

theorem outgoing_internal (g : Internal C) :
    (∑ p : Gate C, wire C p (.inl g)) = ∑ p : C.Gate, C.wire p g.val := by
  rw [sum_oldGate C, Fintype.sum_sum_type]
  simp only [wire, Finset.sum_const_zero, add_zero]
  have hz : ∀ p : Input C, C.wire p.val g.val = 0 :=
    fun p => C.wire_eq_zero_of_isInput p.val g.val p.property
  simp only [hz, Finset.sum_const_zero, add_zero]

theorem isFormula (hout : ¬ (C.label C.out).IsInput)
    (hC : (IsFormula C)) (hs : (InputSiblingsDistinct C)) : (IsFormula (circuit C hout)) := by
  constructor
  · intro p g
    cases p with
    | inr p => exact Nat.zero_le _
    | inl p =>
      cases g with
      | inl g => exact hC.1 p.val g.val
      | inr q => exact wire_input_le_one C hC hs p q
  · intro g hg
    cases g with
    | inl g =>
      change (∑ p : Gate C, wire C p (.inl g)) ≤ 1
      rw [outgoing_internal]
      exact hC.2 g.val g.property
    | inr q => exact (hg (classLabel_isInput C q)).elim

theorem isSkew (hout : ¬ (C.label C.out).IsInput) (hC : (IsSkew C)) :
    (IsSkew (circuit C hout)) := by
  intro p hp
  cases p with
  | inr q =>
    have hi := classLabel_isInput C q
    change classLabel C q = .mul at hp
    rw [hp] at hi
    exact hi.elim
  | inl p =>
    have hp' : C.label p.val = .mul := hp
    have hs := hC p.val hp'
    rw [sum_oldGate C] at hs
    have hi : (∑ g : Input C, if (C.label g.val).IsInput then 0 else C.wire p.val g.val) = 0 := by
      apply Finset.sum_eq_zero
      intro g hg
      exact if_pos g.property
    rw [hi, add_zero] at hs
    change (∑ g : Gate C, if (label C g).IsInput then 0 else wire C (.inl p) g) ≤ 1
    rw [Fintype.sum_sum_type]
    have hq : (∑ q : InputClass C, if (classLabel C q).IsInput then 0 else wire C (.inl p) (.inr q)) = 0 := by
      simp only [classLabel_isInput, ↓reduceIte, Finset.sum_const_zero]
    change (∑ g : Internal C, if (C.label g.val).IsInput then 0 else C.wire p.val g.val) +
      (∑ q : InputClass C, if (classLabel C q).IsInput then 0 else wire C (.inl p) (.inr q)) ≤ 1
    rw [hq, add_zero]
    exact hs

end Lax461425Proofs.InputSharingProperties
