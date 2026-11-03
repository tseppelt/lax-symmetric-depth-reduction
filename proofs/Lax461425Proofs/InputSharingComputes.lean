import Lax461425Proofs.InputSharingConstruction
import Lax461425Proofs.CircuitEvaluation

/-! Identifying equal inputs preserves literal sum/product circuit computation. -/

namespace Lax461425Proofs.InputSharingComputes

open Lax461425.Circuits InputSharingConstruction
open scoped Classical BigOperators

variable {V K : Type*} (C : Circuit V K)

theorem incoming_sum {M : Type*} [AddCommMonoid M] (p : Internal C) (q : Gate C → M) :
    (∑ h : Gate C, wire C (.inl p) h • q h) =
      ∑ h : C.Gate, C.wire p.val h • q (project C h) := by
  have hsplit : (∑ h : C.Gate, C.wire p.val h • q (project C h)) =
      (∑ h : Internal C, C.wire p.val h.val • q (.inl h)) +
      ∑ h : Input C, C.wire p.val h.val • q (.inr (inputClass C h)) := by
    rw [← (oldGateEquiv C).symm.sum_comp (fun h => C.wire p.val h • q (project C h))]
    simp [Fintype.sum_sum_type, oldGateEquiv]
  rw [hsplit, Fintype.sum_sum_type]
  congr 1
  change (∑ a : InputClass C,
    (∑ h : Input C, if inputClass C h = a then C.wire p.val h.val else 0) • q (.inr a)) = _
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  simp

theorem incoming_prod {M : Type*} [CommMonoid M] (p : Internal C) (q : Gate C → M) :
    (∏ h : Gate C, q h ^ wire C (.inl p) h) =
      ∏ h : C.Gate, q (project C h) ^ C.wire p.val h := by
  have hsplit : (∏ h : C.Gate, q (project C h) ^ C.wire p.val h) =
      (∏ h : Internal C, q (.inl h) ^ C.wire p.val h.val) *
      ∏ h : Input C, q (.inr (inputClass C h)) ^ C.wire p.val h.val := by
    rw [← (oldGateEquiv C).symm.prod_comp (fun h => q (project C h) ^ C.wire p.val h)]
    simp [Fintype.prod_sum_type, oldGateEquiv]
  rw [hsplit, Fintype.prod_sum_type]
  congr 1
  change (∏ a : InputClass C,
    q (.inr a) ^ (∑ h : Input C, if inputClass C h = a then C.wire p.val h.val else 0)) = _
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro h _
  simp

variable [CommSemiring K] (hout : ¬ (C.label C.out).IsInput)

theorem computesAt_project {g : C.Gate} {p : MvPolynomial V K}
    (hp : C.ComputesAt g p) : (circuit C hout).ComputesAt (project C g) p := by
  let D := circuit C hout
  let q := fun g : C.Gate => CircuitEvaluation.value D (project C g)
  have hq : ∀ g, C.ComputesAt g (q g) := by
    apply CircuitFacts.computesAt_of_local_values C q
    · intro g x hg
      exact CircuitEvaluation.value_var D ((label_project C g).trans hg)
    · intro g c hg
      exact CircuitEvaluation.value_const D ((label_project C g).trans hg)
    · intro g hg
      have hi : ¬ (C.label g).IsInput := by simp [hg, GateLabel.IsInput]
      change CircuitEvaluation.value D (project C g) = _
      rw [CircuitEvaluation.value_add D ((label_project C g).trans hg)]
      rw [project_internal C ⟨g, hi⟩]
      exact incoming_sum C ⟨g, hi⟩ (CircuitEvaluation.value D)
    · intro g hg
      have hi : ¬ (C.label g).IsInput := by simp [hg, GateLabel.IsInput]
      change CircuitEvaluation.value D (project C g) = _
      rw [CircuitEvaluation.value_mul D ((label_project C g).trans hg)]
      rw [project_internal C ⟨g, hi⟩]
      exact incoming_prod C ⟨g, hi⟩ (CircuitEvaluation.value D)
  have he := RigidComputes.computesAt_unique C g (hq g) hp
  exact he ▸ CircuitEvaluation.computesAt_value D (project C g)

theorem computes {p : MvPolynomial V K} (hp : C.Computes p) :
    (circuit C hout).Computes p := by
  have h := computesAt_project C hout hp
  change (circuit C hout).ComputesAt (.inl ⟨C.out, hout⟩) p
  simpa only [project_internal C ⟨C.out, hout⟩] using h

end Lax461425Proofs.InputSharingComputes
