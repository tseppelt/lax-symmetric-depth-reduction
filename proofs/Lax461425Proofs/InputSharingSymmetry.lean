import Lax461425Proofs.InputSharingConstruction
import Lax461425.SymmetricFamilies

/-! Every old symmetry descends to the circuit with equally labelled inputs identified. -/

namespace Lax461425Proofs.InputSharingSymmetry

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies
open InputSharingConstruction
open scoped Classical

variable {V K : Type*} (C : Circuit V K)
variable (σ : C.Gate ≃ C.Gate) (π : Equiv.Perm V) (hσ : Extends C σ π)

include hσ in
theorem isInput_image (g : C.Gate) :
    (C.label (σ g)).IsInput ↔ (C.label g).IsInput := by
  rw [hσ.1 g]
  cases C.label g <;> rfl

noncomputable def inputEquiv : Input C ≃ Input C :=
  σ.subtypeEquiv fun g => (isInput_image C σ π hσ g).symm

noncomputable def internalEquiv : Internal C ≃ Internal C :=
  σ.subtypeEquiv fun g => (not_congr (isInput_image C σ π hσ g)).symm

theorem mapLabel_injective : Function.Injective (GateLabel.map (K := K) π) := by
  intro l m h
  cases l <;> cases m <;> simp_all [GateLabel.map, π.injective.eq_iff]

noncomputable def classEquiv : InputClass C ≃ InputClass C :=
  Quotient.congr (inputEquiv C σ π hσ) fun g h => by
    change C.label g.val = C.label h.val ↔ C.label (σ g.val) = C.label (σ h.val)
    rw [hσ.1 g.val, hσ.1 h.val]
    exact (mapLabel_injective π).eq_iff.symm

@[simp] theorem classEquiv_inputClass (g : Input C) :
    classEquiv C σ π hσ (inputClass C g) =
      inputClass C (inputEquiv C σ π hσ g) := rfl

theorem classLabel_classEquiv (q : InputClass C) :
    classLabel C (classEquiv C σ π hσ q) = (classLabel C q).map π := by
  induction q using Quotient.inductionOn with
  | h q => exact hσ.1 q.val

noncomputable def gateEquiv : Gate C ≃ Gate C :=
  Equiv.sumCongr (internalEquiv C σ π hσ) (classEquiv C σ π hσ)

theorem label_gateEquiv (g : Gate C) :
    label C (gateEquiv C σ π hσ g) = (label C g).map π := by
  cases g with
  | inl g => exact hσ.1 g.val
  | inr q => exact classLabel_classEquiv C σ π hσ q

theorem wire_gateEquiv (p g : Gate C) :
    wire C (gateEquiv C σ π hσ p) (gateEquiv C σ π hσ g) = wire C p g := by
  cases p with
  | inr p => rfl
  | inl p =>
    cases g with
    | inl g => exact hσ.2 p.val g.val
    | inr q =>
      change (∑ i : Input C, if inputClass C i = classEquiv C σ π hσ q then
        C.wire (σ p.val) i.val else 0) = _
      rw [← (inputEquiv C σ π hσ).sum_comp (fun i : Input C =>
        if inputClass C i = classEquiv C σ π hσ q then C.wire (σ p.val) i.val else 0)]
      apply Finset.sum_congr rfl
      intro i _
      change (if inputClass C (inputEquiv C σ π hσ i) = classEquiv C σ π hσ q then
        C.wire (σ p.val) (σ i.val) else 0) = _
      rw [← classEquiv_inputClass]
      simp only [(classEquiv C σ π hσ).injective.eq_iff, hσ.2]

theorem extends_circuit (hout : ¬ (C.label C.out).IsInput) :
    Extends (circuit C hout) (gateEquiv C σ π hσ) π :=
  ⟨label_gateEquiv C σ π hσ, wire_gateEquiv C σ π hσ⟩

theorem symmetric {G : Type*} [Group G] (ρ : G →* Equiv.Perm V)
    (hout : ¬ (C.label C.out).IsInput) (hC : Symmetric ρ C) :
    Symmetric ρ (circuit C hout) := by
  intro γ
  obtain ⟨σ, hσ⟩ := hC γ
  exact ⟨gateEquiv C σ (ρ γ) hσ, extends_circuit C σ (ρ γ) hσ hout⟩

end Lax461425Proofs.InputSharingSymmetry
