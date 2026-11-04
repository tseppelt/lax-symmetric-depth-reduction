import Lax461425.CircuitProperties
import Lax461425Proofs.PermanentCircuit
import Lax461425Proofs.CircuitFamilyFacts
import Lax461425Proofs.InputSharingConstants

open Lax461425.CircuitProperties

/-! The Ryser construction already identifies all equally labelled inputs. -/

namespace Lax461425Proofs.PermanentCircuit

open Lax461425.Circuits

theorem inputsIdentified {K : Type*} [CommRing K] {n : ℕ} (hn : 0 < n) :
    (InputsIdentified (circuit (K := K) hn)) := by
  intro g h hg he
  cases g <;> cases h <;> simp_all [circuit, label, GateLabel.IsInput]

end Lax461425Proofs.PermanentCircuit
