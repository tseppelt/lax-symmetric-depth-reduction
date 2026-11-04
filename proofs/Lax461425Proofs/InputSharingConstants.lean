import Lax461425.CircuitProperties
import Lax461425.InputSharing
import Lax461425Proofs.CircuitFamilyFacts

open Lax461425.CircuitProperties

namespace Lax461425Proofs.CircuitFamilyFacts

theorem constant_inputsIdentified {V K : Type*} (c : K) :
    (InputsIdentified (Lax461425.CircuitConstants.constant V c)) := by
  intro g h _ _
  exact @Subsingleton.elim Unit inferInstance g h

end Lax461425Proofs.CircuitFamilyFacts
