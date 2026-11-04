import Lax461425.Circuits

/-! Conditions for input normalisation: private inputs, and input siblings that stay distinct
when equally labelled input gates are identified. -/

namespace Lax461425Proofs.InputConditions

open Lax461425.Circuits

/-- Private inputs have one parent and one wire into it, and the output is internal. -/
def PrivateInputs {V K : Type*} (C : Circuit V K) : Prop :=
  ¬ (C.label C.out).IsInput ∧ ∀ g, (C.label g).IsInput →
    ∃ p, C.wire p g = 1 ∧ ∀ q, 0 < C.wire q g → q = p

/-- Identifying labels does not merge two input children of the same parent. -/
def InputSiblingsDistinct {V K : Type*} (C : Circuit V K) : Prop :=
  ∀ p g h, (C.label g).IsInput → (C.label h).IsInput →
    0 < C.wire p g → 0 < C.wire p h → C.label g = C.label h → g = h

end Lax461425Proofs.InputConditions
