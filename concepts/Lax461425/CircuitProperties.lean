import Lax461425.Circuits

/-!
---
title: Formula and skew circuit properties
type: definition
---
Additional predicates on the existing circuit data.
-/

namespace Lax461425.CircuitProperties

open Circuits

open scoped Classical

/-- A formula has no parallel wires and may share inputs, while each noninput gate has
at most one outgoing wire. -/
def IsFormula {V K : Type*} (C : Circuit V K) : Prop :=
  (∀ g h, C.wire g h ≤ 1) ∧
    ∀ g, ¬ (C.label g).IsInput → ∑ h, C.wire h g ≤ 1

/-- At most one incoming wire of a product gate comes from a noninput gate. -/
def IsSkew {V K : Type*} (C : Circuit V K) : Prop :=
  ∀ g, C.label g = .mul → ∑ h, (if (C.label h).IsInput then 0 else C.wire g h) ≤ 1

end Lax461425.CircuitProperties
