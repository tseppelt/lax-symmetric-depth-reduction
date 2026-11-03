import Lax461425.Circuits

/-!
---
title: Formula, skew, and input-sharing circuit properties
type: definition
---
Additional predicates on the existing circuit data. These include the paper's convention
that equally labelled input gates are identified, and conditions for input normalisation.
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

/-- The paper's input convention: equal labels identify input gates. -/
def InputsIdentified {V K : Type*} (C : Circuit V K) : Prop :=
  ∀ g h, (C.label g).IsInput → C.label g = C.label h → g = h

/-- Private inputs have one parent and one wire into it, and the output is internal. -/
def PrivateInputs {V K : Type*} (C : Circuit V K) : Prop :=
  ¬ (C.label C.out).IsInput ∧ ∀ g, (C.label g).IsInput →
    ∃ p, C.wire p g = 1 ∧ ∀ q, 0 < C.wire q g → q = p

/-- Identifying labels does not merge two input children of the same parent. -/
def InputSiblingsDistinct {V K : Type*} (C : Circuit V K) : Prop :=
  ∀ p g h, (C.label g).IsInput → (C.label h).IsInput →
    0 < C.wire p g → 0 < C.wire p h → C.label g = C.label h → g = h

end Lax461425.CircuitProperties
