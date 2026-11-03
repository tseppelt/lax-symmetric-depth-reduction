import Lax461425.Circuits

/-!
---
title: Constant circuits
type: definition
---
One-gate circuits provide witnesses for zero-dimensional polynomial families and for zero
and constant polynomials. No variable input is required, even when the variable type is empty.
-/

namespace Lax461425.CircuitConstants

open Circuits

/-- A circuit consisting of one constant input, which is also its output. -/
def constant (V : Type*) {K : Type*} (c : K) : Circuit V K where
  Gate := Unit
  label := fun _ => .const c
  wire := fun _ _ => 0
  out := ()
  wire_eq_zero_of_isInput := by intros; rfl
  acyclic := by
    intro g h
    cases h with
    | single h => exact (Nat.lt_irrefl 0) h
    | tail _ h => exact (Nat.lt_irrefl 0) h
  reaches_out := by intro g; cases g; exact .refl

end Lax461425.CircuitConstants
