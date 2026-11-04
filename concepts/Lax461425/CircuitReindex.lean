import Lax461425.SymmetricFamilies

/-!
---
title: Reindexing circuit variables
type: definition
---
Changing variable names keeps every gate and wire. A variable equivalence conjugates the
specified action; it does not discard any extending automorphisms.
-/

namespace Lax461425.CircuitReindex

open Circuits

def mapLabel {V W K : Type*} (e : V ≃ W) : GateLabel V K → GateLabel W K
  | .var v => .var (e v)
  | .const c => .const c
  | .add => .add
  | .mul => .mul

/-- Relabel the inputs of a circuit along a variable equivalence. -/
def rename {V W K : Type*} (e : V ≃ W) (C : Circuit V K) : Circuit W K where
  Gate := C.Gate
  label g := mapLabel e (C.label g)
  wire := C.wire
  out := C.out
  wire_eq_zero_of_isInput g h hg := C.wire_eq_zero_of_isInput g h (by
    cases he : C.label g <;> simpa [mapLabel, he, GateLabel.IsInput] using hg)
  acyclic := C.acyclic
  reaches_out := C.reaches_out

/-- Conjugate a variable action along an equivalence of variable types. -/
def action {G V W : Type*} [Group G] (e : V ≃ W) (ρ : G →* Equiv.Perm V) :
    G →* Equiv.Perm W where
  toFun γ := e.permCongr (ρ γ)
  map_one' := by ext w; simp
  map_mul' γ δ := by ext w; simp [Equiv.Perm.mul_apply]

end Lax461425.CircuitReindex
