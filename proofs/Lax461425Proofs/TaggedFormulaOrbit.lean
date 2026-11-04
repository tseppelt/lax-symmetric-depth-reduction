import Lax461425.SymmetricFamilies

/-!
Structural orbit bounds for the tagged formulas of Section 7. A unique constant input fixes
its sole parent under every extending automorphism. Directed ancestor paths are
preserved, allowing restriction to the private occurrences inside each fixed block.
-/

namespace Lax461425Proofs.TaggedFormulaOrbit

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies
open scoped Classical

variable {V K : Type*} {C : Circuit V K}

/-- A uniquely labelled constant is fixed by every extending automorphism. -/
theorem fixes_unique_constant {σ : C.Gate ≃ C.Gate} {π : V → V}
    (hσ : Extends C σ π) (c : K) (g : C.Gate) (hg : C.label g = .const c)
    (huniq : ∀ g', C.label g' = .const c → g' = g) : σ g = g := by
  apply huniq
  rw [hσ.1, hg]
  rfl

/-- Fixing a gate fixes its sole parent. -/
theorem fixes_unique_parent {σ : C.Gate ≃ C.Gate} {π : V → V}
    (hσ : Extends C σ π) {g p : C.Gate} (hg : σ g = g) (hp : 0 < C.wire p g)
    (huniq : ∀ p', 0 < C.wire p' g → p' = p) : σ p = p := by
  apply huniq
  have hwire : 0 < C.wire (σ p) (σ g) := by rw [hσ.2]; exact hp
  rwa [hg] at hwire

/-- Automorphisms map directed ancestor paths to directed ancestor paths. -/
theorem maps_path {σ : C.Gate ≃ C.Gate} {π : V → V} (hσ : Extends C σ π)
    {g r : C.Gate}
    (hpath : Relation.ReflTransGen (fun a b => 0 < C.wire b a) g r) :
    Relation.ReflTransGen (fun a b => 0 < C.wire b a) (σ g) (σ r) := by
  induction hpath with
  | refl => exact .refl
  | tail hab hstep ih =>
    apply ih.tail
    rwa [hσ.2]

end Lax461425Proofs.TaggedFormulaOrbit
