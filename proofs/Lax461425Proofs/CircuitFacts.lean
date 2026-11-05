import Lax461425.Circuits
import Lax461425Proofs.PatternsInductionEquivariant
import Lax461425Proofs.PatternsSupportBasic
import Lax461425Proofs.RigidComputes

/-!
Shared circuit facts for Sections 6 and 7. These use the existing circuit semantics and
automorphisms, without introducing assumptions about computation or symmetry.
-/

namespace Lax461425Proofs.CircuitConstants

open Lax461425.Circuits

/-- A circuit consisting of one constant input, which is also its output. One-gate circuits
provide witnesses for zero-dimensional polynomial families and for zero and constant
polynomials; no variable input is required, even when the variable type is empty. -/
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

end Lax461425Proofs.CircuitConstants

namespace Lax461425Proofs.CircuitFacts

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425Proofs.CircuitConstants

variable {V K : Type*}

/-- A constant circuit computes its label. -/
theorem constant_computes [CommSemiring K] (c : K) :
    (constant V c).Computes (MvPolynomial.C c) :=
  Circuit.ComputesAt.const rfl

/-- Every variable renaming extends to the identity automorphism of a constant circuit. -/
theorem constant_extends (c : K) (π : V → V) :
    Extends (constant V c) (Equiv.refl _) π := by
  constructor <;> intros <;> rfl

/-- A polynomial computed by a circuit is fixed by any variable renaming extending to an
automorphism of that circuit. The output is fixed because all gates reach it. -/
theorem rename_eq_of_computes_of_extends [CommSemiring K] {C : Circuit V K}
    {p : MvPolynomial V K} (hp : C.Computes p) {σ : C.Gate ≃ C.Gate} {π : V → V}
    (hσ : Extends C σ π) : MvPolynomial.rename π p = p := by
  have hcomp := PatternsInductionEquivariant.computesAt_rename C hσ hp
  rw [PatternsSupportBasic.extends_fixes_out hσ] at hcomp
  exact RigidComputes.computesAt_unique C C.out hcomp hp

/-- Local gate equations determine a valid computation throughout a circuit. The proof
uses acyclicity; no evaluation or correctness fact is assumed. -/
theorem computesAt_of_local_values [CommSemiring K] (C : Circuit V K)
    (q : C.Gate → MvPolynomial V K)
    (hvar : ∀ g x, C.label g = .var x → q g = MvPolynomial.X x)
    (hconst : ∀ g c, C.label g = .const c → q g = MvPolynomial.C c)
    (hadd : ∀ g, C.label g = .add → q g = ∑ h, C.wire g h • q h)
    (hmul : ∀ g, C.label g = .mul → q g = ∏ h, q h ^ C.wire g h) :
    ∀ g, C.ComputesAt g (q g) := by
  intro g
  induction g using (RigidHeight.wellFounded_child C).induction with
  | _ g ih =>
    cases hg : C.label g with
    | var x => rw [hvar g x hg]; exact Circuit.ComputesAt.var hg
    | const c => rw [hconst g c hg]; exact Circuit.ComputesAt.const hg
    | add =>
      rw [hadd g hg]
      exact Circuit.ComputesAt.add q hg (fun h hh => ih h hh)
    | mul =>
      rw [hmul g hg]
      exact Circuit.ComputesAt.mul q hg (fun h hh => ih h hh)

end Lax461425Proofs.CircuitFacts
