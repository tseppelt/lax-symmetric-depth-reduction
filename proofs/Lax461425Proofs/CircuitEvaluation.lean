import Lax461425Proofs.CircuitFacts

/-! Every acyclic circuit has a unique polynomial value at every gate. -/

namespace Lax461425Proofs.CircuitEvaluation

open Lax461425.Circuits
open scoped Classical

variable {V K : Type*} [CommSemiring K]

theorem exists_value (C : Circuit V K) (g : C.Gate) :
    ∃ p, C.ComputesAt g p := by
  induction g using (RigidHeight.wellFounded_child C).induction with
  | _ g ih =>
    have hx : ∀ h : C.Gate, ∃ p : MvPolynomial V K,
        0 < C.wire g h → C.ComputesAt h p := by
      intro h
      by_cases hw : 0 < C.wire g h
      · obtain ⟨p, hp⟩ := ih h hw
        exact ⟨p, fun _ => hp⟩
      · exact ⟨0, fun hh => (hw hh).elim⟩
    choose q hq using hx
    cases hg : C.label g with
    | var x => exact ⟨_, Circuit.ComputesAt.var hg⟩
    | const c => exact ⟨_, Circuit.ComputesAt.const hg⟩
    | add => exact ⟨_, Circuit.ComputesAt.add q hg hq⟩
    | mul => exact ⟨_, Circuit.ComputesAt.mul q hg hq⟩

noncomputable def value (C : Circuit V K) (g : C.Gate) : MvPolynomial V K :=
  Classical.choose (exists_value C g)

theorem computesAt_value (C : Circuit V K) (g : C.Gate) :
    C.ComputesAt g (value C g) := Classical.choose_spec (exists_value C g)

theorem value_var (C : Circuit V K) {g : C.Gate} {x : V} (h : C.label g = .var x) :
    value C g = MvPolynomial.X x :=
  RigidComputes.computesAt_unique C g (computesAt_value C g) (.var h)

theorem value_const (C : Circuit V K) {g : C.Gate} {c : K} (h : C.label g = .const c) :
    value C g = MvPolynomial.C c :=
  RigidComputes.computesAt_unique C g (computesAt_value C g) (.const h)

theorem value_add (C : Circuit V K) {g : C.Gate} (h : C.label g = .add) :
    value C g = ∑ u, C.wire g u • value C u :=
  RigidComputes.computesAt_unique C g (computesAt_value C g)
    (.add (value C) h (fun u _ => computesAt_value C u))

theorem value_mul (C : Circuit V K) {g : C.Gate} (h : C.label g = .mul) :
    value C g = ∏ u, value C u ^ C.wire g u :=
  RigidComputes.computesAt_unique C g (computesAt_value C g)
    (.mul (value C) h (fun u _ => computesAt_value C u))

end Lax461425Proofs.CircuitEvaluation
