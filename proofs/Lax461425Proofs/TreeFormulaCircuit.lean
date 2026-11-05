import Lax461425.CircuitProperties
import Lax461425.SymmetricFamilies
import Lax461425Proofs.RigidHeight

open Lax461425.CircuitProperties

/-!
A finite rooted tree with private input occurrences defines a formula circuit. The parent
map makes the absence of parallel wires and of shared internal gates explicit. This is the
graph interface for the tagged Boolean-witness formulas.
-/

namespace Lax461425Proofs.TreeFormulaCircuit

open Lax461425.Circuits
open scoped Classical

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Finite tree data with an increasing rank towards the distinguished root. -/
structure Tree (V K : Type*) where
  Gate : Type
  [fintypeGate : Fintype Gate]
  label : Gate → GateLabel V K
  parent : Gate → Option Gate
  out : Gate
  rank : Gate → ℕ
  parent_out : parent out = none
  parent_exists : ∀ g, g ≠ out → ∃ p, parent g = some p
  rank_parent : ∀ g p, parent g = some p → rank g < rank p
  input_leaf : ∀ g h, (label g).IsInput → parent h ≠ some g

attribute [instance] Tree.fintypeGate

variable {V K : Type*} (T : Tree V K)

private theorem parent_trans_rank {g h : T.Gate}
    (hp : Relation.TransGen (fun a b => T.parent a = some b) g h) : T.rank g < T.rank h := by
  induction hp with
  | single h => exact T.rank_parent _ _ h
  | tail hab hbc ih => exact ih.trans (T.rank_parent _ _ hbc)

private theorem parent_wellFounded : WellFounded (fun p g : T.Gate => T.parent g = some p) := by
  let R := Relation.TransGen (fun p g : T.Gate => T.parent g = some p)
  have htrans : IsTrans T.Gate R := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
  have hmap : ∀ {a b}, R a b → T.rank b < T.rank a := by
    intro a b hab
    induction hab with
    | single h => exact T.rank_parent _ _ h
    | tail hab hbc ih => exact (T.rank_parent _ _ hbc).trans ih
  have hirr : Std.Irrefl R := by
    constructor
    intro g hg
    exact (Nat.lt_irrefl _) (hmap hg)
  letI := htrans
  letI := hirr
  have hsub : Subrelation (fun p g : T.Gate => T.parent g = some p) R := fun h => .single h
  exact hsub.wf (Finite.wellFounded_of_trans_of_irrefl R)

private theorem reaches_root (g : T.Gate) :
    Relation.ReflTransGen (fun a b => T.parent a = some b) g T.out := by
  induction g using (parent_wellFounded T).induction with
  | h g ih =>
    by_cases hg : g = T.out
    · subst g
      exact .refl
    · obtain ⟨p, hp⟩ := T.parent_exists g hg
      have hstep : Relation.ReflTransGen (fun a b => T.parent a = some b) g p := .single hp
      exact hstep.trans (ih p hp)

/-- The circuit associated to rooted tree data. -/
@[reducible] noncomputable def circuit : Circuit V K where
  Gate := T.Gate
  label := T.label
  wire g h := if T.parent h = some g then 1 else 0
  out := T.out
  wire_eq_zero_of_isInput g h hg := if_neg (T.input_leaf g h hg)
  acyclic g := by
    intro hg
    have hp : Relation.TransGen (fun a b => T.parent a = some b) g g := by
      have hsub : (fun a b => 0 < if T.parent a = some b then 1 else 0) ≤
          (fun a b => T.parent a = some b) := by
        intro a b hab
        by_cases hp : T.parent a = some b
        · exact hp
        · simp [hp] at hab
      exact Relation.TransGen.mono hsub g g hg
    exact (Nat.lt_irrefl _) (parent_trans_rank T hp)
  reaches_out g := by
    have hsub : (fun a b => T.parent a = some b) ≤
        (fun a b => 0 < if T.parent a = some b then 1 else 0) := by
      intro a b hab
      simp [hab]
    exact Relation.ReflTransGen.mono hsub g T.out (reaches_root T g)

/-- Private input leaves are permitted, and every nonroot gate has one parent. -/
theorem isFormula : (IsFormula (circuit T)) := by
  constructor
  · intro g h
    simp only [circuit]
    split <;> omega
  · intro g hg
    change (∑ h, if T.parent g = some h then 1 else 0) ≤ 1
    cases hp : T.parent g with
    | none => simp [hp]
    | some p => simp [hp]

/-- A local bottom-up value assignment supplies genuine existing circuit semantics. -/
theorem computes_of_values [CommSemiring K] (q : T.Gate → MvPolynomial V K)
    (hvar : ∀ g x, T.label g = .var x → q g = MvPolynomial.X x)
    (hconst : ∀ g c, T.label g = .const c → q g = MvPolynomial.C c)
    (hadd : ∀ g, T.label g = .add → q g = ∑ h, (circuit T).wire g h • q h)
    (hmul : ∀ g, T.label g = .mul → q g = ∏ h, q h ^ (circuit T).wire g h) :
    (circuit T).Computes (q T.out) := by
  have hcomp : ∀ g, (circuit T).ComputesAt g (q g) := by
    intro g
    induction g using (RigidHeight.wellFounded_child (circuit T)).induction with
    | h g ih =>
      cases heq : T.label g with
      | var x =>
        rw [hvar g x heq]
        exact Circuit.ComputesAt.var heq
      | const c =>
        rw [hconst g c heq]
        exact Circuit.ComputesAt.const heq
      | add =>
        rw [hadd g heq]
        exact Circuit.ComputesAt.add q heq (fun h hh => ih h hh)
      | mul =>
        rw [hmul g heq]
        exact Circuit.ComputesAt.mul q heq (fun h hh => ih h hh)
  exact hcomp T.out

end Lax461425Proofs.TreeFormulaCircuit
