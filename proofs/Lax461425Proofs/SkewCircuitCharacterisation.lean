import Lax461425.SkewCircuitCharacterisation
import Lax461425Proofs.PathRefinementUnlabelled
import Lax461425Proofs.PathRefinementBounds
import Lax461425Proofs.PathRefinementRigid
import Lax461425Proofs.RigidReduced
import Lax461425Proofs.RigidSymmetric
import Lax461425Proofs.RigidOrbit
import Lax461425Proofs.SupportTheorem
import Lax461425Proofs.DixonMortimer

/-! The pathwidth refinement, reusing Tim's support theorem and labelled-pattern machinery. -/
namespace Lax461425Proofs.SkewCircuitCharacterisation

open Lax461425.Circuits Lax461425.CircuitProperties Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425.SymmetricFamilies Lax461425.SymmetricVNP
open Lax461425.SymmetricClasses Lax461425.SymmetricABPs Lax461425.HomomorphismPolynomials
open Lax461425.PatternWidths

/--
---
conclusion: Lax461425.SkewCircuitCharacterisation.mem_span_hom
---
The independent gate induction retains a path certificate at each step.
-/
theorem mem_span_hom {K : Type*} [Field K] [CharZero K] {k n : ℕ} (hk : 2 ≤ k)
    (hn : 2 * k + 1 ≤ n) (C : Circuit (Fin n × Fin n) K)
    (hred : C.IsReduced) (hsym : IsMatrixSymmetric C) (hsize : supportSize C ≤ k)
    (hskew : IsSkew C) {p : MatrixPolynomial n K} (hp : C.Computes p) :
    p ∈ Submodule.span K {q | ∃ F : Pattern, PathwidthLE (2 * k) F ∧ hom K F n = q} :=
  PathRefinementUnlabelled.mem_span_hom hk hn C hred hsym hsize hskew hp

/--
---
conclusion: Lax461425.SkewCircuitCharacterisation.eventually_pathwidth_span
---
Rigidification preserves skewness and does not enlarge orbits. Tim's support theorem
and binomial estimate give a constant support bound for all sufficiently large orders.
-/
theorem eventually_pathwidth_span {K : Type*} [Field K] [CharZero K]
    (f : MatrixFamily K) (hf : InSymVS f) :
    ∃ k N : ℕ, ∀ n, N ≤ n →
      f n ∈ Submodule.span K {q | ∃ F : Pattern, PathwidthLE k F ∧ hom K F n = q} := by
  obtain ⟨b, ⟨c, d, hb⟩, hf⟩ := hf
  let κ := d + 3
  let N := max (max 20 (3 * κ + 2 * (κ - 1) + 1))
    (max (d + 3) (c * 2 ^ d * (d + 3) ^ (d + 3) + 1))
  refine ⟨2 * (κ - 1), N, ?_⟩
  intro n hn
  have hn20 : 20 ≤ n := (Nat.le_max_left _ _).trans ((Nat.le_max_left _ _).trans hn)
  have hlarge : 3 * κ + 2 * (κ - 1) + 1 ≤ n :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_left _ _).trans hn)
  have hchoose := PathRefinementBounds.polynomial_lt_choose c d n ((Nat.le_max_right _ _).trans hn)
  obtain ⟨C, hp, hsym, horb, hs⟩ := hf n
  have hred := RigidReduced.isReduced_reduced C
  have hsym' := RigidSymmetric.isMatrixSymmetric_reduced C hsym
  have hs' := PathRefinementRigid.skew_reduced C hs
  have horb' : orbitSize (RigidConstruction.reduced C) < n.choose κ :=
    (RigidOrbit.orbitSize_reduced_le C hsym).trans_lt (horb.trans_lt ((hb n).trans_lt hchoose))
  have hsize := SupportTheorem.supportSize_le hn20 (by omega : 3 * κ ≤ n + 2)
    (RigidConstruction.reduced C) hred hsym' horb'
  exact mem_span_hom (by dsimp [κ]; omega) (by omega) _ hred hsym' hsize hs'
    (RigidComputes.computes_transfer C hp)

end Lax461425Proofs.SkewCircuitCharacterisation

#print axioms Lax461425Proofs.SkewCircuitCharacterisation.mem_span_hom
#print axioms Lax461425Proofs.SkewCircuitCharacterisation.eventually_pathwidth_span
#print axioms Lax461425Proofs.exists_fixingSubgroup_inf_alternatingGroup_le
#print axioms Lax461425Proofs.ReducedRigid.isRigid
