import Lax461425Proofs.PathRefinementInduction
import Lax461425Proofs.PathRefinementPathwidth
import Lax461425Proofs.PatternsFromCircuits

/-! Evaluating Tim's labelled witnesses with the added path certificate. -/
namespace Lax461425Proofs.PathRefinementUnlabelled
open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425.HomomorphismPolynomials Lax461425.SymmetricABPs
open PatternsSupportAction PatternsSupportBasic PatternsSupportDepth PatternsInductionSetup
open PatternsLabelledOps PatternsLabelledBasic PatternsFromCircuits PathRefinementClass
open RigidComputes ReducedRigid
open scoped Classical

theorem eval_mem_span_hom {K : Type*} [Field K] {Δ k n ℓ r : ℕ} (hℓ : ℓ = 0) (hr : r = 0)
    {φ : (Fin ℓ → Fin n) → (Fin r → Fin n) → MvPolynomial (Fin n × Fin n) K}
    (hφ : φ ∈ spanLinear K Δ k n (Finset.univ : Finset (Fin ℓ ⊕ Fin r))) (v : Fin ℓ → Fin n)
    (w : Fin r → Fin n) :
    φ v w ∈ Submodule.span K {q | ∃ F : Pattern, PathwidthLE (2 * k) F ∧ hom K F n = q} := by
  subst hℓ
  subst hr
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨G, hG, rfl⟩ := hx
      rw [labelledHom_eq_hom_of_zero]
      apply Submodule.subset_span
      refine ⟨G.F, ?_, rfl⟩
      obtain ⟨D⟩ := hG.1
      exact PathRefinementPathwidth.pathwidthLE D.tree D.schedule
  | zero => exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      have : (x + y) v w = x v w + y v w := rfl
      rw [this]
      exact Submodule.add_mem _ ihx ihy
  | smul c x _ ih =>
      have : (c • x) v w = c • x v w := rfl
      rw [this]
      exact Submodule.smul_mem _ c ih

theorem mem_span_hom {K : Type*} [Field K] [CharZero K] {k n : ℕ} (hk : 2 ≤ k)
    (hn : 2 * k + 1 ≤ n) (C : Circuit (Fin n × Fin n) K)
    (hred : C.IsReduced) (hsym : IsMatrixSymmetric C) (hsize : supportSize C ≤ k)
    (hskew : Lax461425.CircuitProperties.IsSkew C) {p : MvPolynomial (Fin n × Fin n) K} (hp : C.Computes p) :
    p ∈ Submodule.span K {q | ∃ F : Pattern, PathwidthLE (2 * k) F ∧ hom K F n = q} := by
  have hrig : IsRigid C := ReducedRigid.isRigid hsym hred
  have hn2 : 2 * supportSize C < n := by omega
  obtain ⟨φ, hφmem, hφeval⟩ := PathRefinementInduction.exists_phi hskew hred hsym hk hn hsize hrig hn2 C.out
  have hsupOut : supOf hrig hn2 C.out = (∅ : Set (Fin n ⊕ Fin n)) := by
    rw [supOf_eq_minSupport, minSupport_out]
  have hleftCard0 : leftCard hrig hn2 C.out = 0 := by
    show (leftPart (supOf hrig hn2 C.out)).ncard = 0
    rw [hsupOut]; simp [leftPart]
  have hrightCard0 : rightCard hrig hn2 C.out = 0 := by
    show (rightPart (supOf hrig hn2 C.out)).ncard = 0
    rw [hsupOut]; simp [rightPart]
  have hpeq : p = φ (leftEnum hrig hn2 C.out) (rightEnum hrig hn2 C.out) :=
    computesAt_unique C C.out hp hφeval
  rw [hpeq]
  exact eval_mem_span_hom hleftCard0 hrightCard0 hφmem _ _

end Lax461425Proofs.PathRefinementUnlabelled
