import Lax461425Proofs.Section6ABPForPatterns
import Lax461425Proofs.Section6ABPLinearCombination
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
Symmetric ABPs for linear combinations of bounded-pathwidth homomorphism polynomials, as in
`Section6Characterisation.exists_abp_of_mem_span` (restated here so that the symVP
characterisation depends only on the ABP constructions).
-/

namespace Lax461425Proofs.SymVPABP

open Lax461425.SymmetricABPs Lax461425.SymmetricFamilies Lax461425.SymmetricClasses
open Lax461425.PatternWidths
open Lax461425.HomomorphismPolynomials
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- Linear combinations of bounded-pathwidth homomorphism polynomials have symmetric
ABPs with the same orbit bound as the individual patterns. As in Lemma 6.5, the
layered branches are padded to distinct lengths before their endpoints are identified. -/
theorem exists_abp_of_mem_span {n k : ℕ} (hn : 1 ≤ n)
    (p : MatrixPolynomial n K)
    (hp : p ∈ Submodule.span K {q | ∃ F : Pattern, PathwidthLE k F ∧ hom K F n = q}) :
    ∃ G : ABP (Fin n × Fin n) K,
      G.Computes p ∧ G.IsMatrixSymmetric ∧ G.orbitSize ≤ n ^ (k + 1) := by
  obtain ⟨m, c, g, heq⟩ := Submodule.mem_span_set'.mp hp
  choose F hF hhom using fun i => (g i).2
  choose ℓ hw using fun i =>
    Section6ABPForPatterns.exists_layered_abp (K := K) hn (F i) (hF i)
  let M : ℕ := Finset.univ.sup ℓ + 1
  choose G hcomp hsym hbound L hlength using fun i => hw i (M * i.val)
  have hsmall (i : Fin m) : ℓ i < M := by
    have h := Finset.le_sup (f := ℓ) (Finset.mem_univ i)
    dsimp only [M]
    omega
  have hdistinct : Function.Injective (fun i => (L i).layer (G i).sink) := by
    intro i j hij
    change (L i).layer (G i).sink = (L j).layer (G j).sink at hij
    rw [hlength i, hlength j] at hij
    apply Fin.ext
    by_contra hne
    have hi := hsmall i
    have hj := hsmall j
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hgap := Nat.mul_le_mul_left M (show i.val + 1 ≤ j.val by omega)
      nlinarith
    · have hgap := Nat.mul_le_mul_left M (show j.val + 1 ≤ i.val by omega)
      nlinarith
  have hB : 1 ≤ n ^ (k + 1) := Nat.one_le_pow _ _ hn
  obtain ⟨H, hH, hsymH, hboundH⟩ :=
    Section6ABPSum.exists_linear_combination c G L hdistinct hsym _ hB hbound
  refine ⟨H, ?_, hsymH, hboundH⟩
  have hsum : (∑ i, MvPolynomial.C (c i) * (G i).polynomial) = p := by
    calc
      _ = ∑ i, c i • (g i).val := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [MvPolynomial.smul_eq_C_mul, ← hhom i]
        exact congrArg (fun q => MvPolynomial.C (c i) * q) (hcomp i)
      _ = p := heq
  exact hsum ▸ hH

end Lax461425Proofs.SymVPABP
