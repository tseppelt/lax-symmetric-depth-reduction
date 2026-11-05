import Lax461425Proofs.Section6ABPForPatterns
import Lax461425Proofs.Section6ABPLinearCombination
import Lax461425Proofs.Section6ABPToSkewFamily
import Lax461425Proofs.Section6Families
import Lax461425.SymmetricABPCharacterisation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
Section 6: symmetric ABPs and symmetric skew circuits compute the same polynomial
families. The ABP constructions, symmetry, orbit bounds, pathwidth refinement, and general
homomorphism spanning are independently proved. The result has no unproved cited dependency
after resolving the theorem interfaces to their checked proofs.
-/

namespace Lax461425Proofs.Section6Characterisation

open Lax461425.SymmetricABPs Lax461425.SymmetricFamilies Lax461425.SymmetricClasses
open Lax461425.PatternWidths
open Lax461425.SymmetricVNP
open Lax461425.HomomorphismPolynomials
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

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

/--
---
conclusion: Lax461425.SymmetricABPCharacterisation.inSymVBP_of_inSymVS
---
Lemma 6.5. The reverse inclusion uses a single uniform pathwidth bound. The positive finite
exceptions and the zero-dimensional index are both represented by actual ABPs. -/
theorem skew_to_abp (f : MatrixFamily K) (hf : InSymVS f) : InSymVBP f := by
  obtain ⟨k, hk⟩ := Section6Families.uniform_pathwidth_span_of_inSymVS hf
  refine ⟨(fun n => (n + 1) ^ (k + 1)), ⟨1, k + 1, fun n => by simp⟩, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using Section6ConstantABP.exists_zero_dimension (f 0)
  · have hn' : 1 ≤ n := by omega
    obtain ⟨G, hG, hsym, hbound⟩ := exists_abp_of_mem_span hn' (f n) (hk n hn')
    exact ⟨G, hG, hsym, hbound.trans (Nat.pow_le_pow_left (by omega) (k + 1))⟩

/--
---
conclusion: Lax461425.SymmetricABPCharacterisation.characterisation
---
Theorem 6.3: equality of the polynomial-orbit family classes, from Lemmas 6.4 and 6.5. -/
theorem equivalence (f : MatrixFamily K) : InSymVBP f ↔ InSymVS f :=
  ⟨Lax461425.SymmetricABPCharacterisation.inSymVS_of_inSymVBP f,
    Lax461425.SymmetricABPCharacterisation.inSymVBP_of_inSymVS f⟩

end Lax461425Proofs.Section6Characterisation
