import Lax461425.ABPsForPatterns
import Lax461425Proofs.Section6ABPLinearCombination
import Lax461425Proofs.Section6ABPToSkewFamily
import Lax461425Proofs.Section6Families
import Lax461425.SymmetricABPCharacterisation
import Lax461425.SkewFromABP
import Lax461425.SkewCircuitCharacterisation
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
branches are tagged by distinct constants before their endpoints are identified. -/
theorem exists_abp_of_mem_span {n k : ℕ} (hn : 1 ≤ n)
    (p : MatrixPolynomial n K)
    (hp : p ∈ Submodule.span K {q | ∃ F : Pattern, PathwidthLE k F ∧ hom K F n = q}) :
    ∃ G : ABP (Fin n × Fin n) K,
      G.Computes p ∧ G.IsMatrixSymmetric ∧ G.orbitSize ≤ n ^ (k + 1) := by
  obtain ⟨m, c, g, heq⟩ := Submodule.mem_span_set'.mp hp
  choose F hF hhom using fun i => (g i).2
  choose G hcomp hsym hbound using fun i =>
    Lax461425.ABPsForPatterns.exists_abp (K := K) hn (F i) (hF i)
  have hB : 1 ≤ n ^ (k + 1) := Nat.one_le_pow _ _ hn
  obtain ⟨H, hH, hsymH, hboundH⟩ :=
    Section6ABPSum.exists_linear_combination c G hsym _ hB hbound
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

/-- Families spanned by homomorphism polynomials of patterns of uniformly bounded pathwidth
have symmetric polynomial-orbit ABPs. The zero-dimensional index is represented by a
constant ABP. -/
theorem abp_of_pathwidth_span (f : MatrixFamily K) (hf : ∃ k : ℕ, ∀ n,
    f n ∈ Submodule.span K {q | ∃ F : Pattern, PathwidthLE k F ∧ hom K F n = q}) :
    InSymVBP f := by
  obtain ⟨k, hk⟩ := hf
  refine ⟨(fun n => (n + 1) ^ (k + 1)), ⟨1, k + 1, fun n => by simp⟩, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using Section6ConstantABP.exists_zero_dimension (f 0)
  · have hn' : 1 ≤ n := by omega
    obtain ⟨G, hG, hsym, hbound⟩ := exists_abp_of_mem_span hn' (f n) (hk n)
    exact ⟨G, hG, hsym, hbound.trans (Nat.pow_le_pow_left (by omega) (k + 1))⟩

/--
---
conclusion: Lax461425.SkewCircuitCharacterisation.characterisation
---
The forward direction is the pathwidth refinement of the support theorem, with finite
exceptions absorbed by homomorphism spanning and the zero-dimensional index spanned by the
empty pattern. The backward direction builds symmetric ABPs and converts them to skew
circuits (Lemma 6.4). -/
theorem symVS_characterisation (f : MatrixFamily K) :
    InSymVS f ↔ ∃ k : ℕ, ∀ n,
      f n ∈ Submodule.span K {q | ∃ F : Pattern, PathwidthLE k F ∧ hom K F n = q} :=
  ⟨Section6Families.pathwidth_span_of_inSymVS, fun hf =>
    Lax461425.SkewFromABP.inSymVS_of_inSymVBP f (abp_of_pathwidth_span f hf)⟩

/--
---
conclusion: Lax461425.SymmetricABPCharacterisation.inSymVBP_of_inSymVS
---
Lemma 6.5. The reverse inclusion uses a single uniform pathwidth bound. The zero-dimensional
index is represented by an actual ABP. -/
theorem skew_to_abp (f : MatrixFamily K) (hf : InSymVS f) : InSymVBP f :=
  abp_of_pathwidth_span f ((Lax461425.SkewCircuitCharacterisation.characterisation f).mp hf)

/--
---
conclusion: Lax461425.SymmetricABPCharacterisation.characterisation
---
Theorem 6.3: equality of the polynomial-orbit family classes, from Lemmas 6.4 and 6.5. -/
theorem equivalence (f : MatrixFamily K) : InSymVBP f ↔ InSymVS f :=
  ⟨Lax461425.SkewFromABP.inSymVS_of_inSymVBP f,
    Lax461425.SymmetricABPCharacterisation.inSymVBP_of_inSymVS f⟩

end Lax461425Proofs.Section6Characterisation
