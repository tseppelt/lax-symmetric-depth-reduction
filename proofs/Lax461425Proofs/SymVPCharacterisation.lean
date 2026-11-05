import Lax461425.SymmetricVPCharacterisation
import Lax461425.ReducedRigid
import Lax461425.SymmetricABPCharacterisation
import Lax461425Proofs.SymVPWidths
import Lax461425Proofs.PathRefinementBounds
import Lax461425Proofs.CircuitFacts
import Lax461425Proofs.ConverseOrbitSupport
import Lax461425Proofs.SymmetricPathDecomposition
import Lax461425Proofs.Section6Characterisation
import Lax461425Proofs.Section6ConstantABP
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
The characterisation of symmetric VP by homomorphism polynomials of patterns of bounded
treewidth, assembled from the bounded-depth characterisation, the support theorem,
rigidification, and the correspondence between treewidth and `Δ`-forestwidth.
-/

namespace Lax461425Proofs.SymVPCharacterisation

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425.SymmetricFamilies Lax461425.SymmetricClasses Lax461425.SymmetricABPs
open Lax461425.HomomorphismPolynomials Lax461425.PatternWidths Lax461425.Forestwidth
open SymVPWidths

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem matrixInvariant_of_inSymVP {f : MatrixFamily K} (hf : InSymVP f) (n : ℕ) :
    MatrixInvariant (f n) := by
  obtain ⟨b, -, hf⟩ := hf
  intro γ
  obtain ⟨C, hcomp, hsym, -, -⟩ := hf n
  obtain ⟨σ, hσ⟩ := hsym γ
  exact CircuitFacts.rename_eq_of_computes_of_extends hcomp hσ

/-- Families in `symVP` are spanned by bounded-treewidth homomorphism polynomials for all
sufficiently large `n`. -/
theorem eventually_treewidth_span (f : MatrixFamily K) (hf : InSymVP f) :
    ∃ k N : ℕ, ∀ n, N ≤ n →
      f n ∈ Submodule.span K {q | ∃ F : Pattern, TreewidthLE k F ∧ hom K F n = q} := by
  obtain ⟨b, ⟨c, d, hb⟩, hf⟩ := hf
  let κ := d + 3
  let N := max (max 20 (3 * κ + 2 * (κ - 1) + 1))
    (max (d + 3) (c * 2 ^ d * (d + 3) ^ (d + 3) + 1))
  refine ⟨κ - 1 - 1, N, ?_⟩
  intro n hn
  have hn20 : 20 ≤ n := (Nat.le_max_left _ _).trans ((Nat.le_max_left _ _).trans hn)
  have hlarge : 3 * κ + 2 * (κ - 1) + 1 ≤ n :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_left _ _).trans hn)
  have hchoose := PathRefinementBounds.polynomial_lt_choose c d n ((Nat.le_max_right _ _).trans hn)
  obtain ⟨C, hp, hsym, horb, -⟩ := hf n
  obtain ⟨C', hred, hsym', hp', -, -, horb'⟩ :=
    Lax461425.Rigidification.exists_reduced C hsym hp
  have horb'' : orbitSize C' < n.choose κ :=
    horb'.trans_lt (horb.trans_lt ((hb n).trans_lt hchoose))
  have hsize := Lax461425.SupportTheorem.supportSize_le hn20 (by omega : 3 * κ ≤ n + 2)
    C' hred hsym' horb''
  have hspan := (Lax461425.BoundedDepthCharacterisation.characterisation
    (Δ := max 1 (supportDepth C')) (le_max_left _ _) (by dsimp [κ]; omega : 2 ≤ κ - 1)
    (by omega) (f n)).1 ⟨C', hp', hred, hsym', hsize, le_max_right _ _⟩
  refine Submodule.span_mono ?_ hspan
  rintro q ⟨F, hF, rfl⟩
  exact ⟨F, Lax461425.TreewidthForestwidth.treewidthLE_of_forestwidthLE hF, rfl⟩

/-- Families in `symVP` are spanned by bounded-treewidth homomorphism polynomials. -/
theorem treewidth_span_of_inSymVP (f : MatrixFamily K) (hf : InSymVP f) :
    ∃ k : ℕ, ∀ n,
      f n ∈ Submodule.span K {q | ∃ F : Pattern, TreewidthLE k F ∧ hom K F n = q} := by
  obtain ⟨k, N, hN⟩ := eventually_treewidth_span f hf
  refine ⟨max k (2 * N), fun n => ?_⟩
  by_cases hlarge : N ≤ n
  · refine Submodule.span_mono ?_ (hN n hlarge)
    rintro q ⟨F, hF, rfl⟩
    exact ⟨F, treewidthLE_mono (Nat.le_max_left _ _) hF, rfl⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact mem_span_zero _ (f 0)
    · refine Submodule.span_mono ?_
        (Lax461425.HomomorphismSpanning.invariant_mem_span_hom hn (f n)
          (matrixInvariant_of_inSymVP hf n))
      rintro q ⟨F, hA, hB, rfl⟩
      exact ⟨F, treewidthLE_mono (le_trans (by omega) (Nat.le_max_right k (2 * N)))
        (treewidthLE_two_mul hA hB), rfl⟩

/-- Every family spanned by homomorphism polynomials has, on finitely many indices, symmetric
skew circuits: truncate the family and use symmetric ABPs. -/
theorem exists_circuits_below (f : MatrixFamily K) (k : ℕ)
    (hk : ∀ n, f n ∈ Submodule.span K {q | ∃ F : Pattern, TreewidthLE k F ∧ hom K F n = q})
    (N : ℕ) :
    ∃ c d : ℕ, ∀ n, n < N → ∃ C : Circuit (Fin n × Fin n) K,
      C.Computes (f n) ∧ IsMatrixSymmetric C ∧ orbitSize C ≤ c * (n + 1) ^ d := by
  classical
  let g : MatrixFamily K := fun n => if n < N then f n else 0
  have hg : InSymVBP g := by
    refine ⟨fun n => (n + 1) ^ (2 * N + 1), ⟨1, 2 * N + 1, fun n => by simp⟩, fun n => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨G, hG, hsym, hbound⟩ := Section6ConstantABP.exists_zero_dimension (g 0)
      exact ⟨G, hG, hsym, hbound.trans (Nat.one_le_pow _ _ (by omega))⟩
    · have hmem : g n ∈ Submodule.span K
          {q | ∃ F : Pattern, PathwidthLE (2 * N) F ∧ hom K F n = q} := by
        by_cases hnN : n < N
        · simp only [g, if_pos hnN]
          have hinv : MatrixInvariant (f n) := matrixInvariant_of_mem_span
            (by rintro q ⟨F, -, rfl⟩; exact hom_matrixInvariant K F n) (hk n)
          refine Submodule.span_mono ?_
            (Lax461425.HomomorphismSpanning.invariant_mem_span_hom hn (f n) hinv)
          rintro q ⟨F, hA, hB, rfl⟩
          exact ⟨F, SymmetricPathDecomposition.pathwidthLE_mono (by omega)
            (SymmetricPathDecomposition.pathwidthLE_two_mul hA hB), rfl⟩
        · simp only [g, if_neg hnN]
          exact Submodule.zero_mem _
      obtain ⟨G, hG, hsym, hbound⟩ :=
        Section6Characterisation.exists_abp_of_mem_span hn (g n) hmem
      exact ⟨G, hG, hsym, hbound.trans (Nat.pow_le_pow_left (by omega) _)⟩
  obtain ⟨b, ⟨c, d, hb⟩, hS⟩ := Lax461425.SymmetricABPCharacterisation.inSymVS_of_inSymVBP g hg
  refine ⟨c, d, fun n hn => ?_⟩
  obtain ⟨C, hC, hsym, horb, -⟩ := hS n
  refine ⟨C, ?_, hsym, horb.trans (hb n)⟩
  simpa only [g, if_pos hn] using hC

/-- Families spanned by bounded-treewidth homomorphism polynomials are in `symVP`. -/
theorem inSymVP_of_treewidth_span (f : MatrixFamily K) (k : ℕ)
    (hk : ∀ n, f n ∈ Submodule.span K {q | ∃ F : Pattern, TreewidthLE k F ∧ hom K F n = q}) :
    InSymVP f := by
  classical
  let k' := k + 2
  let N := 2 * k' + 1
  obtain ⟨c, d, hsmall⟩ := exists_circuits_below f k hk N
  refine ⟨fun n => c * (n + 1) ^ d + n ^ k', ⟨c + 1, d + k', fun n => ?_⟩, fun n => ?_⟩
  · have h1 : (n + 1) ^ d ≤ (n + 1) ^ (d + k') := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : n ^ k' ≤ (n + 1) ^ (d + k') :=
      (Nat.pow_le_pow_left (Nat.le_succ n) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
    calc c * (n + 1) ^ d + n ^ k' ≤ c * (n + 1) ^ (d + k') + (n + 1) ^ (d + k') :=
          Nat.add_le_add (Nat.mul_le_mul_left _ h1) h2
      _ = (c + 1) * (n + 1) ^ (d + k') := by ring
  by_cases hn : n < N
  · obtain ⟨C, hC, hsym, horb⟩ := hsmall n hn
    exact ⟨C, hC, hsym, horb.trans (Nat.le_add_right _ _), trivial⟩
  · obtain ⟨m, a, g, heq⟩ := Submodule.mem_span_set'.mp (hk n)
    choose F hF hhom using fun i => (g i).2
    choose Δ hΔ1 hΔ using fun i =>
      Lax461425.TreewidthForestwidth.exists_forestwidthLE_of_treewidthLE (hF i)
    let Δ₀ := max 1 (Finset.univ.sup Δ)
    have hspan : f n ∈ Submodule.span K
        {q | ∃ F : Pattern, ForestwidthLE Δ₀ (k' - 1) F ∧ hom K F n = q} := by
      rw [← heq]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      refine ⟨F i, forestwidthLE_mono ?_ (by omega) (hΔ i), hhom i⟩
      exact (Finset.le_sup (f := Δ) (Finset.mem_univ i)).trans (Nat.le_max_right _ _)
    obtain ⟨C, hC, hred, hsym, hsize, -⟩ :=
      (Lax461425.BoundedDepthCharacterisation.characterisation (Δ := Δ₀) (le_max_left _ _)
        (by omega : 2 ≤ k') (by omega : 2 * k' + 1 ≤ n) (f n)).2 hspan
    have horb := orbitSize_le_pow_of_supportSize_le
      (Lax461425.ReducedRigid.isRigid C hsym hred) (by omega) hsize
    exact ⟨C, hC, hsym, horb.trans (Nat.le_add_left _ _), trivial⟩

/--
---
conclusion: Lax461425.SymmetricVPCharacterisation.characterisation
---
`symVP` consists of the families spanned by homomorphism polynomials of patterns of bounded
treewidth. For large `n`, the support theorem bounds the support size of a rigidified circuit,
and the bounded-depth characterisation (with the support depth as depth bound) applies; for
the finitely many remaining `n`, matrix-invariance and the general homomorphism spanning theorem
suffice. Conversely, a common depth bound for the finitely many patterns in each linear
combination gives circuits via the bounded-depth characterisation, while finitely many
exceptional indices are covered by symmetric ABPs.
-/
theorem characterisation (f : MatrixFamily K) :
    InSymVP f ↔ ∃ k : ℕ, ∀ n,
      f n ∈ Submodule.span K {q | ∃ F : Pattern, TreewidthLE k F ∧ hom K F n = q} :=
  ⟨treewidth_span_of_inSymVP f, fun ⟨k, hk⟩ => inSymVP_of_treewidth_span f k hk⟩

end Lax461425Proofs.SymVPCharacterisation

#print axioms Lax461425Proofs.SymVPCharacterisation.characterisation
