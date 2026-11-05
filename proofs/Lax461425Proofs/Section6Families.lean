import Lax461425.SymmetricABPs
import Lax461425.HomomorphismSpanning
import Lax461425Proofs.SymmetricPathDecomposition
import Lax461425Proofs.CircuitFacts
import Lax461425Proofs.SkewCircuitCharacterisation

/-!
Family-level bookkeeping for Section 6. The pathwidth direction is proved by refining
Tim's labelled-pattern machinery. Finite exceptional positive indices are
absorbed by a single uniform width bound, using the checked finite homomorphism expansion.
-/

namespace Lax461425Proofs.Section6Families

open Lax461425.SymmetricFamilies Lax461425.SymmetricClasses Lax461425.SymmetricABPs
open Lax461425.HomomorphismPolynomials Lax461425.MatrixSymmetry
open SymmetricPathDecomposition

variable {K : Type*} [Field K] [CharZero K] {f : MatrixFamily K}

theorem matrixInvariant_of_inSymVS (hf : InSymVS f) : ∀ n, MatrixInvariant (f n) := by
  obtain ⟨b, hb, hf⟩ := hf
  intro n γ
  obtain ⟨C, hcomp, hsym, hbound, hskew⟩ := hf n
  obtain ⟨σ, hσ⟩ := hsym γ
  exact CircuitFacts.rename_eq_of_computes_of_extends hcomp hσ

/-- Absorb the finite exceptions in the proved eventual pathwidth bound using the
independently proved homomorphism-spanning result. -/
theorem uniform_pathwidth_span_of_inSymVS (hf : InSymVS f) :
    ∃ k : ℕ, ∀ n, 1 ≤ n →
      f n ∈ Submodule.span K {q | ∃ F : Pattern, PathwidthLE k F ∧ hom K F n = q} := by
  have hinv := matrixInvariant_of_inSymVS hf
  obtain ⟨k, N, hN⟩ := Lax461425.SkewCircuitCharacterisation.eventually_pathwidth_span f hf
  refine ⟨max k (2 * N), ?_⟩
  intro n hn
  by_cases hlarge : N ≤ n
  · apply (Submodule.span_mono ?_) (hN n hlarge)
    rintro q ⟨F, hF, rfl⟩
    exact ⟨F, pathwidthLE_mono (Nat.le_max_left _ _) hF, rfl⟩
  · apply (Submodule.span_mono ?_)
      (Lax461425.HomomorphismSpanning.invariant_mem_span_hom hn (f n) (hinv n))
    rintro q ⟨F, hA, hB, rfl⟩
    have hF := pathwidthLE_two_mul hA hB
    exact ⟨F, pathwidthLE_mono (le_trans (by omega) (Nat.le_max_right k (2 * N))) hF, rfl⟩

end Lax461425Proofs.Section6Families
