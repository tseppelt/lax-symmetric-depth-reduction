import Lax461425Proofs.BoundedDepthGlueComputes
import Lax461425Proofs.BoundedDepthGlueSymmetric
import Lax461425Proofs.BoundedDepthGlueSize
import Lax461425Proofs.BoundedDepthGlueSc
import Lax461425Proofs.RigidReduced
import Lax461425Proofs.RigidSymmetric
import Lax461425Proofs.RigidComputes
import Lax461425Proofs.ReducedRigid
import Lax461425.BoundedDepthCharacterisation
import Lax461425.CircuitsForPatterns
import Lax461425.PatternsFromCircuits
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
Final assembly, discharging the concept axiom
`Lax461425.BoundedDepthCharacterisation.characterisation`.
-/

namespace Lax461425Proofs

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425.HomomorphismPolynomials Lax461425.Forestwidth
open Lax461425Proofs.RigidConstruction

open scoped Classical

/-- **A circuit for a single pattern `F` of bounded forestwidth**, computing `hom K F n`,
whether or not `F` has an edge. -/
theorem exists_circuit_for_pattern {K : Type*} [Field K] [CharZero K] {Δ k n : ℕ} (hΔ : 1 ≤ Δ)
    (hk : 2 ≤ k) (hn : 2 * k + 1 ≤ n) (F : Pattern) (hF : ForestwidthLE Δ (k - 1) F) :
    ∃ C : Circuit (Fin n × Fin n) K, C.Computes (hom K F n) ∧ C.IsReduced ∧
      IsMatrixSymmetric C ∧ supportSize C ≤ k ∧ supportDepth C ≤ Δ := by
  obtain ⟨C, hC1, hC2, hC3, hC4, hC5, -, -, -⟩ :=
    Lax461425.CircuitsForPatterns.exists_circuit (K := K) hΔ hk hn F hF
  exact ⟨C, hC1, hC2, hC3, hC4, hC5⟩

/--
---
conclusion: Lax461425.BoundedDepthCharacterisation.characterisation
---
The characterisation of bounded-depth matrix-symmetric circuits.

The forward direction (1 → 2) is the concept `PatternsFromCircuits.mem_span_hom` directly.

For the backward direction (2 → 1), `Submodule.mem_span_set'` writes `p = ∑ i, f i • hom K
(F i) n` for finitely many patterns `F i` with `ForestwidthLE Δ (k - 1) (F i)`. For each `i`, a
circuit `D i` computing `hom K (F i) n` is obtained from the concept
`CircuitsForPatterns.exists_circuit`; it is reduced, matrix-symmetric, with support size `≤ k`
and support depth `≤ Δ`. These are glued (`BoundedDepthGlueCircuit.glueCircuit`) by scaling each
block's output by `f i` (via a new `mul`-gate and a new `const (f i)` input gate) and summing
all of these via a new output `add`-gate; the glue circuit computes `∑ i, f i • hom K (F i) n =
p` (`BoundedDepthGlueComputes.glueCircuit_computes`) and is matrix-symmetric
(`BoundedDepthGlueSymmetric.glueCircuit_isMatrixSymmetric`), since every block is. Rigidifying
it (`RigidConstruction.reduced`) yields a reduced, matrix-symmetric circuit computing `p`
(`RigidReduced.isReduced_reduced`, `RigidSymmetric.isMatrixSymmetric_reduced`,
`RigidComputes.computes_transfer`) with support size `≤ k`
(`BoundedDepthGlueSize.glueCircuit_reduced_supportSize_le`) and support depth `≤ Δ`
(`BoundedDepthGlueSc.glueCircuit_reduced_supportDepth_le`), the latter via a potential built
from each block's own `sc`, since every glue gate has empty minimal support and every block's
own minimal support is unaffected by rigidifying the glue circuit as a whole
(`BoundedDepthEmbed.embed_equiv_eq`, `BoundedDepthReducedFormula.reduced_σOf_eq`).

The concept `Rigidification.exists_reduced` is deliberately not used: it does not preserve support
size or support depth, so the proof rigidifies with `RigidConstruction.reduced` and tracks the
supports of the block gates through it directly. -/
theorem characterisation {K : Type*} [Field K] [CharZero K] {Δ k n : ℕ} (hΔ : 1 ≤ Δ)
    (hk : 2 ≤ k) (hn : 2 * k + 1 ≤ n) (p : MvPolynomial (Fin n × Fin n) K) :
    (∃ C : Circuit (Fin n × Fin n) K,
        C.Computes p ∧ C.IsReduced ∧ IsMatrixSymmetric C ∧
          supportSize C ≤ k ∧ supportDepth C ≤ Δ) ↔
      p ∈ Submodule.span K {q | ∃ F : Pattern, ForestwidthLE Δ (k - 1) F ∧ hom K F n = q} := by
  constructor
  · rintro ⟨C, hCp, hCred, hCsym, hCss, hCsd⟩
    exact Lax461425.PatternsFromCircuits.mem_span_hom hΔ hk hn C hCred hCsym hCss hCsd hCp
  · intro hp
    obtain ⟨m, fcoef, g, hpeq⟩ := Submodule.mem_span_set'.mp hp
    choose F hFfw hFhom using fun i => (g i).2
    choose D hDcomp hDred hDsym hDss hDsd using
      fun i => exists_circuit_for_pattern (K := K) hΔ hk hn (F i) (hFfw i)
    have hsymE : IsMatrixSymmetric (glueCircuit D fcoef) :=
      glueCircuit_isMatrixSymmetric D fcoef hDred hDsym
    have hredRed : (reduced (glueCircuit D fcoef)).IsReduced := RigidReduced.isReduced_reduced _
    have hsymRed : IsMatrixSymmetric (reduced (glueCircuit D fcoef)) :=
      RigidSymmetric.isMatrixSymmetric_reduced _ hsymE
    have hrigRed : IsRigid (reduced (glueCircuit D fcoef)) :=
      Lax461425Proofs.ReducedRigid.isRigid hsymRed hredRed
    have hssE : supportSize (reduced (glueCircuit D fcoef)) ≤ k :=
      glueCircuit_reduced_supportSize_le D fcoef hDred hDsym hrigRed hDss
    have hcomp : (glueCircuit D fcoef).Computes p := by
      have hc := glueCircuit_computes D fcoef (fun i => hDcomp i)
      rwa [show (∑ i, fcoef i • hom K (F i) n) = p by
        rw [← hpeq]; exact Finset.sum_congr rfl (fun i _ => by rw [hFhom i])] at hc
    refine ⟨reduced (glueCircuit D fcoef), RigidComputes.computes_transfer _ hcomp, hredRed,
      hsymRed, hssE, ?_⟩
    exact glueCircuit_reduced_supportDepth_le D fcoef hDred hDsym hrigRed hssE hDss (by omega) hDsd

end Lax461425Proofs
