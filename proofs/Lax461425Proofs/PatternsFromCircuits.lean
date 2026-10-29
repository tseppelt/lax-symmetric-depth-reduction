import Lax461425Proofs.PatternsInductionMain
import Lax461425Proofs.PatternsLabelledUnlabelled
import Lax461425Proofs.ReducedRigid
import Lax461425.PatternsFromCircuits

/-!
Discharges the concept axiom `Lax461425.PatternsFromCircuits.mem_span_hom` (thm:patterns),
via `lem:induction` (`PatternsInductionMain.exists_phi`).
-/

namespace Lax461425Proofs.PatternsFromCircuits

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425.HomomorphismPolynomials Lax461425.Forestwidth
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open Lax461425Proofs.PatternsSupportDepth Lax461425Proofs.PatternsInductionSetup
open Lax461425Proofs.PatternsInductionMain
open Lax461425Proofs.PatternsRestrictedMono Lax461425Proofs.PatternsLabelledOps
open Lax461425Proofs.PatternsLabelledBasic Lax461425Proofs.PatternsLabelledUnlabelled
open Lax461425Proofs.RigidComputes Lax461425Proofs.ReducedRigid
open scoped Classical

/-- **`labelledHom` at the trivial `(0,0)` arity is the unlabelled homomorphism polynomial.**
The defining `if`-condition of `labelledHom` quantifies over `Fin 0`, hence is vacuously true,
collapsing the sum to exactly `hom K G.F n`. -/
theorem labelledHom_eq_hom_of_zero {K : Type*} [CommSemiring K] (G : LabelledPattern 0 0) (n : ℕ)
    (v w : Fin 0 → Fin n) : labelledHom K G n v w = hom K G.F n := by
  show (∑ hA : G.F.A → Fin n, ∑ hB : G.F.B → Fin n,
      if (∀ i : Fin 0, hA (G.a i) = v i) ∧ (∀ j : Fin 0, hB (G.b j) = w j) then
        (∏ x, ∏ y, MvPolynomial.X (hA x, hB y) ^ G.F.mult x y : MvPolynomial (Fin n × Fin n) K)
      else 0) = hom K G.F n
  have hcond : ∀ hA : G.F.A → Fin n, ∀ hB : G.F.B → Fin n,
      ((∀ i : Fin 0, hA (G.a i) = v i) ∧ (∀ j : Fin 0, hB (G.b j) = w j)) := fun _ _ =>
    ⟨fun i => i.elim0, fun j => j.elim0⟩
  refine Finset.sum_congr rfl (fun hA _ => Finset.sum_congr rfl (fun hB _ => ?_))
  rw [if_pos (hcond hA hB)]

/-- **`G` is the `(0,0)`-labelling of its own pattern.** Both label maps out of `Fin 0` are
forced to equal `Fin.elim0` (the unique function with that domain). -/
theorem eq_ofPattern (G : LabelledPattern 0 0) : G = ofPattern G.F := by
  cases G with
  | mk F a b =>
    congr 1
    · exact Subsingleton.elim a Fin.elim0
    · exact Subsingleton.elim b Fin.elim0

/-- **Every member of `𝔗^{Δ,k}_n(ℓ,r)`, for `ℓ = r = 0`, evaluated at any point, lies in the
target span.** Stated with `ℓ = r = 0` as hypotheses (rather than literal `Fin 0`s) so it can be
applied directly to `leftCard hrig hn C.out`/`rightCard hrig hn C.out` via `subst`. -/
theorem eval_mem_span_hom {K : Type*} [Field K] {Δ k n ℓ r : ℕ} (hℓ : ℓ = 0) (hr : r = 0)
    (hΔ : 1 ≤ Δ) (hk1 : 1 ≤ k)
    {φ : (Fin ℓ → Fin n) → (Fin r → Fin n) → MvPolynomial (Fin n × Fin n) K}
    (hφ : φ ∈ span𝔗P K Δ k n (Finset.univ : Finset (Fin ℓ ⊕ Fin r))) (v : Fin ℓ → Fin n)
    (w : Fin r → Fin n) :
    φ v w ∈ Submodule.span K {q | ∃ F : Pattern, ForestwidthLE Δ (k - 1) F ∧ hom K F n = q} := by
  subst hℓ
  subst hr
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨G, hG, rfl⟩ := hx
      rw [labelledHom_eq_hom_of_zero]
      apply Submodule.subset_span
      refine ⟨G.F, ?_, rfl⟩
      rw [← inClass_ofPattern_iff hΔ hk1, ← eq_ofPattern G]
      exact hG.1
  | zero => exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      have : (x + y) v w = x v w + y v w := rfl
      rw [this]
      exact Submodule.add_mem _ ihx ihy
  | smul c x _ ih =>
      have : (c • x) v w = c • x v w := rfl
      rw [this]
      exact Submodule.smul_mem _ c ih

/--
---
conclusion: Lax461425.PatternsFromCircuits.mem_span_hom
---
**`mem_span_hom`.** A polynomial computed by a reduced matrix-symmetric circuit of support
size `≤ k` and support depth `≤ Δ` is a linear combination of homomorphism polynomials of
patterns of `Δ`-forestwidth at most `k - 1`.

Applies `PatternsInductionMain.exists_phi` (`lem:induction`) at `g := C.out`. Since
`minSupport C C.out = ∅` (`PatternsSupportBasic.minSupport_out`), `supOf hrig hn C.out = ∅` too
(`supOf_eq_minSupport`), so `leftCard hrig hn C.out = rightCard hrig hn C.out = 0`; the witness
`φ`, lifted from depth `sc C C.out` to `Δ` (`sc_le_supportDepth`, `hdepth`, `span𝔗P_mono`), is
evaluated at the (unique, since the arities are `0`) canonical enumerations, giving `p`
(`computesAt_unique`, since `C.Computes p` unfolds to `C.ComputesAt C.out p`). Every generator
`labelledHom K G n` of `span𝔗P K Δ k n (Finset.univ : Finset (Fin 0 ⊕ Fin 0))`, evaluated at any
point, is exactly the *unlabelled* homomorphism polynomial `hom K G.F n`
(`labelledHom_eq_hom_of_zero`, since the defining `if`-condition of `labelledHom` is vacuously
true at arity `(0,0)`), and `G ∈ 𝒯^{Δ,k}(0,0)` is exactly `ForestwidthLE Δ (k - 1) G.F`
(`PatternsLabelledUnlabelled.inClass_ofPattern_iff`, using `G = ofPattern G.F` since both label
maps out of `Fin 0` are forced to be `Fin.elim0`); `eval_mem_span_hom` packages this as a
`Submodule.span_induction` argument, stated for an arbitrary arity `(ℓ, r)` with `ℓ = r = 0` as
*hypotheses* (rather than literal `Fin 0`s) so that it can be `subst`ed in directly against
`leftCard hrig hn C.out`/`rightCard hrig hn C.out`, with no further reindexing needed. -/
theorem mem_span_hom {K : Type*} [Field K] [CharZero K] {Δ k n : ℕ} (hΔ : 1 ≤ Δ) (hk : 2 ≤ k)
    (hn : 2 * k + 1 ≤ n) (C : Circuit (Fin n × Fin n) K)
    (hred : C.IsReduced) (hsym : IsMatrixSymmetric C) (hsize : supportSize C ≤ k)
    (hdepth : supportDepth C ≤ Δ) {p : MvPolynomial (Fin n × Fin n) K} (hp : C.Computes p) :
    p ∈ Submodule.span K {q | ∃ F : Pattern, ForestwidthLE Δ (k - 1) F ∧ hom K F n = q} := by
  have hrig : IsRigid C := ReducedRigid.isRigid hsym hred
  have hn2 : 2 * supportSize C < n := by omega
  obtain ⟨φ, hφmem, hφeval⟩ := exists_phi hred hsym hk hn hsize hrig hn2 C.out
  have hsupOut : supOf hrig hn2 C.out = (∅ : Set (Fin n ⊕ Fin n)) := by
    rw [supOf_eq_minSupport, minSupport_out]
  have hleftCard0 : leftCard hrig hn2 C.out = 0 := by
    show (leftPart (supOf hrig hn2 C.out)).ncard = 0
    rw [hsupOut]; simp [leftPart]
  have hrightCard0 : rightCard hrig hn2 C.out = 0 := by
    show (rightPart (supOf hrig hn2 C.out)).ncard = 0
    rw [hsupOut]; simp [rightPart]
  have hdepth' : sc C C.out ≤ Δ := (sc_le_supportDepth C.out).trans hdepth
  have hφmem' : φ ∈ span𝔗P K Δ k n
      (Finset.univ : Finset (Fin (leftCard hrig hn2 C.out) ⊕ Fin (rightCard hrig hn2 C.out))) :=
    span𝔗P_mono hdepth' hφmem
  have hpeq : p = φ (leftEnum hrig hn2 C.out) (rightEnum hrig hn2 C.out) :=
    computesAt_unique C C.out hp hφeval
  rw [hpeq]
  exact eval_mem_span_hom hleftCard0 hrightCard0 hΔ (by omega) hφmem' _ _

end Lax461425Proofs.PatternsFromCircuits
