import Lax461425Proofs.BoundedDepthGlueSupportFormula

/-!
**The support-size bound for the rigidified glue circuit.**
-/

namespace Lax461425Proofs

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.RigidConstruction Lax461425Proofs.PatternsSupportBasic

open scoped Classical

variable {n m : ℕ} {K : Type*} [Field K] [CharZero K] (D : Fin m → Circuit (Fin n × Fin n) K)
  (f : Fin m → K)

/-- **`supportSize (reduced (glueCircuit D f)) ≤ k`**, given every block's support size is
`≤ k`. -/
theorem glueCircuit_reduced_supportSize_le (hred : ∀ i, (D i).IsReduced)
    (hsym : ∀ i, IsMatrixSymmetric (D i)) (hrigRed : IsRigid (reduced (glueCircuit D f))) {k : ℕ}
    (hssD : ∀ i, supportSize (D i) ≤ k) :
    supportSize (reduced (glueCircuit D f)) ≤ k := by
  apply Nat.sInf_le
  intro g
  rcases hg : g.1 with ⟨i, y⟩ | i | i | ⟨⟩
  · have hgeq : g = toC' (glueCircuit D f) (blk D i y) := by
      rw [← toC'_self (glueCircuit D f) g, hg]
    obtain ⟨S, hS, hSc⟩ := supportSize_spec (hrigOf D hred hsym i) y
    refine ⟨S, ?_, le_trans hSc (hssD i)⟩
    rw [hgeq]
    exact (isSupport_reduced_blk_iff D f hred hsym i hrigRed y S).mpr hS
  · have hgeq : g = toC' (glueCircuit D f) (scaledG D i) := by
      rw [← toC'_self (glueCircuit D f) g, hg]
    refine ⟨∅, ?_, by simp⟩
    rw [hgeq]
    exact isSupport_reduced_glue_empty D f hred hsym hrigRed (fun j y hc => by cases hc)
  · have hgeq : g = toC' (glueCircuit D f) (constG D i) := by
      rw [← toC'_self (glueCircuit D f) g, hg]
    refine ⟨∅, ?_, by simp⟩
    rw [hgeq]
    exact isSupport_reduced_glue_empty D f hred hsym hrigRed (fun j y hc => by cases hc)
  · have hgeq : g = toC' (glueCircuit D f) (outGG D) := by
      rw [← toC'_self (glueCircuit D f) g, hg]
    refine ⟨∅, ?_, by simp⟩
    rw [hgeq]
    exact isSupport_reduced_glue_empty D f hred hsym hrigRed (fun j y hc => by cases hc)

end Lax461425Proofs
