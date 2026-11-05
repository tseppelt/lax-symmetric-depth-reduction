import Lax461425.CircuitProperties
import Lax461425Proofs.PermanentCircuit
import Lax461425Proofs.CircuitFamilyFacts
import Lax461425.PermanentCompleteness

open Lax461425.CircuitProperties

/-! Proposition 7.5: permanent belongs to symmetric VNP over every field. -/

namespace Lax461425Proofs.Permanent

open Lax461425.Permanent Lax461425.SymmetricFamilies Lax461425Proofs.CircuitConstants

/--
---
conclusion: Lax461425.PermanentCompleteness.membership
---
The permanent family has a polynomial-size jointly symmetric Boolean witness.
The result holds over every commutative ring, including characteristic two. -/
theorem permanent_membership (K : Type*) [CommRing K] : InSymVNP (permanent K) := by
  refine ⟨(fun n => n), (fun n => 2 * n ^ 2 + 3 * n + 4), ?_, ?_, ?_⟩
  · exact ⟨1, 1, fun n => by simp⟩
  · refine ⟨9, 2, fun n => ?_⟩
    nlinarith [Nat.zero_le n]
  · intro n
    by_cases hn : 0 < n
    · exact ⟨PermanentCircuit.auxAction n, ryserWitness K n, PermanentCircuit.circuit hn,
        PermanentCircuit.computes hn, PermanentCircuit.symmetric hn,
        PermanentCircuit.orbitSize_le hn, trivial,
        ryserWitness_boolSum K n⟩
    · have hz : n = 0 := by omega
      subst n
      refine ⟨PermanentCircuit.auxAction 0, ryserWitness K 0,
        constant ((Fin 0 × Fin 0) ⊕ Fin 0) (1 : K), ?_, ?_, ?_,
        trivial,
        ryserWitness_boolSum K 0⟩
      · simpa [ryserWitness] using
          CircuitFacts.constant_computes (V := (Fin 0 × Fin 0) ⊕ Fin 0) (1 : K)
      · exact CircuitFamilyFacts.constant_symmetric _ _
      · exact (CircuitFamilyFacts.constant_orbitSize_le_one _ _).trans (by norm_num)

end Lax461425Proofs.Permanent
