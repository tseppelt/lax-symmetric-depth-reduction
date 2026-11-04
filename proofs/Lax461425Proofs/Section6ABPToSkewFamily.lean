import Lax461425.CircuitProperties
import Lax461425.SymmetricABPCharacterisation
import Lax461425Proofs.Section6ABPToSkewOrbits
import Lax461425Proofs.PolynomialBounds
import Lax461425Proofs.Section6ABPToSkewComputes

open Lax461425.CircuitProperties

/-! The family-level inclusion of symmetric ABPs in symmetric skew circuits. -/

namespace Lax461425Proofs.Section6ABPToSkew

open Lax461425.SymmetricFamilies Lax461425.SymmetricABPs

/--
---
conclusion: Lax461425.SymmetricABPCharacterisation.inSymVS_of_inSymVBP
---
Lemma 6.4. The explicit conversion preserves computation and symmetry, and its gate orbits are bounded
by `B + B² (n² + 1) + 1` whenever the ABP vertex orbits are bounded by `B`.
-/
theorem family_inclusion {K : Type*} [CommSemiring K] (f : MatrixFamily K)
    (hf : InSymVBP f) : InSymVS f := by
  obtain ⟨b, hb, hw⟩ := hf
  refine ⟨(fun n => b n + b n ^ 2 * (n ^ 2 + 1) + 1),
    PolynomialBounds.skew_bound hb, ?_⟩
  intro n
  obtain ⟨G, hcomp, hsym, horbit⟩ := hw n
  refine ⟨circuit G, ?_, circuit_isMatrixSymmetric G hsym, ?_, circuit_isSkew G⟩
  · change G.polynomial = f n at hcomp
    exact hcomp ▸ circuit_computes G
  · apply (circuit_orbitSize_le G).trans
    change G.orbitSize + G.orbitSize ^ 2 * (n ^ 2 + 1) + 1 ≤
      b n + b n ^ 2 * (n ^ 2 + 1) + 1
    have hsq : G.orbitSize ^ 2 ≤ b n ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul horbit horbit
    exact Nat.add_le_add_right
      (Nat.add_le_add horbit (Nat.mul_le_mul_right (n ^ 2 + 1) hsq)) 1

end Lax461425Proofs.Section6ABPToSkew
