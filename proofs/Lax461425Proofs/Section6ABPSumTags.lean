import Lax461425Proofs.Section6ABPSumBound

/-!
The branch tags of Lemma 6.5. Extending automorphisms fix constant labels, so the distinct
tags on the edges leaving the entries and entering the sink fix both endpoints of every
branch, including under automorphisms not chosen by the matrix action.
-/

namespace Lax461425Proofs.Section6ABPSum

open Lax461425.SymmetricABPs
open scoped Classical

noncomputable section

variable {I V : Type} {K : Type*} [Fintype I] [Nonempty I] [Fintype V] [Field K] [CharZero K]

omit [Nonempty I] in
theorem tag_injective : Function.Injective (tag (I := I) (K := K)) := by
  intro i j h
  simp only [tag, add_left_inj, Nat.cast_inj] at h
  exact (Fintype.equivFin I).injective (Fin.ext h)

variable (G : I → ABP V K) (c : I → K) (σ : Vertex G ≃ Vertex G) (π : Equiv.Perm V)
variable (hσ : (abp G c).Extends σ π)

include hσ

/-- Distinct branch tags fix both endpoints of every branch. -/
theorem endpoints_fixed_of_tags :
    (∀ i, σ (.entry i) = .entry i) ∧ (∀ i, σ (.exit i) = .exit i) := by
  constructor
  · intro i
    have he := (hσ.2.2.1 .source (.entry i)).2 (show edge G .source (.entry i) from trivial)
    rw [hσ.1] at he
    cases hi : σ (.entry i) <;> simp only [hi, edge] at he
    rename_i j
    have hb : (abp G c).edge (.entry i) (.branch i (G i).source) := ⟨rfl, rfl⟩
    have hl := hσ.2.2.2 _ _ hb
    have hb' := (hσ.2.2.1 _ _).2 hb
    rw [hi] at hl hb'
    cases hv : σ (.branch i (G i).source) <;> simp only [hv, edge] at hb'
    rename_i j' v
    obtain ⟨rfl, -⟩ := hb'
    rw [hv] at hl
    simp only [label, constForm, AffineForm.polynomial, MvPolynomial.rename_C, map_zero,
      zero_mul, Finset.sum_const_zero, add_zero] at hl
    rw [tag_injective (MvPolynomial.C_injective _ _ hl)]
  · intro i
    have he := (hσ.2.2.1 (.exit i) .sink).2 (show edge G (.exit i) .sink from trivial)
    rw [hσ.2.1] at he
    cases hi : σ (.exit i) <;> simp only [hi, edge] at he
    rename_i j
    have hl := hσ.2.2.2 (.exit i) .sink trivial
    rw [hi, hσ.2.1] at hl
    simp only [label, constForm, AffineForm.polynomial, MvPolynomial.rename_C, map_zero,
      zero_mul, Finset.sum_const_zero, add_zero] at hl
    rw [tag_injective (inv_inj.mp (MvPolynomial.C_injective _ _ hl))]

end
end Lax461425Proofs.Section6ABPSum
