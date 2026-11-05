import Lax461425.Permanent
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

/-! The paper's finite-support expansion into monomial words, without length padding. -/

namespace Lax461425Proofs.PermanentPresentation

open scoped BigOperators Classical

variable {V : Type} {K : Type*} [CommSemiring K]

abbrev Occurrence (m : V →₀ ℕ) := Σ v : m.support, Fin (m v.val)

noncomputable def word (m : V →₀ ℕ) (j : Fin (Fintype.card (Occurrence m))) : V :=
  ((Fintype.equivFin (Occurrence m)).symm j).1.val

lemma monomial_word (m : V →₀ ℕ) (c : K) :
    MvPolynomial.monomial m c = MvPolynomial.C c *
      ∏ j, MvPolynomial.X (word m j) := by
  rw [MvPolynomial.monomial_eq]
  congr 1
  dsimp only [word]
  rw [(Fintype.equivFin (Occurrence m)).symm.prod_comp
    (fun u : Occurrence m => (MvPolynomial.X u.1.val : MvPolynomial V K))]
  simp only [Fintype.prod_sigma, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (Finset.prod_coe_sort m.support (fun v => (MvPolynomial.X v : MvPolynomial V K) ^ m v)).symm

/-- Each supported monomial uses its actual variable word. The empty word represents
a constant, and the zero polynomial has no supported terms. -/
theorem exists_presentation (p : MvPolynomial V K) :
    ∃ (B : Type) (_ : Fintype B) (_ : DecidableEq B) (d : B → ℕ) (c : B → K)
      (z : ∀ b, Fin (d b) → V),
      p = ∑ b, MvPolynomial.C (c b) * ∏ j, MvPolynomial.X (z b j) := by
  refine ⟨p.support, inferInstance, inferInstance,
    (fun b => Fintype.card (Occurrence b.val)), (fun b => p.coeff b.val),
    (fun b => word b.val), ?_⟩
  calc
    p = ∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m) := p.as_sum
    _ = _ := by
      rw [← Finset.sum_coe_sort p.support]
      exact Finset.sum_congr rfl fun b _ => monomial_word b.val (p.coeff b.val)

end Lax461425Proofs.PermanentPresentation
