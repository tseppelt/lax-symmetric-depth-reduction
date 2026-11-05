import Lax461425.HomomorphismPolynomials
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Quotient
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Quotient patterns and the exact regrouping of edge multiplicities. -/
open Lax461425.SymmetricFamilies (MatrixPolynomial)

namespace Lax461425Proofs.HomSpanningQuotient

open Lax461425.HomomorphismPolynomials
open scoped Classical

noncomputable section

def weight {K : Type*} [CommSemiring K] (F : Pattern) {n : ℕ}
    (a : F.A → Fin n) (b : F.B → Fin n) : MatrixPolynomial n K :=
  ∏ x, ∏ y, MvPolynomial.X (a x, b y) ^ F.mult x y

def quotient (F : Pattern) (r : Setoid F.A) (s : Setoid F.B) : Pattern where
  A := Quotient r
  B := Quotient s
  mult x y := ∑ a : {a : F.A // Quotient.mk r a = x},
    ∑ b : {b : F.B // Quotient.mk s b = y}, F.mult a.val b.val

theorem card_left (F : Pattern) (r : Setoid F.A) (s : Setoid F.B) :
    Fintype.card (quotient F r s).A ≤ Fintype.card F.A :=
  Fintype.card_le_of_surjective (Quotient.mk r) Quotient.mk_surjective

theorem card_right (F : Pattern) (r : Setoid F.A) (s : Setoid F.B) :
    Fintype.card (quotient F r s).B ≤ Fintype.card F.B :=
  Fintype.card_le_of_surjective (Quotient.mk s) Quotient.mk_surjective

theorem weight_quotient {K : Type*} [CommSemiring K] (F : Pattern)
    (r : Setoid F.A) (s : Setoid F.B) {n : ℕ}
    (a : Quotient r → Fin n) (b : Quotient s → Fin n) :
    weight (K := K) (quotient F r s) a b =
      weight F (a ∘ Quotient.mk r) (b ∘ Quotient.mk s) := by
  unfold weight quotient
  simp only [← Finset.prod_pow_eq_pow_sum]
  calc
    _ = ∏ x : Quotient r, ∏ u : {u : F.A // Quotient.mk r u = x},
        ∏ y : Quotient s, ∏ v : {v : F.B // Quotient.mk s v = y},
          (MvPolynomial.X (a x, b y) : MatrixPolynomial n K) ^ F.mult u.val v.val := by
      apply Finset.prod_congr rfl
      intro x _
      rw [Finset.prod_comm]
    _ = _ := by
      simp_rw [show ∀ (x : Quotient r) (u : {u : F.A // Quotient.mk r u = x})
        (y : Quotient s) (v : {v : F.B // Quotient.mk s v = y}),
        (MvPolynomial.X (a x, b y) : MatrixPolynomial n K) ^ F.mult u.val v.val =
        MvPolynomial.X (a (Quotient.mk r u.val), b (Quotient.mk s v.val)) ^ F.mult u.val v.val
        from fun _ u _ v => by rw [u.property, v.property]]
      have hb : ∀ u : F.A,
          (∏ y : Quotient s, ∏ v : {v : F.B // Quotient.mk s v = y},
            (MvPolynomial.X (a (Quotient.mk r u), b (Quotient.mk s v.val)) :
              MatrixPolynomial n K) ^ F.mult u v.val) =
          ∏ v : F.B, (MvPolynomial.X (a (Quotient.mk r u), b (Quotient.mk s v)) :
              MatrixPolynomial n K) ^ F.mult u v := by
        intro u
        exact Fintype.prod_fiberwise (Quotient.mk s)
          (fun v : F.B => (MvPolynomial.X (a (Quotient.mk r u), b (Quotient.mk s v)) :
            MatrixPolynomial n K) ^ F.mult u v)
      simp_rw [hb]
      exact Fintype.prod_fiberwise (Quotient.mk r)
        (fun u : F.A => ∏ v : F.B,
          (MvPolynomial.X (a (Quotient.mk r u), b (Quotient.mk s v)) :
            MatrixPolynomial n K) ^ F.mult u v)

end
end Lax461425Proofs.HomSpanningQuotient
