import Lax461425.Permanent
import Lax461425.SymmetricFamilies
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
Ryser's Boolean-cube identity, including characteristic two. This is an algebraic identity
over every commutative ring; the circuit witness is treated separately.
-/

namespace Lax461425Proofs.Permanent

open scoped BigOperators
open Finset Equiv

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

/-- Boolean values as elements of a ring. -/
def bit (b : Bool) : R := if b then 1 else 0

lemma bit_sign_sum (d : ℕ) :
    (∑ b : Bool, (2 * bit b - 1 : R) * bit b ^ d) = if d = 0 then 0 else 1 := by
  cases d <;> norm_num [bit]

lemma prod_fibers (h : I → I) (e : I → Bool) :
    (∏ i, (bit (e (h i)) : R)) =
      ∏ j, (bit (e j) : R) ^ ((univ.filter fun i => h i = j).card) := by
  rw [← Finset.prod_fiberwise' univ h (fun j => (bit (e j) : R))]
  simp

lemma boolean_weight (h : I → I) :
    (∑ e : I → Bool, (∏ j, (2 * bit (e j) - 1 : R)) *
      ∏ i, (bit (e (h i)) : R)) = if Function.Surjective h then 1 else 0 := by
  simp_rw [prod_fibers, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j b =>
    (2 * bit b - 1 : R) * bit b ^ ((univ.filter fun i => h i = j).card))]
  simp_rw [bit_sign_sum]
  by_cases hh : Function.Surjective h
  · rw [if_pos hh]
    apply Finset.prod_eq_one
    intro j _
    obtain ⟨i, hi⟩ := hh j
    have hn : (univ.filter fun i => h i = j).Nonempty := ⟨i, by simp [hi]⟩
    simp [Finset.card_ne_zero.mpr hn]
  · rw [if_neg hh]
    simp only [Function.Surjective, not_forall, not_exists] at hh
    obtain ⟨j, hj⟩ := hh
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    have he : (univ.filter fun i => h i = j) = ∅ := by
      ext i
      simp [hj i]
    simp [he]

/-- Expansion of the Boolean witness into a sum over surjective self-maps. -/
theorem boolean_sum_eq_sum_surjective (M : Matrix I I R) :
    (∑ e : I → Bool, (∏ j, (2 * bit (e j) - 1 : R)) *
      ∏ i, ∑ j, M i j * bit (e j)) =
      ∑ h : I → I, if Function.Surjective h then ∏ i, M i (h i) else 0 := by
  simp_rw [Fintype.prod_sum]
  simp_rw [Finset.mul_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  calc
    _ = (∏ i, M i (h i)) *
        ∑ e : I → Bool, (∏ j, (2 * bit (e j) - 1 : R)) *
          ∏ i, (bit (e (h i)) : R) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = _ := by rw [boolean_weight]; split_ifs <;> simp

lemma sum_surjective_eq_permanent (M : Matrix I I R) :
    (∑ h : I → I, if Function.Surjective h then ∏ i, M i (h i) else 0) =
      Matrix.permanent M := by
  classical
  rw [← Matrix.permanent_transpose]
  unfold Matrix.permanent
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun h hh =>
    Equiv.ofBijective h (Finset.mem_filter.mp hh).2.bijective_of_finite) ?_ ?_ ?_ ?_
  · intro h hh
    exact Finset.mem_univ _
  · intro h hh k hk heq
    exact congrArg (fun e : Equiv.Perm I => (e : I → I)) heq
  · intro σ _
    refine ⟨σ, by simp [σ.surjective], ?_⟩
    ext i
    rfl
  · intro h hh
    rfl

/-- Ryser's Boolean-cube identity, over every commutative ring. -/
theorem ryser_boolean (M : Matrix I I R) :
    (∑ e : I → Bool, (∏ j, (2 * bit (e j) - 1 : R)) *
      ∏ i, ∑ j, M i j * bit (e j)) = Matrix.permanent M :=
  (boolean_sum_eq_sum_surjective M).trans (sum_surjective_eq_permanent M)

set_option backward.isDefEq.respectTransparency false in
/-- The polynomial Ryser witness sums to the permanent, including order zero. -/
theorem ryserWitness_boolSum (K : Type*) [CommRing K] (n : ℕ) :
    Lax461425.SymmetricFamilies.boolSum (Lax461425.Permanent.ryserWitness K n) =
      Lax461425.Permanent.polynomial K n := by
  classical
  unfold Lax461425.SymmetricFamilies.boolSum Lax461425.Permanent.ryserWitness
    Lax461425.Permanent.polynomial
  convert ryser_boolean (fun i j : Fin n =>
    (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) K)) using 1
  refine Finset.sum_congr (by ext e; simp) ?_
  intro e _
  simp [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_prod, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_sum, bit]

end Lax461425Proofs.Permanent
