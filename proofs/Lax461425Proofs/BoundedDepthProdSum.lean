import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Two generic finite combinatorial facts used repeatedly when evaluating the glue circuit: a
product supported on exactly two points, and a sum supported on exactly the image of an
injective function.
-/

namespace Lax461425Proofs

open scoped Classical

/-- A product `∏ x, qval x ^ e x` where `e` vanishes off `{a, b}` (`a ≠ b`) reduces to the two
non-trivial factors. -/
theorem prod_eq_of_two_support {α V : Type*} [Fintype α] [CommMonoid V] (e : α → ℕ)
    (qval : α → V) {a b : α} (hab : a ≠ b) (hrest : ∀ x, x ≠ a → x ≠ b → e x = 0) :
    (∏ x, qval x ^ e x) = qval a ^ e a * qval b ^ e b := by
  have hstep : ∏ x : α, qval x ^ e x = ∏ x ∈ ({a, b} : Finset α), qval x ^ e x := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [hrest x (fun h => hx (Or.inl h)) (fun h => hx (Or.inr h)), pow_zero]
  rw [hstep, Finset.prod_insert (by simp [hab]), Finset.prod_singleton]

/-- A sum `∑ x, e x • qval x` where `e` is `1` on the image of an injective `ι : β → α` and
vanishes elsewhere reduces to a sum over `β`. -/
theorem sum_eq_of_support_image {α β V : Type*} [Fintype α] [Fintype β] [AddCommMonoid V]
    (e : α → ℕ) (qval : α → V) (ι : β → α) (hι : Function.Injective ι) (h1 : ∀ j, e (ι j) = 1)
    (hrest : ∀ x, (∀ j, x ≠ ι j) → e x = 0) :
    (∑ x, e x • qval x) = ∑ j : β, qval (ι j) := by
  have hstep : (∑ x : α, e x • qval x) =
      ∑ x ∈ (Finset.univ : Finset β).image ι, e x • qval x := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    rw [hrest x (fun j hj => hx (by simp [hj]))]
    simp
  rw [hstep, Finset.sum_image (fun x _ y _ hxy => hι hxy)]
  exact Finset.sum_congr rfl (fun j _ => by rw [h1 j, one_nsmul])

end Lax461425Proofs
