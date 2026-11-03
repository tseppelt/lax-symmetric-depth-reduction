import Lax461425Proofs.HomSpanningConstraints
import Mathlib.LinearAlgebra.Span.Defs

/-! Collision inclusion-exclusion expresses injective sums in the bounded-vertex hom span. -/
namespace Lax461425Proofs.HomSpanningInjective

open Lax461425.HomomorphismPolynomials HomSpanningQuotient HomSpanningConstraints
open scoped Classical
noncomputable section

def homSpan (K : Type*) [Field K] (n : ℕ) : Submodule K (MvPolynomial (Fin n × Fin n) K) :=
  Submodule.span K {q | ∃ F : Pattern,
    Fintype.card F.A ≤ n ∧ Fintype.card F.B ≤ n ∧ hom K F n = q}

def avoid {K : Type*} [CommRing K] (F : Pattern) (n : ℕ)
    (S T : Finset (Event F)) : MvPolynomial (Fin n × Fin n) K :=
  ∑ a : F.A → Fin n, ∑ b : F.B → Fin n,
    if (∀ e ∈ S, ¬ collision F a b e) ∧ (∀ e ∈ T, collision F a b e)
      then weight F a b else 0

theorem avoid_empty {K : Type*} [CommRing K] (F : Pattern) (n : ℕ) (T : Finset (Event F)) :
    avoid (K := K) F n ∅ T = hom K (quotient F (leftRelation F T) (rightRelation F T)) n := by
  simpa [avoid] using required_sum_eq_hom (K := K) F T n

theorem avoid_insert {K : Type*} [CommRing K] (F : Pattern) (n : ℕ)
    (S T : Finset (Event F)) (e : Event F) :
    avoid (K := K) F n (insert e S) T = avoid F n S T - avoid F n S (insert e T) := by
  unfold avoid
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hc : collision F a b e <;> simp [Finset.forall_mem_insert, hc]

theorem avoid_mem {K : Type*} [Field K] (F : Pattern) (n : ℕ)
    (hA : Fintype.card F.A ≤ n) (hB : Fintype.card F.B ≤ n)
    (S T : Finset (Event F)) : avoid (K := K) F n S T ∈ homSpan K n := by
  induction S using Finset.induction_on generalizing T with
  | empty =>
    rw [avoid_empty]
    exact Submodule.subset_span ⟨quotient F _ _,
      (card_left F _ _).trans hA, (card_right F _ _).trans hB, rfl⟩
  | @insert e S he ih =>
    rw [avoid_insert]
    exact Submodule.sub_mem _ (ih T) (ih (insert e T))

def badPairs (F : Pattern) : Finset (Event F) :=
  Finset.univ.filter (Sum.elim (fun x => x.1 ≠ x.2) (fun y => y.1 ≠ y.2))

theorem avoids_iff_injective (F : Pattern) {n : ℕ} (a : F.A → Fin n) (b : F.B → Fin n) :
    (∀ e ∈ badPairs F, ¬ collision F a b e) ↔ Function.Injective a ∧ Function.Injective b := by
  constructor
  · intro h
    constructor
    · intro x y he
      by_contra hn
      exact h (.inl (x,y)) (by simp [badPairs, hn]) he
    · intro x y he
      by_contra hn
      exact h (.inr (x,y)) (by simp [badPairs, hn]) he
  · rintro ⟨ha,hb⟩ e he
    cases e with
    | inl x => exact fun hc => (Finset.mem_filter.mp he).2 (ha hc)
    | inr y => exact fun hc => (Finset.mem_filter.mp he).2 (hb hc)

def injectiveHom (K : Type*) [CommRing K] (F : Pattern) (n : ℕ) :
    MvPolynomial (Fin n × Fin n) K :=
  ∑ a : F.A → Fin n, ∑ b : F.B → Fin n,
    if Function.Injective a ∧ Function.Injective b then weight F a b else 0

theorem injectiveHom_mem {K : Type*} [Field K] (F : Pattern) (n : ℕ)
    (hA : Fintype.card F.A ≤ n) (hB : Fintype.card F.B ≤ n) :
    injectiveHom K F n ∈ homSpan K n := by
  have he : injectiveHom K F n = avoid F n (badPairs F) ∅ := by
    unfold injectiveHom avoid
    simp only [avoids_iff_injective]
    simp
  rw [he]
  exact avoid_mem F n hA hB _ _

end
end Lax461425Proofs.HomSpanningInjective
