import Lax461425Proofs.HomSpanningQuotient

/-! Equality constraints on assignments are precisely homomorphisms of quotient patterns. -/
namespace Lax461425Proofs.HomSpanningConstraints

open Lax461425.HomomorphismPolynomials HomSpanningQuotient
open scoped Classical
noncomputable section

abbrev Event (F : Pattern) := (F.A × F.A) ⊕ (F.B × F.B)

def collision (F : Pattern) {n : ℕ} (a : F.A → Fin n) (b : F.B → Fin n) : Event F → Prop :=
  Sum.elim (fun x => a x.1 = a x.2) (fun y => b y.1 = b y.2)

def leftRelation (F : Pattern) (S : Finset (Event F)) : Setoid F.A :=
  Relation.EqvGen.setoid (fun a a' => Sum.inl (a, a') ∈ S)

def rightRelation (F : Pattern) (S : Finset (Event F)) : Setoid F.B :=
  Relation.EqvGen.setoid (fun b b' => Sum.inr (b, b') ∈ S)

theorem required_iff (F : Pattern) (S : Finset (Event F)) {n : ℕ}
    (a : F.A → Fin n) (b : F.B → Fin n) :
    (∀ e ∈ S, collision F a b e) ↔
      leftRelation F S ≤ Setoid.ker a ∧ rightRelation F S ≤ Setoid.ker b := by
  constructor
  · intro h
    exact ⟨Setoid.eqvGen_le (fun x y he => h (.inl (x,y)) he),
      Setoid.eqvGen_le (fun x y he => h (.inr (x,y)) he)⟩
  · rintro ⟨hl, hr⟩ e he
    cases e with
    | inl x => exact hl (Relation.EqvGen.rel _ _ he)
    | inr y => exact hr (Relation.EqvGen.rel _ _ he)

theorem sum_lift {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [AddCommMonoid R]
    (r : Setoid A) (f : (A → B) → R) :
    (∑ a : A → B, if r ≤ Setoid.ker a then f a else 0) =
      ∑ a : Quotient r → B, f (a ∘ Quotient.mk r) := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype _ (by simp : ∀ a : A → B,
    a ∈ Finset.univ.filter (fun a => r ≤ Setoid.ker a) ↔ r ≤ Setoid.ker a) f]
  exact Fintype.sum_equiv (Setoid.liftEquiv r) _ _ (fun a => rfl)

set_option backward.isDefEq.respectTransparency false in
theorem required_sum_eq_hom {K : Type*} [CommSemiring K] (F : Pattern)
    (S : Finset (Event F)) (n : ℕ) :
    (∑ a : F.A → Fin n, ∑ b : F.B → Fin n,
      if ∀ e ∈ S, collision F a b e then weight (K := K) F a b else 0) =
      hom K (quotient F (leftRelation F S) (rightRelation F S)) n := by
  simp_rw [required_iff, ite_and]
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [sum_lift (leftRelation F S) (fun a : F.A → Fin n =>
    ∑ b : F.B → Fin n, if rightRelation F S ≤ Setoid.ker b then weight (K := K) F a b else 0)]
  have hb : ∀ a : F.A → Fin n,
      (∑ b : F.B → Fin n, if rightRelation F S ≤ Setoid.ker b then weight (K := K) F a b else 0) =
        ∑ b : Quotient (rightRelation F S) → Fin n,
          weight F a (b ∘ Quotient.mk (rightRelation F S)) := by
    intro a
    exact sum_lift (rightRelation F S) (fun b => weight (K := K) F a b)
  simp_rw [hb]
  unfold hom
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact (weight_quotient F _ _ a b).symm

end
end Lax461425Proofs.HomSpanningConstraints
