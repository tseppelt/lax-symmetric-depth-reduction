import Lax461425Proofs.PatternsLabelledBasic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Prod

/-!
---
title: Gluing labelled graphs (lem:labelled-ops, item 2), the polynomial identity
type: definition
---
We construct the *gluing* `glue G G'` of two `(ℓ,r)`-labelled graphs `G, G'`: the disjoint union
of `G.F, G'.F`, with `a_i` identified with `a'_i` and `b_j` with `b'_j` for every label
position. The vertex sets of the glued pattern are genuine quotients (via `Quot`, with the bare
*generating* relation, never its closure under symmetry/transitivity -- the computation rule for
`Quot.lift`, together with `Quot.sound`, handles the closure automatically) of `G.F.A ⊕ G'.F.A`
and `G.F.B ⊕ G'.F.B`. Edges are glued by *summing* multiplicities over the (possibly several)
original vertices landing in a given quotient class: this is the only sensible definition once
some vertices are identified (the identified vertices accumulate the incident edges of *both*
original graphs), and it is what makes the key multiplicativity identity
`labelledHom K (glue G G') n v w = labelledHom K G n v w * labelledHom K G' n v w`
(`labelledHom_glue` below) true.
-/

namespace Lax461425Proofs.PatternsLabelledGlue

open Lax461425.HomomorphismPolynomials Lax461425Proofs.PatternsLabelledBasic
open scoped Classical

variable {ℓ r : ℕ}

/-! ### A generic quotient-lifting equivalence -/

/-- `f` respects the relation `rel`: a necessary and sufficient condition for `f` to factor
through `Quot rel`. -/
def Respects {α β : Type*} (rel : α → α → Prop) (f : α → β) : Prop :=
  ∀ a a', rel a a' → f a = f a'

/-- Functions out of `Quot rel` correspond exactly to functions on the underlying type that
respect `rel`. We only ever need to check that a candidate function respects the *generating*
relation `rel` (not its reflexive-symmetric-transitive closure): `Quot.lift`'s defining property
takes care of the rest, since `Quot.mk rel a = Quot.mk rel b` holds in `Quot rel` exactly when
`a, b` are connected by the closure of `rel`, and any function built via `Quot.lift` automatically
respects *that* equality (by the computation rule `Quot.lift f h (Quot.mk rel a) = f a`, which is
`rfl`). -/
noncomputable def quotLiftEquiv {α : Type*} (rel : α → α → Prop) (β : Type*) :
    (Quot rel → β) ≃ {f : α → β // Respects rel f} where
  toFun H := ⟨H ∘ Quot.mk rel, fun a a' haa' => by simp [Quot.sound haa']⟩
  invFun f := Quot.lift f.1 f.2
  left_inv H := funext fun q => Quot.inductionOn q (fun a => rfl)
  right_inv f := Subtype.ext (funext fun a => rfl)

/-! ### Side-independent gluing along a pair of maps

Everything about the `A`-side and `B`-side gluings is the same statement about a pair of maps
`f : ι → α`, `g : ι → β` (to be identified pointwise); it is proved once here. -/

section PairGeneric

variable {ι α β : Type*} (f : ι → α) (g : ι → β)

/-- The generating relation on `α ⊕ β` identifying `f i` with `g i`. -/
def PairRel : α ⊕ β → α ⊕ β → Prop := fun x y => ∃ i, x = Sum.inl (f i) ∧ y = Sum.inr (g i)

/-- `x` is a copy of some `f i` (on the left) or `g i` (on the right). -/
def IsPairLabel (x : α ⊕ β) : Prop :=
  Sum.elim (fun x0 => ∃ i, f i = x0) (fun x0' => ∃ i, g i = x0') x

theorem eqvGen_pairRel_eq_or {x y : α ⊕ β} (h : Relation.EqvGen (PairRel f g) x y) :
    x = y ∨ (IsPairLabel f g x ∧ IsPairLabel f g y) := by
  induction h with
  | rel a b hab => obtain ⟨i, ha, hb⟩ := hab; subst ha; subst hb; exact Or.inr ⟨⟨i, rfl⟩, ⟨i, rfl⟩⟩
  | refl a => exact Or.inl rfl
  | symm a b _ ih =>
      rcases ih with h | ⟨h1, h2⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨h2, h1⟩
  | trans a b c _ _ ih1 ih2 =>
      rcases ih1 with hab | ⟨ha, hb⟩
      · subst hab; exact ih2
      · rcases ih2 with hbc | ⟨hb', hc⟩
        · subst hbc; exact Or.inr ⟨ha, hb⟩
        · exact Or.inr ⟨ha, hc⟩

theorem pairRel_quot_eq_or {x y : α ⊕ β} (h : Quot.mk (PairRel f g) x = Quot.mk (PairRel f g) y) :
    x = y ∨ (IsPairLabel f g x ∧ IsPairLabel f g y) :=
  eqvGen_pairRel_eq_or f g (Quot.eq.mp h)

/-- The pairs of functions agreeing at every identified pair `(f i, g i)`. -/
abbrev PairCompat (γ : Type*) :=
  {p : (α → γ) × (β → γ) // ∀ i, p.1 (f i) = p.2 (g i)}

noncomputable instance [Finite α] [Finite β] (γ : Type*) [Finite γ] :
    Fintype (PairCompat f g γ) := Fintype.ofFinite _

/-- Functions on the glued vertex set correspond exactly to compatible pairs of functions. Built
directly via the universal property of `Quot`. -/
noncomputable def pairLabelEquiv (γ : Type*) :
    (Quot (PairRel f g) → γ) ≃ PairCompat f g γ where
  toFun H := ⟨(H ∘ Quot.mk _ ∘ Sum.inl, H ∘ Quot.mk _ ∘ Sum.inr), fun i => by
    simp [Quot.sound (show PairRel f g (Sum.inl (f i)) (Sum.inr (g i)) from ⟨i, rfl, rfl⟩)]⟩
  invFun p := Quot.lift (Sum.elim p.1.1 p.1.2) (by
    rintro a b ⟨i, rfl, rfl⟩
    simpa using p.2 i)
  left_inv H := funext fun q => Quot.inductionOn q (fun a => by cases a <;> rfl)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> rfl

/-- A sum over `PairCompat f g γ` is a double sum over the two sides, guarded by compatibility. -/
theorem sum_pairCompat_eq_sum_ite [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {γ : Type*} [Fintype γ] [DecidableEq γ] {M : Type*} [AddCommMonoid M]
    (F : (α → γ) → (β → γ) → M) :
    ∑ p : PairCompat f g γ, F p.1.1 p.1.2
      = ∑ a : α → γ, ∑ b : β → γ, if (∀ i, a (f i) = b (g i)) then F a b else 0 := by
  have step1 : (∑ a ∈ Finset.univ.filter
        (fun x : (α → γ) × (β → γ) => ∀ i, x.1 (f i) = x.2 (g i)), F a.1 a.2)
      = ∑ x : PairCompat f g γ, F x.1.1 x.1.2 :=
    Finset.sum_subtype _ (fun x => by simp) _
  rw [← step1, Finset.sum_filter]
  exact Fintype.sum_prod_type' (fun a b => if (∀ i, a (f i) = b (g i)) then F a b else 0)

end PairGeneric

/-! ### The glued vertex sets -/

variable (G G' : LabelledPattern ℓ r)

/-- The generating relation on `G.F.A ⊕ G'.F.A` identifying `a_i` with `a'_i`. -/
abbrev GlueRelA : G.F.A ⊕ G'.F.A → G.F.A ⊕ G'.F.A → Prop := PairRel G.a G'.a

/-- The generating relation on `G.F.B ⊕ G'.F.B` identifying `b_j` with `b'_j`. -/
abbrev GlueRelB : G.F.B ⊕ G'.F.B → G.F.B ⊕ G'.F.B → Prop := PairRel G.b G'.b

/-- The glued `A`-side vertex set: `G.F.A ⊕ G'.F.A` with `a_i` identified with `a'_i`. -/
abbrev GlueA := Quot (GlueRelA G G')

/-- The glued `B`-side vertex set: `G.F.B ⊕ G'.F.B` with `b_j` identified with `b'_j`. -/
abbrev GlueB := Quot (GlueRelB G G')

noncomputable instance : Fintype (GlueA G G') := Fintype.ofFinite _
noncomputable instance : DecidableEq (GlueA G G') := Classical.decEq _
noncomputable instance : Fintype (GlueB G G') := Fintype.ofFinite _
noncomputable instance : DecidableEq (GlueB G G') := Classical.decEq _

/-- The quotient projection onto the glued `A`-side vertex set. -/
def glueπA : G.F.A ⊕ G'.F.A → GlueA G G' := Quot.mk _

/-- The quotient projection onto the glued `B`-side vertex set. -/
def glueπB : G.F.B ⊕ G'.F.B → GlueB G G' := Quot.mk _

theorem glueπA_sound (i : Fin ℓ) : glueπA G G' (Sum.inl (G.a i)) = glueπA G G' (Sum.inr (G'.a i)) :=
  Quot.sound ⟨i, rfl, rfl⟩

theorem glueπB_sound (j : Fin r) : glueπB G G' (Sum.inl (G.b j)) = glueπB G G' (Sum.inr (G'.b j)) :=
  Quot.sound ⟨j, rfl, rfl⟩

/-- The multiplicity between a vertex of `G.F.A ⊕ G'.F.A` and a vertex of `G.F.B ⊕ G'.F.B`,
*before* quotienting: the disjoint union of `G.F.mult` and `G'.F.mult`, with every "cross" pair
(one vertex from `G`, one from `G'`) given multiplicity `0` (there is never an edge directly
between the two original graphs; any apparent connection comes only from identified label
vertices). -/
def glueMult0 : G.F.A ⊕ G'.F.A → G.F.B ⊕ G'.F.B → ℕ :=
  Sum.elim (fun x => Sum.elim (G.F.mult x) (fun _ => 0))
    (fun x' => Sum.elim (fun _ => 0) (G'.F.mult x'))

/-- The multiplicity between two glued vertices: the *sum*, over all pairs of original vertices
landing in the given pair of quotient classes, of their `glueMult0`. (This is forced: once
vertices are identified, the identified vertex must carry the combined incidence of all the
original vertices it came from.) -/
noncomputable def glueMult' (qa : GlueA G G') (qb : GlueB G G') : ℕ :=
  ∑ p : {p : (G.F.A ⊕ G'.F.A) × (G.F.B ⊕ G'.F.B) // (glueπA G G' p.1, glueπB G G' p.2) = (qa, qb)},
    glueMult0 G G' p.1.1 p.1.2

/-- The glued pattern. -/
noncomputable def gluePattern : Pattern where
  A := GlueA G G'
  B := GlueB G G'
  mult := glueMult' G G'

/-- **Item 2's construction**: the gluing `F ⊙ F'` of two `(ℓ,r)`-labelled graphs, identifying
`a_i` with `a'_i` and `b_j` with `b'_j` at every label position. -/
noncomputable def glue : LabelledPattern ℓ r where
  F := gluePattern G G'
  a := fun i => glueπA G G' (Sum.inl (G.a i))
  b := fun j => glueπB G G' (Sum.inl (G.b j))

/-! ### The product factors through `glueMult0` -/

open MvPolynomial in
/-- The core combinatorial fact behind the multiplicativity of homomorphism polynomials under
gluing: the big product over the glued vertex sets, with `glueMult'`-many copies of each
variable, equals the big product over the *original* (pre-quotient) vertex sets, with
`glueMult0`-many copies of each variable. This holds for *any* choice of `hA, hB` on the glued
vertex sets (no label-matching hypothesis is needed here): it is simply the statement that
`glueMult'` is the pushforward, under the quotient maps, of `glueMult0`. -/
theorem prod_pow_glueMult' (n : ℕ) (K : Type*) [CommSemiring K]
    (hA : GlueA G G' → Fin n) (hB : GlueB G G' → Fin n) :
    (∏ qa : GlueA G G', ∏ qb : GlueB G G',
        (X (hA qa, hB qb) : MvPolynomial (Fin n × Fin n) K) ^ glueMult' G G' qa qb)
      = ∏ x : G.F.A ⊕ G'.F.A, ∏ y : G.F.B ⊕ G'.F.B,
          (X (hA (glueπA G G' x), hB (glueπB G G' y)) :
              MvPolynomial (Fin n × Fin n) K) ^ glueMult0 G G' x y := by
  set g : (G.F.A ⊕ G'.F.A) × (G.F.B ⊕ G'.F.B) → GlueA G G' × GlueB G G' :=
    fun p => (glueπA G G' p.1, glueπB G G' p.2) with hg
  set f : (G.F.A ⊕ G'.F.A) × (G.F.B ⊕ G'.F.B) → MvPolynomial (Fin n × Fin n) K :=
    fun p => X (hA (glueπA G G' p.1), hB (glueπB G G' p.2)) ^ glueMult0 G G' p.1 p.2 with hf
  calc (∏ qa : GlueA G G', ∏ qb : GlueB G G',
        (X (hA qa, hB qb) : MvPolynomial (Fin n × Fin n) K) ^ glueMult' G G' qa qb)
      = ∏ j : GlueA G G' × GlueB G G',
          (X (hA j.1, hB j.2) : MvPolynomial (Fin n × Fin n) K) ^ glueMult' G G' j.1 j.2 :=
        (Fintype.prod_prod_type' _).symm
    _ = ∏ j : GlueA G G' × GlueB G G',
          ∏ p : {p : (G.F.A ⊕ G'.F.A) × (G.F.B ⊕ G'.F.B) // g p = j}, f p.1 := by
        apply Finset.prod_congr rfl
        intro j _
        show (X (hA j.1, hB j.2) : MvPolynomial (Fin n × Fin n) K) ^ glueMult' G G' j.1 j.2 = _
        rw [glueMult', ← Finset.prod_pow_eq_pow_sum]
        apply Finset.prod_congr rfl
        intro p _
        have hp : g p.1 = j := p.2
        show _ = f p.1
        have h1 : glueπA G G' p.1.1 = j.1 := congrArg Prod.fst hp
        have h2 : glueπB G G' p.1.2 = j.2 := congrArg Prod.snd hp
        simp only [hf, h1, h2]
    _ = ∏ p : (G.F.A ⊕ G'.F.A) × (G.F.B ⊕ G'.F.B), f p := Fintype.prod_fiberwise g f
    _ = ∏ x : G.F.A ⊕ G'.F.A, ∏ y : G.F.B ⊕ G'.F.B, f (x, y) := Fintype.prod_prod_type f

open MvPolynomial in
/-- The glued product factors as the product of the two original products: combining
`prod_pow_glueMult'` with the fact that `glueMult0` vanishes on "cross" pairs (so the two
mixed blocks of the fourfold split contribute only `1`s). This is the polynomial-level heart of
item 2: it is exactly the statement that the inner product of `labelledHom` for `glue G G'`
factors as a product of the inner products for `G` and for `G'`. -/
theorem prod_pow_glueMult'_eq_mul (n : ℕ) (K : Type*) [CommSemiring K]
    (hA : GlueA G G' → Fin n) (hB : GlueB G G' → Fin n) :
    (∏ qa : GlueA G G', ∏ qb : GlueB G G',
        (X (hA qa, hB qb) : MvPolynomial (Fin n × Fin n) K) ^ glueMult' G G' qa qb)
      = (∏ x : G.F.A, ∏ y : G.F.B,
          (X (hA (glueπA G G' (Sum.inl x)), hB (glueπB G G' (Sum.inl y))) :
              MvPolynomial (Fin n × Fin n) K) ^ G.F.mult x y)
        * ∏ x' : G'.F.A, ∏ y' : G'.F.B,
            (X (hA (glueπA G G' (Sum.inr x')), hB (glueπB G G' (Sum.inr y'))) :
                MvPolynomial (Fin n × Fin n) K) ^ G'.F.mult x' y' := by
  rw [prod_pow_glueMult']
  simp only [Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl
    intro x _
    have h1 : ∀ y : G.F.B, glueMult0 G G' (Sum.inl x) (Sum.inl y) = G.F.mult x y := fun _ => rfl
    have h2 : ∀ y' : G'.F.B, glueMult0 G G' (Sum.inl x) (Sum.inr y') = 0 := fun _ => rfl
    simp only [h1, h2, pow_zero, Finset.prod_const_one, mul_one]
  · apply Finset.prod_congr rfl
    intro x' _
    have h1 : ∀ y : G.F.B, glueMult0 G G' (Sum.inr x') (Sum.inl y) = 0 := fun _ => rfl
    have h2 : ∀ y' : G'.F.B, glueMult0 G G' (Sum.inr x') (Sum.inr y') = G'.F.mult x' y' :=
      fun _ => rfl
    simp only [h1, h2, pow_zero, Finset.prod_const_one, one_mul]

/-! ### Functions on the glued vertex sets, as compatible pairs -/

/-- The pairs of `A`-side functions that agree at every identified label pair `(a_i, a'_i)`. We
route *every* use of this type through this fixed name, with its `Fintype` instance declared
once below (via `Fintype.ofFinite`, needing no `DecidablePred`): this sidesteps the same hazard
that `isolatedSet` in `PatternsLabelledBasic` was designed to avoid for `Finset.filter` --
independently-elaborated `DecidablePred`/`Fintype` instances for the *same* underlying predicate
are propositionally but not always syntactically/definitionally equal, which breaks naive `rw`
across lemmas that are generic in the predicate. Naming the type once and fixing its instance
here means every occurrence (in `glueLabelEquivA`'s codomain, and in every lemma about sums over
it) resolves to the *same* instance. -/
abbrev CompatA (γ : Type*) [Fintype γ] := PairCompat G.a G'.a γ

/-- The `B`-side analogue of `CompatA`. -/
abbrev CompatB (γ : Type*) [Fintype γ] := PairCompat G.b G'.b γ

/-- Functions on the glued `A`-side vertex set correspond exactly to pairs of functions on the
two original `A`-sides that agree at every identified label pair `(a_i, a'_i)`. This is the
"crux" bijection: built directly via the universal property of `Quot` (never via the closure of
`GlueRelA` under symmetry/transitivity). -/
noncomputable def glueLabelEquivA (γ : Type*) [Fintype γ] :
    (GlueA G G' → γ) ≃ CompatA G G' γ := pairLabelEquiv G.a G'.a γ

/-- The `B`-side analogue of `glueLabelEquivA`. -/
noncomputable def glueLabelEquivB (γ : Type*) [Fintype γ] :
    (GlueB G G' → γ) ≃ CompatB G G' γ := pairLabelEquiv G.b G'.b γ

/-! ### Dropping the compatibility constraint under a matching label condition -/

/-! ### Converting a `CompatA`/`CompatB` sum into an ordinary double sum -/

/-- A sum over `CompatA G G' γ` is the same as a double sum over the two sides, guarded by the
compatibility condition. Stated specifically for the *named* type `CompatA` (never for a freshly
written `Subtype` literal): this keeps every use of this fact anchored to the single `Fintype`
instance declared for `CompatA`, avoiding a mismatch against some other, independently
elaborated (though propositionally equal) `Fintype`/`DecidablePred` instance for the same
underlying subtype. -/
theorem sum_compatA_eq_sum_ite {γ : Type*} [Fintype γ] [DecidableEq γ] {M : Type*}
    [AddCommMonoid M]
    (f : (G.F.A → γ) → (G'.F.A → γ) → M) :
    ∑ pa : CompatA G G' γ, f pa.1.1 pa.1.2
      = ∑ hAG : G.F.A → γ, ∑ hAG' : G'.F.A → γ,
          if (∀ i, hAG (G.a i) = hAG' (G'.a i)) then f hAG hAG' else 0 := by
  convert sum_pairCompat_eq_sum_ite G.a G'.a f

/-- The `B`-side analogue of `sum_compatA_eq_sum_ite`. -/
theorem sum_compatB_eq_sum_ite {γ : Type*} [Fintype γ] [DecidableEq γ] {M : Type*}
    [AddCommMonoid M]
    (f : (G.F.B → γ) → (G'.F.B → γ) → M) :
    ∑ pb : CompatB G G' γ, f pb.1.1 pb.1.2
      = ∑ hBG : G.F.B → γ, ∑ hBG' : G'.F.B → γ,
          if (∀ j, hBG (G.b j) = hBG' (G'.b j)) then f hBG hBG' else 0 := by
  convert sum_pairCompat_eq_sum_ite G.b G'.b f

/-! ### The homomorphism-polynomial multiplicativity of gluing -/

/-- A compatibility guard around a sum factors out of the sum: whenever the guard holds we get
the sum unchanged, and whenever it fails both sides are `0`. -/
theorem ite_sum_eq_sum_ite {ι M : Type*} [Fintype ι] [AddCommMonoid M] (p : Prop)
    [Decidable p] (f : ι → M) : (if p then (∑ x, f x) else 0) = ∑ x, if p then f x else 0 := by
  by_cases hp : p <;> simp [hp]

/-- The pointwise identity underlying the final assembly of `labelledHom_glue`: once a
compatibility guard is nested around a label condition on *each* side, and that label condition
pins down the value at every identified point, the two compatibility guards become redundant and
the whole thing splits as a product of the two independent "labelledHom"-style summands. Stated
as a free-standing lemma (not inside the main proof) so that `simp`'s case analysis is not
swamped by the ambient context of `labelledHom_glue`, and with the label index types fixed to
`Fin ℓ`/`Fin r` (rather than kept abstract) to avoid a `Decidable`-instance mismatch between a
quantifier over an abstract `Fintype` and the concrete `Nat.decidableForallFin` instance that
Lean actually picks for `∀ i : Fin ℓ, ⋯` wherever this lemma gets *used*. -/
theorem pointwise_glue_ite {α α' β β' γ M : Type*} [DecidableEq γ] [MulZeroClass M]
    (lab : Fin ℓ → α) (lab' : Fin ℓ → α') (target : Fin ℓ → γ)
    (labB : Fin r → β) (labB' : Fin r → β') (targetB : Fin r → γ)
    (hAG : α → γ) (hAG' : α' → γ) (hBG : β → γ) (hBG' : β' → γ) (c1 c2 : M) :
    (if (∀ i, hAG (lab i) = hAG' (lab' i)) then
        (if (∀ j, hBG (labB j) = hBG' (labB' j)) then
          (if (∀ i, hAG (lab i) = target i) ∧ (∀ j, hBG (labB j) = targetB j) then c1 * c2
          else 0)
        else 0)
      else 0)
      = (if (∀ i, hAG (lab i) = target i) ∧ (∀ j, hBG (labB j) = targetB j) then c1 else 0) *
        (if (∀ i, hAG' (lab' i) = target i) ∧ (∀ j, hBG' (labB' j) = targetB j) then c2 else 0) := by
  have hfA : (∀ i, hAG (lab i) = target i) → (∀ i, hAG' (lab' i) = target i) →
      (∀ i, hAG (lab i) = hAG' (lab' i)) := fun h h' i => (h i).trans (h' i).symm
  have hfB : (∀ j, hBG (labB j) = targetB j) → (∀ j, hBG' (labB' j) = targetB j) →
      (∀ j, hBG (labB j) = hBG' (labB' j)) := fun h h' j => (h j).trans (h' j).symm
  have hbA : (∀ i, hAG (lab i) = hAG' (lab' i)) → (∀ i, hAG (lab i) = target i) →
      (∀ i, hAG' (lab' i) = target i) := fun h h' i => (h i).symm.trans (h' i)
  have hbB : (∀ j, hBG (labB j) = hBG' (labB' j)) → (∀ j, hBG (labB j) = targetB j) →
      (∀ j, hBG' (labB' j) = targetB j) := fun h h' j => (h j).symm.trans (h' j)
  have hAiff : (∀ i, hAG (lab i) = target i) →
      ((∀ i, hAG (lab i) = hAG' (lab' i)) ↔ (∀ i, hAG' (lab' i) = target i)) :=
    fun hpa => ⟨fun hcA => hbA hcA hpa, hfA hpa⟩
  have hBiff : (∀ j, hBG (labB j) = targetB j) →
      ((∀ j, hBG (labB j) = hBG' (labB' j)) ↔ (∀ j, hBG' (labB' j) = targetB j)) :=
    fun hpb => ⟨fun hcB => hbB hcB hpb, hfB hpb⟩
  by_cases hpa : ∀ i, hAG (lab i) = target i
  · by_cases hpb : ∀ j, hBG (labB j) = targetB j
    · by_cases hcA : ∀ i, hAG (lab i) = hAG' (lab' i)
      · have hpa' : ∀ i, hAG' (lab' i) = target i := (hAiff hpa).mp hcA
        by_cases hcB : ∀ j, hBG (labB j) = hBG' (labB' j)
        · have hpb' : ∀ j, hBG' (labB' j) = targetB j := (hBiff hpb).mp hcB
          simp [hpa, hpb, hpa', hpb']
        · have hpb'_neg : ¬ (∀ j, hBG' (labB' j) = targetB j) :=
            fun h => hcB ((hBiff hpb).mpr h)
          have hpb'_neg' : ¬ (∀ j, targetB j = hBG' (labB' j)) :=
            fun h => hpb'_neg (fun j => (h j).symm)
          simp [hpa, hpb, hpa', hpb'_neg, hpb'_neg']
      · have hpa'_neg : ¬ (∀ i, hAG' (lab' i) = target i) :=
          fun h => hcA ((hAiff hpa).mpr h)
        have hpa'_neg' : ¬ (∀ i, target i = hAG' (lab' i)) :=
          fun h => hpa'_neg (fun i => (h i).symm)
        simp [hpa, hpb, hpa'_neg, hpa'_neg']
    · simp [hpb]
  · simp [hpa]

open MvPolynomial in
/-- **Item 2's polynomial identity**: the homomorphism polynomial of a gluing is the *product*
of the two original homomorphism polynomials. This is the heart of item 2 of `lem:labelled-ops`:
`F ⊙ F' ∈ 𝒯^{Δ,k}_P(ℓ,r)` relies on this to show the generator-level product lands back in the
span, once combined with `InClassP` closure under `glue` (depth/width + support bound, not yet
established here). -/
theorem labelledHom_glue (n : ℕ) (K : Type*) [CommSemiring K]
    (v : Fin ℓ → Fin n) (w : Fin r → Fin n) :
    labelledHom K (glue G G') n v w = labelledHom K G n v w * labelledHom K G' n v w := by
  set ΦG : (G.F.A → Fin n) → (G.F.B → Fin n) → MvPolynomial (Fin n × Fin n) K :=
    fun hAG hBG => ∏ x, ∏ y, X (hAG x, hBG y) ^ G.F.mult x y with hΦG
  set ΦG' : (G'.F.A → Fin n) → (G'.F.B → Fin n) → MvPolynomial (Fin n × Fin n) K :=
    fun hAG' hBG' => ∏ x', ∏ y', X (hAG' x', hBG' y') ^ G'.F.mult x' y' with hΦG'
  have hhomG : labelledHom K G n v w =
      ∑ hAG : G.F.A → Fin n, ∑ hBG : G.F.B → Fin n,
        if (∀ i, hAG (G.a i) = v i) ∧ (∀ j, hBG (G.b j) = w j) then ΦG hAG hBG else 0 := rfl
  have hhomG' : labelledHom K G' n v w =
      ∑ hAG' : G'.F.A → Fin n, ∑ hBG' : G'.F.B → Fin n,
        if (∀ i, hAG' (G'.a i) = v i) ∧ (∀ j, hBG' (G'.b j) = w j) then ΦG' hAG' hBG' else 0 := rfl
  have hhomGlue : labelledHom K (glue G G') n v w =
      ∑ hA : GlueA G G' → Fin n, ∑ hB : GlueB G G' → Fin n,
        if (∀ i, hA (glueπA G G' (Sum.inl (G.a i))) = v i) ∧
            (∀ j, hB (glueπB G G' (Sum.inl (G.b j))) = w j) then
          ΦG (hA ∘ glueπA G G' ∘ Sum.inl) (hB ∘ glueπB G G' ∘ Sum.inl) *
            ΦG' (hA ∘ glueπA G G' ∘ Sum.inr) (hB ∘ glueπB G G' ∘ Sum.inr)
        else 0 := by
    show (∑ hA : GlueA G G' → Fin n, ∑ hB : GlueB G G' → Fin n,
        if (∀ i, hA ((glue G G').a i) = v i) ∧ (∀ j, hB ((glue G G').b j) = w j) then
          (∏ x, ∏ y, X (hA x, hB y) ^ (glue G G').F.mult x y : MvPolynomial (Fin n × Fin n) K)
        else 0) = _
    apply Finset.sum_congr rfl
    intro hA _
    apply Finset.sum_congr rfl
    intro hB _
    congr 1
    exact prod_pow_glueMult'_eq_mul G G' n K hA hB
  rw [hhomGlue, hhomG, hhomG']
  -- Reindex the `hA`-sum via `glueLabelEquivA`, then the `hB`-sum via `glueLabelEquivB`.
  have hreindexA : (∑ hA : GlueA G G' → Fin n, ∑ hB : GlueB G G' → Fin n,
        if (∀ i, hA (glueπA G G' (Sum.inl (G.a i))) = v i) ∧
            (∀ j, hB (glueπB G G' (Sum.inl (G.b j))) = w j) then
          ΦG (hA ∘ glueπA G G' ∘ Sum.inl) (hB ∘ glueπB G G' ∘ Sum.inl) *
            ΦG' (hA ∘ glueπA G G' ∘ Sum.inr) (hB ∘ glueπB G G' ∘ Sum.inr)
        else 0)
      = ∑ pa : CompatA G G' (Fin n), ∑ hB : GlueB G G' → Fin n,
          if (∀ i, pa.1.1 (G.a i) = v i) ∧ (∀ j, hB (glueπB G G' (Sum.inl (G.b j))) = w j) then
              ΦG pa.1.1 (hB ∘ glueπB G G' ∘ Sum.inl) * ΦG' pa.1.2 (hB ∘ glueπB G G' ∘ Sum.inr)
            else 0 := by
    apply Fintype.sum_equiv (glueLabelEquivA G G' (Fin n))
    intro hA
    rfl
  have hreindexB : ∀ (hAG1 : G.F.A → Fin n) (hAG1' : G'.F.A → Fin n) (cond1 : Prop)
      [Decidable cond1],
      (∑ hB : GlueB G G' → Fin n,
          if cond1 ∧ (∀ j, hB (glueπB G G' (Sum.inl (G.b j))) = w j) then
            ΦG hAG1 (hB ∘ glueπB G G' ∘ Sum.inl) * ΦG' hAG1' (hB ∘ glueπB G G' ∘ Sum.inr)
          else 0)
        = ∑ pb : CompatB G G' (Fin n),
            if cond1 ∧ (∀ j, pb.1.1 (G.b j) = w j) then ΦG hAG1 pb.1.1 * ΦG' hAG1' pb.1.2
            else 0 := by
    intro hAG1 hAG1' cond1 _
    apply Fintype.sum_equiv (glueLabelEquivB G G' (Fin n))
    intro hB
    rfl
  rw [hreindexA]
  rw [Finset.sum_congr rfl (fun pa (_ : pa ∈ Finset.univ) =>
    hreindexB pa.1.1 pa.1.2 (∀ i, pa.1.1 (G.a i) = v i))]
  rw [show (∑ pa : CompatA G G' (Fin n), ∑ pb : CompatB G G' (Fin n),
        if (∀ i, pa.1.1 (G.a i) = v i) ∧ (∀ j, pb.1.1 (G.b j) = w j) then
            ΦG pa.1.1 pb.1.1 * ΦG' pa.1.2 pb.1.2
          else 0)
      = ∑ hAG : G.F.A → Fin n, ∑ hAG' : G'.F.A → Fin n,
          if (∀ i, hAG (G.a i) = hAG' (G'.a i)) then
            (∑ pb : CompatB G G' (Fin n),
              if (∀ i, hAG (G.a i) = v i) ∧ (∀ j, pb.1.1 (G.b j) = w j) then
                ΦG hAG pb.1.1 * ΦG' hAG' pb.1.2
              else 0)
          else 0 from
      sum_compatA_eq_sum_ite G G'
        (fun hAG hAG' => ∑ pb : CompatB G G' (Fin n),
          if (∀ i, hAG (G.a i) = v i) ∧ (∀ j, pb.1.1 (G.b j) = w j) then
            ΦG hAG pb.1.1 * ΦG' hAG' pb.1.2
          else 0)]
  trans (∑ hAG : G.F.A → Fin n, ∑ hAG' : G'.F.A → Fin n,
      if (∀ i, hAG (G.a i) = hAG' (G'.a i)) then
        (∑ hBG : G.F.B → Fin n, ∑ hBG' : G'.F.B → Fin n,
          if (∀ j, hBG (G.b j) = hBG' (G'.b j)) then
            (if (∀ i, hAG (G.a i) = v i) ∧ (∀ j, hBG (G.b j) = w j) then
              ΦG hAG hBG * ΦG' hAG' hBG' else 0)
          else 0)
      else 0)
  · apply Finset.sum_congr rfl
    intro hAG _
    apply Finset.sum_congr rfl
    intro hAG' _
    by_cases hc : ∀ i, hAG (G.a i) = hAG' (G'.a i)
    · rw [if_pos hc, if_pos hc,
        sum_compatB_eq_sum_ite G G'
          (fun hBG hBG' => if (∀ i, hAG (G.a i) = v i) ∧ (∀ j, hBG (G.b j) = w j) then
              ΦG hAG hBG * ΦG' hAG' hBG' else 0)]
    · rw [if_neg hc, if_neg hc]
  -- Now: ∑ hAG, ∑ hAG', if compatA then (∑ hBG, ∑ hBG', if compatB then (if AcondG∧BcondG then
  -- ΦG*ΦG' else 0) else 0) else 0 = labelledHom G * labelledHom G'.
  have pointwise : ∀ (hAG : G.F.A → Fin n) (hAG' : G'.F.A → Fin n) (hBG : G.F.B → Fin n)
      (hBG' : G'.F.B → Fin n),
      (if (∀ i, hAG (G.a i) = hAG' (G'.a i)) then
          (if (∀ j, hBG (G.b j) = hBG' (G'.b j)) then
            (if (∀ i, hAG (G.a i) = v i) ∧ (∀ j, hBG (G.b j) = w j) then
              ΦG hAG hBG * ΦG' hAG' hBG' else 0)
          else 0)
        else 0)
      = (if (∀ i, hAG (G.a i) = v i) ∧ (∀ j, hBG (G.b j) = w j) then ΦG hAG hBG else 0) *
        (if (∀ i, hAG' (G'.a i) = v i) ∧ (∀ j, hBG' (G'.b j) = w j) then ΦG' hAG' hBG' else 0) :=
    fun hAG hAG' hBG hBG' => pointwise_glue_ite G.a G'.a v G.b G'.b w hAG hAG' hBG hBG'
      (ΦG hAG hBG) (ΦG' hAG' hBG')
  trans (∑ hAG : G.F.A → Fin n, ∑ hAG' : G'.F.A → Fin n, ∑ hBG : G.F.B → Fin n,
      ∑ hBG' : G'.F.B → Fin n,
        (if (∀ i, hAG (G.a i) = v i) ∧ (∀ j, hBG (G.b j) = w j) then ΦG hAG hBG else 0) *
        (if (∀ i, hAG' (G'.a i) = v i) ∧ (∀ j, hBG' (G'.b j) = w j) then ΦG' hAG' hBG' else 0))
  · apply Finset.sum_congr rfl
    intro hAG _
    apply Finset.sum_congr rfl
    intro hAG' _
    have step1 : (if (∀ i, hAG (G.a i) = hAG' (G'.a i)) then
          (∑ hBG : G.F.B → Fin n, ∑ hBG' : G'.F.B → Fin n,
            if (∀ j, hBG (G.b j) = hBG' (G'.b j)) then
              (if (∀ i, hAG (G.a i) = v i) ∧ (∀ j, hBG (G.b j) = w j) then
                ΦG hAG hBG * ΦG' hAG' hBG' else 0)
            else 0)
        else 0)
        = ∑ hBG : G.F.B → Fin n,
            if (∀ i, hAG (G.a i) = hAG' (G'.a i)) then
              (∑ hBG' : G'.F.B → Fin n,
                if (∀ j, hBG (G.b j) = hBG' (G'.b j)) then
                  (if (∀ i, hAG (G.a i) = v i) ∧ (∀ j, hBG (G.b j) = w j) then
                    ΦG hAG hBG * ΦG' hAG' hBG' else 0)
                else 0)
            else 0 :=
      ite_sum_eq_sum_ite _ _
    rw [step1]
    apply Finset.sum_congr rfl
    intro hBG _
    have step2 : (if (∀ i, hAG (G.a i) = hAG' (G'.a i)) then
          (∑ hBG' : G'.F.B → Fin n,
            if (∀ j, hBG (G.b j) = hBG' (G'.b j)) then
              (if (∀ i, hAG (G.a i) = v i) ∧ (∀ j, hBG (G.b j) = w j) then
                ΦG hAG hBG * ΦG' hAG' hBG' else 0)
            else 0)
        else 0)
        = ∑ hBG' : G'.F.B → Fin n,
            if (∀ i, hAG (G.a i) = hAG' (G'.a i)) then
              (if (∀ j, hBG (G.b j) = hBG' (G'.b j)) then
                (if (∀ i, hAG (G.a i) = v i) ∧ (∀ j, hBG (G.b j) = w j) then
                  ΦG hAG hBG * ΦG' hAG' hBG' else 0)
              else 0)
            else 0 :=
      ite_sum_eq_sum_ite _ _
    rw [step2]
    apply Finset.sum_congr rfl
    intro hBG' _
    exact pointwise hAG hAG' hBG hBG'
  trans ((∑ hAG : G.F.A → Fin n, ∑ hBG : G.F.B → Fin n,
        if (∀ i, hAG (G.a i) = v i) ∧ (∀ j, hBG (G.b j) = w j) then ΦG hAG hBG else 0) *
      ∑ hAG' : G'.F.A → Fin n, ∑ hBG' : G'.F.B → Fin n,
        if (∀ i, hAG' (G'.a i) = v i) ∧ (∀ j, hBG' (G'.b j) = w j) then ΦG' hAG' hBG' else 0)
  · rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro hAG _
    apply Finset.sum_congr rfl
    intro hAG' _
    rw [Finset.sum_mul_sum]
  · rw [← hhomG, ← hhomG']

/-! ### `InClassP` closed under `glue` (item 2's remaining support-cardinality step)

Every quotient class of `GlueRelA`/`GlueRelB` is either a singleton (an un-identified vertex)
or consists *entirely* of label vertices (from both sides, at possibly several positions that
all happen to coincide): `GlueRelA`/`GlueRelB` only ever relate `a_i` (from `G`) to `a'_i` (from
`G'`), never two non-label vertices. We formalize this via `IsGlueLabelA`/`IsGlueLabelB`
("`x` is a copy of some label vertex") and the fact that it is invariant along
`Relation.EqvGen (GlueRelA G G')`/`Relation.EqvGen (GlueRelB G G')` (the relation `Quot` actually
quotients by), hence along `glueπA`/`glueπB`-fibers. -/

/-- `x` is (a copy of) an `A`-side label vertex: equal to `G.a i` on the left, or to `G'.a i` on
the right, for some label index `i`. -/
abbrev IsGlueLabelA : G.F.A ⊕ G'.F.A → Prop := IsPairLabel G.a G'.a

/-- The `B`-side analogue of `IsGlueLabelA`. -/
abbrev IsGlueLabelB : G.F.B ⊕ G'.F.B → Prop := IsPairLabel G.b G'.b

theorem glueπA_eq_iff_eq_or_isGlueLabelA {x y : G.F.A ⊕ G'.F.A} (h : glueπA G G' x = glueπA G G' y) :
    x = y ∨ (IsGlueLabelA G G' x ∧ IsGlueLabelA G G' y) :=
  pairRel_quot_eq_or G.a G'.a h

theorem glueπB_eq_iff_eq_or_isGlueLabelB {x y : G.F.B ⊕ G'.F.B} (h : glueπB G G' x = glueπB G G' y) :
    x = y ∨ (IsGlueLabelB G G' x ∧ IsGlueLabelB G G' y) :=
  pairRel_quot_eq_or G.b G'.b h

/-- `IsGlueLabelA` transfers backwards along a `glueπA`-coincidence. -/
theorem IsGlueLabelA.of_glueπA_eq {x y : G.F.A ⊕ G'.F.A} (h : glueπA G G' x = glueπA G G' y)
    (hy : IsGlueLabelA G G' y) : IsGlueLabelA G G' x := by
  rcases glueπA_eq_iff_eq_or_isGlueLabelA G G' h with rfl | ⟨hx, -⟩
  exacts [hy, hx]

/-- The `B`-side analogue of `IsGlueLabelA.of_glueπA_eq`. -/
theorem IsGlueLabelB.of_glueπB_eq {x y : G.F.B ⊕ G'.F.B} (h : glueπB G G' x = glueπB G G' y)
    (hy : IsGlueLabelB G G' y) : IsGlueLabelB G G' x := by
  rcases glueπB_eq_iff_eq_or_isGlueLabelB G G' h with rfl | ⟨hx, -⟩
  exacts [hy, hx]

/-- If the glued `A`-side vertex `qa` is non-isolated in `gluePattern G G'`, some original
`A`-side vertex projecting to it (on the matching original side) is non-isolated in its own
original pattern: the only way to create new incidences by gluing is to sum the multiplicities
of the (possibly several) original vertices landing in the same quotient class, so at least one
of them must already carry a nonzero multiplicity. -/
theorem exists_not_isolated_source_inl {qa : GlueA G G'}
    (h : ¬ isIsolated (gluePattern G G') (Sum.inl qa)) :
    ∃ x : G.F.A ⊕ G'.F.A, glueπA G G' x = qa ∧
      ((∃ x0, x = Sum.inl x0 ∧ ¬ isIsolated G.F (Sum.inl x0)) ∨
       (∃ x0', x = Sum.inr x0' ∧ ¬ isIsolated G'.F (Sum.inl x0'))) := by
  have h' : ¬ ∀ y : GlueB G G', (gluePattern G G').mult qa y = 0 := h
  push_neg at h'
  obtain ⟨qb, hqb⟩ := h'
  have hne : glueMult' G G' qa qb ≠ 0 := hqb
  have hex : ∃ p0 : {p : (G.F.A ⊕ G'.F.A) × (G.F.B ⊕ G'.F.B) //
      (glueπA G G' p.1, glueπB G G' p.2) = (qa, qb)}, glueMult0 G G' p0.1.1 p0.1.2 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (Finset.sum_eq_zero fun p0 _ => hcon p0)
  obtain ⟨⟨⟨x, y⟩, hxy⟩, hne0⟩ := hex
  have hqa : glueπA G G' x = qa := congrArg Prod.fst hxy
  refine ⟨x, hqa, ?_⟩
  rcases x with x0 | x0' <;> rcases y with y0 | y0'
  · exact Or.inl ⟨x0, rfl, fun hiso => hne0 (hiso y0)⟩
  · exact absurd rfl hne0
  · exact absurd rfl hne0
  · exact Or.inr ⟨x0', rfl, fun hiso => hne0 (hiso y0')⟩

/-- The `B`-side analogue of `exists_not_isolated_source_inl`. -/
theorem exists_not_isolated_source_inr {qb : GlueB G G'}
    (h : ¬ isIsolated (gluePattern G G') (Sum.inr qb)) :
    ∃ y : G.F.B ⊕ G'.F.B, glueπB G G' y = qb ∧
      ((∃ y0, y = Sum.inl y0 ∧ ¬ isIsolated G.F (Sum.inr y0)) ∨
       (∃ y0', y = Sum.inr y0' ∧ ¬ isIsolated G'.F (Sum.inr y0'))) := by
  have h' : ¬ ∀ x : GlueA G G', (gluePattern G G').mult x qb = 0 := h
  push_neg at h'
  obtain ⟨qa, hqa⟩ := h'
  have hne : glueMult' G G' qa qb ≠ 0 := hqa
  have hex : ∃ p0 : {p : (G.F.A ⊕ G'.F.A) × (G.F.B ⊕ G'.F.B) //
      (glueπA G G' p.1, glueπB G G' p.2) = (qa, qb)}, glueMult0 G G' p0.1.1 p0.1.2 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (Finset.sum_eq_zero fun p0 _ => hcon p0)
  obtain ⟨⟨⟨x, y⟩, hxy⟩, hne0⟩ := hex
  have hqb : glueπB G G' y = qb := congrArg Prod.snd hxy
  refine ⟨y, hqb, ?_⟩
  rcases x with x0 | x0' <;> rcases y with y0 | y0'
  · exact Or.inl ⟨y0, rfl, fun hiso => hne0 (hiso x0)⟩
  · exact absurd rfl hne0
  · exact absurd rfl hne0
  · exact Or.inr ⟨y0', rfl, fun hiso => hne0 (hiso x0')⟩

variable {Δ k : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)}

/-- If `x0` is a non-isolated `A`-side vertex of `G` that is labelled (`G.a i0 = x0`) and `hGP`
witnesses `G ∈ 𝒯^{Δ,k}_P(ℓ,r)`, then the glued vertex it projects to (`qa`, via `glueπA`) is a
label vertex of `glue G G'` at a position in `P`. -/
theorem mem_image_of_label (hGP : InClassP Δ k P G) {x0 : G.F.A}
    (hniso0 : ¬ isIsolated G.F (Sum.inl x0)) (i0 : Fin ℓ) (hi0 : G.a i0 = x0)
    {qa : GlueA G G'} (hqa : glueπA G G' (Sum.inl x0) = qa) :
    Sum.inl qa ∈ Finset.univ.image (fun p : P => (glue G G').labelVertex (p : Fin ℓ ⊕ Fin r)) := by
  have hmemG : Sum.inl x0 ∈ G.labelSupport :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨Sum.inl i0, Finset.mem_univ _, by
      show Sum.inl (G.a i0) = Sum.inl x0; rw [hi0]⟩, not_isIsolated_iff_notMem.mp hniso0⟩
  obtain ⟨p0, -, hp0⟩ := Finset.mem_image.mp (hGP.2 hmemG)
  rcases p0 with ⟨i1 | j1, hpP⟩
  · have hx0 : G.a i1 = x0 := Sum.inl_injective hp0
    refine Finset.mem_image.mpr ⟨⟨Sum.inl i1, hpP⟩, Finset.mem_univ _, ?_⟩
    show Sum.inl (glueπA G G' (Sum.inl (G.a i1))) = Sum.inl qa
    rw [hx0, hqa]
  · simp [LabelledPattern.labelVertex] at hp0

/-- The `G'`-sided analogue of `mem_image_of_label`, going through `glueπA (Sum.inr x0')`. -/
theorem mem_image_of_label' (hGP' : InClassP Δ k P G') {x0' : G'.F.A}
    (hniso0 : ¬ isIsolated G'.F (Sum.inl x0')) (i0 : Fin ℓ) (hi0 : G'.a i0 = x0')
    {qa : GlueA G G'} (hqa : glueπA G G' (Sum.inr x0') = qa) :
    Sum.inl qa ∈ Finset.univ.image (fun p : P => (glue G G').labelVertex (p : Fin ℓ ⊕ Fin r)) := by
  have hmemG' : Sum.inl x0' ∈ G'.labelSupport :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨Sum.inl i0, Finset.mem_univ _, by
      show Sum.inl (G'.a i0) = Sum.inl x0'; rw [hi0]⟩, not_isIsolated_iff_notMem.mp hniso0⟩
  obtain ⟨p0, -, hp0⟩ := Finset.mem_image.mp (hGP'.2 hmemG')
  rcases p0 with ⟨i1 | j1, hpP⟩
  · have hx0' : G'.a i1 = x0' := Sum.inl_injective hp0
    refine Finset.mem_image.mpr ⟨⟨Sum.inl i1, hpP⟩, Finset.mem_univ _, ?_⟩
    show Sum.inl (glueπA G G' (Sum.inl (G.a i1))) = Sum.inl qa
    rw [glueπA_sound G G' i1, hx0', hqa]
  · simp [LabelledPattern.labelVertex] at hp0

/-- The `B`-side analogue of `mem_image_of_label`. -/
theorem mem_image_of_labelB (hGP : InClassP Δ k P G) {y0 : G.F.B}
    (hniso0 : ¬ isIsolated G.F (Sum.inr y0)) (j0 : Fin r) (hj0 : G.b j0 = y0)
    {qb : GlueB G G'} (hqb : glueπB G G' (Sum.inl y0) = qb) :
    Sum.inr qb ∈ Finset.univ.image (fun p : P => (glue G G').labelVertex (p : Fin ℓ ⊕ Fin r)) := by
  have hmemG : Sum.inr y0 ∈ G.labelSupport :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨Sum.inr j0, Finset.mem_univ _, by
      show Sum.inr (G.b j0) = Sum.inr y0; rw [hj0]⟩, not_isIsolated_iff_notMem.mp hniso0⟩
  obtain ⟨p0, -, hp0⟩ := Finset.mem_image.mp (hGP.2 hmemG)
  rcases p0 with ⟨i1 | j1, hpP⟩
  · simp [LabelledPattern.labelVertex] at hp0
  · have hy0 : G.b j1 = y0 := Sum.inr_injective hp0
    refine Finset.mem_image.mpr ⟨⟨Sum.inr j1, hpP⟩, Finset.mem_univ _, ?_⟩
    show Sum.inr (glueπB G G' (Sum.inl (G.b j1))) = Sum.inr qb
    rw [hy0, hqb]

/-- The `G'`-sided analogue of `mem_image_of_labelB`. -/
theorem mem_image_of_labelB' (hGP' : InClassP Δ k P G') {y0' : G'.F.B}
    (hniso0 : ¬ isIsolated G'.F (Sum.inr y0')) (j0 : Fin r) (hj0 : G'.b j0 = y0')
    {qb : GlueB G G'} (hqb : glueπB G G' (Sum.inr y0') = qb) :
    Sum.inr qb ∈ Finset.univ.image (fun p : P => (glue G G').labelVertex (p : Fin ℓ ⊕ Fin r)) := by
  have hmemG' : Sum.inr y0' ∈ G'.labelSupport :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨Sum.inr j0, Finset.mem_univ _, by
      show Sum.inr (G'.b j0) = Sum.inr y0'; rw [hj0]⟩, not_isIsolated_iff_notMem.mp hniso0⟩
  obtain ⟨p0, -, hp0⟩ := Finset.mem_image.mp (hGP'.2 hmemG')
  rcases p0 with ⟨i1 | j1, hpP⟩
  · simp [LabelledPattern.labelVertex] at hp0
  · have hy0' : G'.b j1 = y0' := Sum.inr_injective hp0
    refine Finset.mem_image.mpr ⟨⟨Sum.inr j1, hpP⟩, Finset.mem_univ _, ?_⟩
    show Sum.inr (glueπB G G' (Sum.inl (G.b j1))) = Sum.inr qb
    rw [glueπB_sound G G' j1, hy0', hqb]

/-- **Item 2's support bound**: `(glue G G').labelSupport` is covered by the image, under
`(glue G G').labelVertex`, of `P` alone (never needing a position outside `P`), given that `G`
and `G'` both already enjoy this for the same `P`. -/
theorem labelSupport_glue_subset (hG : InClassP Δ k P G) (hG' : InClassP Δ k P G') :
    (glue G G').labelSupport ⊆
      Finset.univ.image (fun p : P => (glue G G').labelVertex (p : Fin ℓ ⊕ Fin r)) := by
  intro v hv
  obtain ⟨hv1, hv2⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hv1
  have hniso : ¬ isIsolated (gluePattern G G') v := not_isIsolated_iff_notMem.mpr hv2
  rcases p with i | j
  · have hv_eq : v = Sum.inl (glueπA G G' (Sum.inl (G.a i))) := hp.symm
    subst hv_eq
    obtain ⟨x, hx_qa, hcase⟩ := exists_not_isolated_source_inl G G' hniso
    rcases hcase with ⟨x0, hx_eq, hniso0⟩ | ⟨x0', hx_eq, hniso0⟩
    · subst hx_eq
      have hlabel : IsGlueLabelA G G' (Sum.inl x0) :=
        IsGlueLabelA.of_glueπA_eq G G' hx_qa ⟨i, rfl⟩
      obtain ⟨i0, hi0⟩ := hlabel
      exact mem_image_of_label G G' hG hniso0 i0 hi0 hx_qa
    · subst hx_eq
      have hlabel : IsGlueLabelA G G' (Sum.inr x0') :=
        IsGlueLabelA.of_glueπA_eq G G' hx_qa ⟨i, rfl⟩
      obtain ⟨i0, hi0⟩ := hlabel
      exact mem_image_of_label' G G' hG' hniso0 i0 hi0 hx_qa
  · have hv_eq : v = Sum.inr (glueπB G G' (Sum.inl (G.b j))) := hp.symm
    subst hv_eq
    obtain ⟨y, hy_qb, hcase⟩ := exists_not_isolated_source_inr G G' hniso
    rcases hcase with ⟨y0, hy_eq, hniso0⟩ | ⟨y0', hy_eq, hniso0⟩
    · subst hy_eq
      have hlabel : IsGlueLabelB G G' (Sum.inl y0) :=
        IsGlueLabelB.of_glueπB_eq G G' hy_qb ⟨j, rfl⟩
      obtain ⟨j0, hj0⟩ := hlabel
      exact mem_image_of_labelB G G' hG hniso0 j0 hj0 hy_qb
    · subst hy_eq
      have hlabel : IsGlueLabelB G G' (Sum.inr y0') :=
        IsGlueLabelB.of_glueπB_eq G G' hy_qb ⟨j, rfl⟩
      obtain ⟨j0, hj0⟩ := hlabel
      exact mem_image_of_labelB' G G' hG' hniso0 j0 hj0 hy_qb

/-- **Item 2's card bound** (`InClassP.card_labelSupport_le` specialized to `glue G G'`, via
`labelSupport_glue_subset`): `|L⁺(glue G G')| ≤ |P|`. -/
theorem card_labelSupport_glue_le (hG : InClassP Δ k P G) (hG' : InClassP Δ k P G') :
    (glue G G').labelSupport.card ≤ P.card :=
  calc (glue G G').labelSupport.card
      ≤ (Finset.univ.image (fun p : P => (glue G G').labelVertex (p : Fin ℓ ⊕ Fin r))).card :=
        Finset.card_le_card (labelSupport_glue_subset G G' hG hG')
    _ ≤ (Finset.univ : Finset P).card := Finset.card_image_le
    _ = P.card := by rw [Finset.card_univ, Fintype.card_coe]

/-! ### `InClassP` closed under `glue`: the tree merge (item 2's depth/width step)

A generic fact about any `RootExactDecomposition`: a vertex that is in the root bag propagates
upward (towards the root) through every bag containing it. This is the key structural fact that
lets us show label vertices can only ever be "genuine entries" (in the sense of `connected`) at
the root, both before and after gluing. -/

theorem RootExactDecomposition.mem_bag_parent_of_mem_bag_root {Δ k : ℕ}
    (D : RootExactDecomposition G Δ k) {w : G.F.A ⊕ G.F.B} (hw : w ∈ D.bag D.root) {t : D.Node}
    (ht : w ∈ D.bag t) : t = D.root ∨ w ∈ D.bag (D.parent t) := by
  by_contra hcon
  push_neg at hcon
  exact hcon.1 (D.connected w t D.root ht (Or.inr hcon.2) hw (Or.inl rfl))

/-- The natural embedding of `G`'s vertices into the glued vertex set. -/
def embG : G.F.A ⊕ G.F.B → GlueA G G' ⊕ GlueB G G' :=
  Sum.map (fun x0 => glueπA G G' (Sum.inl x0)) (fun y0 => glueπB G G' (Sum.inl y0))

/-- The natural embedding of `G'`'s vertices into the glued vertex set. -/
def embG' : G'.F.A ⊕ G'.F.B → GlueA G G' ⊕ GlueB G G' :=
  Sum.map (fun x0' => glueπA G G' (Sum.inr x0')) (fun y0' => glueπB G G' (Sum.inr y0'))

theorem embG_labelVertex (p : Fin ℓ ⊕ Fin r) :
    embG G G' (G.labelVertex p) = (glue G G').labelVertex p := by cases p <;> rfl

theorem embG'_labelVertex (p : Fin ℓ ⊕ Fin r) :
    embG' G G' (G'.labelVertex p) = (glue G G').labelVertex p := by
  cases p with
  | inl i =>
      show Sum.inl (glueπA G G' (Sum.inr (G'.a i))) = Sum.inl (glueπA G G' (Sum.inl (G.a i)))
      rw [glueπA_sound]
  | inr j =>
      show Sum.inr (glueπB G G' (Sum.inr (G'.b j))) = Sum.inr (glueπB G G' (Sum.inl (G.b j)))
      rw [glueπB_sound]

theorem glueMult'_ne_zero_of_mult_ne_zero_left {x0 : G.F.A} {y0 : G.F.B} (h : G.F.mult x0 y0 ≠ 0) :
    glueMult' G G' (glueπA G G' (Sum.inl x0)) (glueπB G G' (Sum.inl y0)) ≠ 0 := by
  have hmem : (⟨(Sum.inl x0, Sum.inl y0), rfl⟩ :
      {p : (G.F.A ⊕ G'.F.A) × (G.F.B ⊕ G'.F.B) //
        (glueπA G G' p.1, glueπB G G' p.2) =
          (glueπA G G' (Sum.inl x0), glueπB G G' (Sum.inl y0))}) ∈ (Finset.univ : Finset _) :=
    Finset.mem_univ _
  have hle : glueMult0 G G' (Sum.inl x0) (Sum.inl y0) ≤
      glueMult' G G' (glueπA G G' (Sum.inl x0)) (glueπB G G' (Sum.inl y0)) :=
    Finset.single_le_sum (f := fun p0 => glueMult0 G G' p0.1.1 p0.1.2)
      (fun p0 _ => Nat.zero_le _) hmem
  intro hzero
  rw [hzero] at hle
  exact h (Nat.le_zero.mp hle)

theorem glueMult'_ne_zero_of_mult_ne_zero_right {x0' : G'.F.A} {y0' : G'.F.B}
    (h : G'.F.mult x0' y0' ≠ 0) :
    glueMult' G G' (glueπA G G' (Sum.inr x0')) (glueπB G G' (Sum.inr y0')) ≠ 0 := by
  have hmem : (⟨(Sum.inr x0', Sum.inr y0'), rfl⟩ :
      {p : (G.F.A ⊕ G'.F.A) × (G.F.B ⊕ G'.F.B) //
        (glueπA G G' p.1, glueπB G G' p.2) =
          (glueπA G G' (Sum.inr x0'), glueπB G G' (Sum.inr y0'))}) ∈ (Finset.univ : Finset _) :=
    Finset.mem_univ _
  have hle : glueMult0 G G' (Sum.inr x0') (Sum.inr y0') ≤
      glueMult' G G' (glueπA G G' (Sum.inr x0')) (glueπB G G' (Sum.inr y0')) :=
    Finset.single_le_sum (f := fun p0 => glueMult0 G G' p0.1.1 p0.1.2)
      (fun p0 _ => Nat.zero_le _) hmem
  intro hzero
  rw [hzero] at hle
  exact h (Nat.le_zero.mp hle)

theorem not_isIsolated_embG_of_not_isIsolated {w : G.F.A ⊕ G.F.B} (hw : ¬ isIsolated G.F w) :
    ¬ isIsolated (gluePattern G G') (embG G G' w) := by
  cases w with
  | inl x0 =>
      have hw' : ¬ ∀ y0, G.F.mult x0 y0 = 0 := hw
      push_neg at hw'
      obtain ⟨y0, hy0⟩ := hw'
      have hex : ¬ ∀ qb : GlueB G G', (gluePattern G G').mult (glueπA G G' (Sum.inl x0)) qb = 0 := by
        push_neg
        exact ⟨glueπB G G' (Sum.inl y0), glueMult'_ne_zero_of_mult_ne_zero_left G G' hy0⟩
      exact hex
  | inr y0 =>
      have hw' : ¬ ∀ x0, G.F.mult x0 y0 = 0 := hw
      push_neg at hw'
      obtain ⟨x0, hx0⟩ := hw'
      have hex : ¬ ∀ qa : GlueA G G', (gluePattern G G').mult qa (glueπB G G' (Sum.inl y0)) = 0 := by
        push_neg
        exact ⟨glueπA G G' (Sum.inl x0), glueMult'_ne_zero_of_mult_ne_zero_left G G' hx0⟩
      exact hex

theorem not_isIsolated_embG'_of_not_isIsolated {w : G'.F.A ⊕ G'.F.B} (hw : ¬ isIsolated G'.F w) :
    ¬ isIsolated (gluePattern G G') (embG' G G' w) := by
  cases w with
  | inl x0' =>
      have hw' : ¬ ∀ y0', G'.F.mult x0' y0' = 0 := hw
      push_neg at hw'
      obtain ⟨y0', hy0'⟩ := hw'
      have hex : ¬ ∀ qb : GlueB G G', (gluePattern G G').mult (glueπA G G' (Sum.inr x0')) qb = 0 := by
        push_neg
        exact ⟨glueπB G G' (Sum.inr y0'), glueMult'_ne_zero_of_mult_ne_zero_right G G' hy0'⟩
      exact hex
  | inr y0' =>
      have hw' : ¬ ∀ x0', G'.F.mult x0' y0' = 0 := hw
      push_neg at hw'
      obtain ⟨x0', hx0'⟩ := hw'
      have hex : ¬ ∀ qa : GlueA G G', (gluePattern G G').mult qa (glueπB G G' (Sum.inr y0')) = 0 := by
        push_neg
        exact ⟨glueπA G G' (Sum.inr x0'), glueMult'_ne_zero_of_mult_ne_zero_right G G' hx0'⟩
      exact hex

theorem embG_mem_labelSupport_of_mem {w : G.F.A ⊕ G.F.B} (hw : w ∈ G.labelSupport) :
    embG G G' w ∈ (glue G G').labelSupport := by
  obtain ⟨hw1, hw2⟩ := Finset.mem_sdiff.mp hw
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hw1
  have hniso : ¬ isIsolated G.F w := not_isIsolated_iff_notMem.mpr hw2
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨p, Finset.mem_univ _, ?_⟩,
    not_isIsolated_iff_notMem.mp (not_isIsolated_embG_of_not_isIsolated G G' hniso)⟩
  rw [← hp, embG_labelVertex]

theorem embG'_mem_labelSupport_of_mem {w : G'.F.A ⊕ G'.F.B} (hw : w ∈ G'.labelSupport) :
    embG' G G' w ∈ (glue G G').labelSupport := by
  obtain ⟨hw1, hw2⟩ := Finset.mem_sdiff.mp hw
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hw1
  have hniso : ¬ isIsolated G'.F w := not_isIsolated_iff_notMem.mpr hw2
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨p, Finset.mem_univ _, ?_⟩,
    not_isIsolated_iff_notMem.mp (not_isIsolated_embG'_of_not_isIsolated G G' hniso)⟩
  rw [← hp, embG'_labelVertex]

/-! ### The merged tree

Given root-exact decompositions `D` of `G` and `D'` of `G'` (both of depth `≤ Δ`, width `≤ k`),
we build a root-exact decomposition of `glue G G'` by *identifying* `D.root` and `D'.root`
(rather than attaching a fresh root above both, as `PatternsLabelledOps.DelNode` does for item
4): this keeps the depth bound at `Δ` (not `Δ + 1`). Since `G, G'` are parameters of `D, D'`'s
very *type*, every definition/lemma about the merged tree must take `G G'` explicitly, ahead of
`D D'` (there is no way around this: the elaborator needs `G, G'` in hand just to know `D, D'`'s
type). -/

variable {Δ k : ℕ} (D : RootExactDecomposition G Δ k) (D' : RootExactDecomposition G' Δ k)

/-- The merged node type: `D`'s nodes, together with `D'`'s *non-root* nodes (`D'.root` is
identified with `D.root`, so it is not a separate node here). -/
abbrev GlueNode (G G' : LabelledPattern ℓ r) (D : RootExactDecomposition G Δ k)
    (D' : RootExactDecomposition G' Δ k) := D.Node ⊕ {t' : D'.Node // t' ≠ D'.root}

/-- The merged root: `D.root`, now playing the role of both original roots. -/
def glueRoot : GlueNode G G' D D' := Sum.inl D.root

/-- The merged parent map: `D`'s own parent map on the left; on the right, `D'`'s parent map,
redirected into the merged root whenever it would otherwise reach `D'.root`. -/
noncomputable def glueParent : GlueNode G G' D D' → GlueNode G G' D D' :=
  Sum.elim (fun t => Sum.inl (D.parent t))
    (fun p => if hr : D'.parent p.1 = D'.root then Sum.inl D.root
      else Sum.inr ⟨D'.parent p.1, hr⟩)

/-- The merged bag map: `D`'s non-root bags, pushed forward via `embG`; `D'`'s non-root bags,
pushed forward via `embG'`; and the merged root's bag is `(glue G G').labelSupport` directly
(absorbing both original root bags, by `labelSupport_glue_subset`/`embG_mem_labelSupport_of_mem`
below). Isolated vertices are stripped before pushing a non-root bag forward: a vertex isolated
in its own original pattern, even if (needlessly) present in some bag of `D`/`D'`, carries no
edges to justify retaining it, and retaining it could otherwise break `connected` after gluing
(it is never forced to propagate towards the root the way a genuine label vertex is). -/
noncomputable def glueBag : GlueNode G G' D D' → Finset (GlueA G G' ⊕ GlueB G G')
  | Sum.inl t => if t = D.root then (glue G G').labelSupport
      else (D.bag t \ isolatedSet G.F).image (embG G G')
  | Sum.inr p => (D'.bag p.1 \ isolatedSet G'.F).image (embG' G G')

theorem glueParent_inl (t : D.Node) : glueParent G G' D D' (Sum.inl t) = Sum.inl (D.parent t) :=
  rfl

theorem glueParent_inr_root {t' : D'.Node} (h : t' ≠ D'.root) (hr : D'.parent t' = D'.root) :
    glueParent G G' D D' (Sum.inr ⟨t', h⟩) = glueRoot G G' D D' := by
  simp [glueParent, glueRoot, hr]

theorem glueParent_inr_of_ne {t' : D'.Node} (h : t' ≠ D'.root) (hr : D'.parent t' ≠ D'.root) :
    glueParent G G' D D' (Sum.inr ⟨t', h⟩) = Sum.inr ⟨D'.parent t', hr⟩ := by
  simp [glueParent, hr]

theorem glueParent_root : glueParent G G' D D' (glueRoot G G' D D') = glueRoot G G' D D' := by
  show Sum.inl (D.parent D.root) = Sum.inl D.root
  rw [D.parent_root]

theorem glueBag_inl_root : glueBag G G' D D' (Sum.inl D.root) = (glue G G').labelSupport :=
  if_pos rfl

theorem glueBag_root : glueBag G G' D D' (glueRoot G G' D D') = (glue G G').labelSupport :=
  glueBag_inl_root G G' D D'

theorem glueBag_inl_of_ne {t : D.Node} (h : t ≠ D.root) :
    glueBag G G' D D' (Sum.inl t) = (D.bag t \ isolatedSet G.F).image (embG G G') :=
  if_neg h

theorem glueBag_inr {t' : D'.Node} (h : t' ≠ D'.root) :
    glueBag G G' D D' (Sum.inr ⟨t', h⟩) = (D'.bag t' \ isolatedSet G'.F).image (embG' G G') := rfl

theorem glueParent_iterate_inl : ∀ (m : ℕ) (t : D.Node),
    (glueParent G G' D D')^[m] (Sum.inl t) = Sum.inl (D.parent^[m] t) := by
  intro m
  induction m with
  | zero => intro t; rfl
  | succ m ih =>
      intro t
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, glueParent_inl]

theorem glueParent_iterate_root (m : ℕ) :
    (glueParent G G' D D')^[m] (glueRoot G G' D D') = glueRoot G G' D D' := by
  show (glueParent G G' D D')^[m] (Sum.inl D.root) = Sum.inl D.root
  rw [glueParent_iterate_inl, Function.iterate_fixed D.parent_root m]

theorem glueParent_iterate_of_root : ∀ (m : ℕ) (t0' : D'.Node) (h0 : t0' ≠ D'.root),
    D'.parent^[m] t0' = D'.root →
      (glueParent G G' D D')^[m] (Sum.inr ⟨t0', h0⟩) = glueRoot G G' D D' := by
  intro m
  induction m with
  | zero => intro t0' h0 ht; exact absurd ht h0
  | succ m ih =>
      intro t0' h0 ht
      rw [Function.iterate_succ_apply]
      by_cases hr : D'.parent t0' = D'.root
      · rw [glueParent_inr_root G G' D D' h0 hr]
        exact glueParent_iterate_root G G' D D' m
      · rw [glueParent_inr_of_ne G G' D D' h0 hr]
        have ht' : D'.parent^[m] (D'.parent t0') = D'.root := by
          rwa [Function.iterate_succ_apply] at ht
        exact ih (D'.parent t0') hr ht'

theorem glueDepth_le (t : GlueNode G G' D D') :
    (glueParent G G' D D')^[Δ] t = glueRoot G G' D D' := by
  cases t with
  | inl t0 =>
      show (glueParent G G' D D')^[Δ] (Sum.inl t0) = Sum.inl D.root
      rw [glueParent_iterate_inl, D.depth_le]
  | inr t0 =>
      obtain ⟨t0', h0⟩ := t0
      exact glueParent_iterate_of_root G G' D D' Δ t0' h0 (D'.depth_le t0')

theorem glueCard_bag_le {P : Finset (Fin ℓ ⊕ Fin r)} (hP : P.card ≤ k) (hG : InClassP Δ k P G)
    (hG' : InClassP Δ k P G') (t : GlueNode G G' D D') : (glueBag G G' D D' t).card ≤ k := by
  cases t with
  | inl t0 =>
      by_cases hr : t0 = D.root
      · subst hr
        rw [glueBag_inl_root]
        exact (card_labelSupport_glue_le G G' hG hG').trans hP
      · rw [glueBag_inl_of_ne G G' D D' hr]
        exact Finset.card_image_le.trans ((Finset.card_le_card Finset.sdiff_subset).trans
          (D.card_bag_le t0))
  | inr t0 =>
      obtain ⟨t0', h0⟩ := t0
      rw [glueBag_inr G G' D D' h0]
      exact Finset.card_image_le.trans ((Finset.card_le_card Finset.sdiff_subset).trans
        (D'.card_bag_le t0'))

theorem glueExists_mem_bag (v : GlueA G G' ⊕ GlueB G G') (hv : ¬ isIsolated (gluePattern G G') v) :
    ∃ t, v ∈ glueBag G G' D D' t := by
  cases v with
  | inl qa =>
      obtain ⟨x, hx_qa, hcase⟩ := exists_not_isolated_source_inl G G' hv
      rcases hcase with ⟨x0, hx_eq, hniso0⟩ | ⟨x0', hx_eq, hniso0⟩
      · subst hx_eq
        obtain ⟨t0, ht0⟩ := D.exists_mem_bag (Sum.inl x0) hniso0
        by_cases hr : t0 = D.root
        · refine ⟨glueRoot G G' D D', ?_⟩
          rw [glueBag_root, ← hx_qa]
          have hmem : Sum.inl x0 ∈ G.labelSupport := by rw [← D.bag_root, ← hr]; exact ht0
          exact embG_mem_labelSupport_of_mem G G' hmem
        · refine ⟨Sum.inl t0, ?_⟩
          rw [glueBag_inl_of_ne G G' D D' hr, ← hx_qa]
          exact Finset.mem_image.mpr ⟨Sum.inl x0, Finset.mem_sdiff.mpr ⟨ht0,
            not_isIsolated_iff_notMem.mp hniso0⟩, rfl⟩
      · subst hx_eq
        obtain ⟨t0', ht0'⟩ := D'.exists_mem_bag (Sum.inl x0') hniso0
        by_cases hr : t0' = D'.root
        · refine ⟨glueRoot G G' D D', ?_⟩
          rw [glueBag_root, ← hx_qa]
          have hmem : Sum.inl x0' ∈ G'.labelSupport := by rw [← D'.bag_root, ← hr]; exact ht0'
          exact embG'_mem_labelSupport_of_mem G G' hmem
        · refine ⟨Sum.inr ⟨t0', hr⟩, ?_⟩
          rw [glueBag_inr G G' D D' hr, ← hx_qa]
          exact Finset.mem_image.mpr ⟨Sum.inl x0', Finset.mem_sdiff.mpr ⟨ht0',
            not_isIsolated_iff_notMem.mp hniso0⟩, rfl⟩
  | inr qb =>
      obtain ⟨y, hy_qb, hcase⟩ := exists_not_isolated_source_inr G G' hv
      rcases hcase with ⟨y0, hy_eq, hniso0⟩ | ⟨y0', hy_eq, hniso0⟩
      · subst hy_eq
        obtain ⟨t0, ht0⟩ := D.exists_mem_bag (Sum.inr y0) hniso0
        by_cases hr : t0 = D.root
        · refine ⟨glueRoot G G' D D', ?_⟩
          rw [glueBag_root, ← hy_qb]
          have hmem : Sum.inr y0 ∈ G.labelSupport := by rw [← D.bag_root, ← hr]; exact ht0
          exact embG_mem_labelSupport_of_mem G G' hmem
        · refine ⟨Sum.inl t0, ?_⟩
          rw [glueBag_inl_of_ne G G' D D' hr, ← hy_qb]
          exact Finset.mem_image.mpr ⟨Sum.inr y0, Finset.mem_sdiff.mpr ⟨ht0,
            not_isIsolated_iff_notMem.mp hniso0⟩, rfl⟩
      · subst hy_eq
        obtain ⟨t0', ht0'⟩ := D'.exists_mem_bag (Sum.inr y0') hniso0
        by_cases hr : t0' = D'.root
        · refine ⟨glueRoot G G' D D', ?_⟩
          rw [glueBag_root, ← hy_qb]
          have hmem : Sum.inr y0' ∈ G'.labelSupport := by rw [← D'.bag_root, ← hr]; exact ht0'
          exact embG'_mem_labelSupport_of_mem G G' hmem
        · refine ⟨Sum.inr ⟨t0', hr⟩, ?_⟩
          rw [glueBag_inr G G' D D' hr, ← hy_qb]
          exact Finset.mem_image.mpr ⟨Sum.inr y0', Finset.mem_sdiff.mpr ⟨ht0',
            not_isIsolated_iff_notMem.mp hniso0⟩, rfl⟩

theorem glueExists_edge_mem_bag (x : GlueA G G') (y : GlueB G G') (hxy : glueMult' G G' x y ≠ 0) :
    ∃ t, Sum.inl x ∈ glueBag G G' D D' t ∧ Sum.inr y ∈ glueBag G G' D D' t := by
  have hex : ∃ p0 : {p : (G.F.A ⊕ G'.F.A) × (G.F.B ⊕ G'.F.B) //
      (glueπA G G' p.1, glueπB G G' p.2) = (x, y)}, glueMult0 G G' p0.1.1 p0.1.2 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hxy (Finset.sum_eq_zero fun p0 _ => hcon p0)
  obtain ⟨⟨⟨x0, y0⟩, hxy0⟩, hne0⟩ := hex
  have hx0 : glueπA G G' x0 = x := congrArg Prod.fst hxy0
  have hy0 : glueπB G G' y0 = y := congrArg Prod.snd hxy0
  rcases x0 with x0 | x0' <;> rcases y0 with y0 | y0'
  · have hmul : G.F.mult x0 y0 ≠ 0 := hne0
    obtain ⟨t0, ht0x, ht0y⟩ := D.exists_edge_mem_bag x0 y0 hmul
    by_cases hr : t0 = D.root
    · refine ⟨glueRoot G G' D D', ?_, ?_⟩
      · rw [glueBag_root, ← hx0]
        have hmem : Sum.inl x0 ∈ G.labelSupport := by rw [← D.bag_root, ← hr]; exact ht0x
        exact embG_mem_labelSupport_of_mem G G' hmem
      · rw [glueBag_root, ← hy0]
        have hmem : Sum.inr y0 ∈ G.labelSupport := by rw [← D.bag_root, ← hr]; exact ht0y
        exact embG_mem_labelSupport_of_mem G G' hmem
    · refine ⟨Sum.inl t0, ?_, ?_⟩
      · rw [glueBag_inl_of_ne G G' D D' hr, ← hx0]
        exact Finset.mem_image.mpr ⟨Sum.inl x0, Finset.mem_sdiff.mpr ⟨ht0x,
          not_isIsolated_iff_notMem.mp (fun hiso => hmul (hiso y0))⟩, rfl⟩
      · rw [glueBag_inl_of_ne G G' D D' hr, ← hy0]
        exact Finset.mem_image.mpr ⟨Sum.inr y0, Finset.mem_sdiff.mpr ⟨ht0y,
          not_isIsolated_iff_notMem.mp (fun hiso => hmul (hiso x0))⟩, rfl⟩
  · exact absurd rfl hne0
  · exact absurd rfl hne0
  · have hmul : G'.F.mult x0' y0' ≠ 0 := hne0
    obtain ⟨t0', ht0x', ht0y'⟩ := D'.exists_edge_mem_bag x0' y0' hmul
    by_cases hr : t0' = D'.root
    · refine ⟨glueRoot G G' D D', ?_, ?_⟩
      · rw [glueBag_root, ← hx0]
        have hmem : Sum.inl x0' ∈ G'.labelSupport := by rw [← D'.bag_root, ← hr]; exact ht0x'
        exact embG'_mem_labelSupport_of_mem G G' hmem
      · rw [glueBag_root, ← hy0]
        have hmem : Sum.inr y0' ∈ G'.labelSupport := by rw [← D'.bag_root, ← hr]; exact ht0y'
        exact embG'_mem_labelSupport_of_mem G G' hmem
    · refine ⟨Sum.inr ⟨t0', hr⟩, ?_, ?_⟩
      · rw [glueBag_inr G G' D D' hr, ← hx0]
        exact Finset.mem_image.mpr ⟨Sum.inl x0', Finset.mem_sdiff.mpr ⟨ht0x',
          not_isIsolated_iff_notMem.mp (fun hiso => hmul (hiso y0'))⟩, rfl⟩
      · rw [glueBag_inr G G' D D' hr, ← hy0]
        exact Finset.mem_image.mpr ⟨Sum.inr y0', Finset.mem_sdiff.mpr ⟨ht0y',
          not_isIsolated_iff_notMem.mp (fun hiso => hmul (hiso x0'))⟩, rfl⟩

/-! ### `connected` for the merged tree

The crux: a label vertex can only ever be a "genuine entry" (in the sense of `connected`) at the
merged root, since its own original root bag already equals the *whole* label support, and
`RootExactDecomposition.mem_bag_parent_of_mem_bag_root` then forces it to propagate towards the
root wherever it appears. A *non*-label vertex, on the other hand, never crosses sides (its
`GlueRelA`/`GlueRelB`-class is a singleton, by `eq_of_glueπA_eq_of_not_isGlueLabelA` below), so
its entry status transfers faithfully from `D`'s (or `D'`'s) own `connected`. -/

theorem eq_of_glueπA_eq_of_not_isGlueLabelA {x y : G.F.A ⊕ G'.F.A}
    (heq : glueπA G G' x = glueπA G G' y) (hx : ¬ IsGlueLabelA G G' x) : x = y :=
  (glueπA_eq_iff_eq_or_isGlueLabelA G G' heq).resolve_right fun h => hx h.1

theorem eq_of_glueπB_eq_of_not_isGlueLabelB {x y : G.F.B ⊕ G'.F.B}
    (heq : glueπB G G' x = glueπB G G' y) (hx : ¬ IsGlueLabelB G G' x) : x = y :=
  (glueπB_eq_iff_eq_or_isGlueLabelB G G' heq).resolve_right fun h => hx h.1

theorem notMem_labelSupport_glue_inl_of_not_isGlueLabelA {x : G.F.A ⊕ G'.F.A}
    (hx : ¬ IsGlueLabelA G G' x) : Sum.inl (glueπA G G' x) ∉ (glue G G').labelSupport := by
  intro hmem
  obtain ⟨hmem1, -⟩ := Finset.mem_sdiff.mp hmem
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hmem1
  rcases p with i | j
  · have heq0 : glueπA G G' (Sum.inl (G.a i)) = glueπA G G' x := Sum.inl_injective hp
    have heq : x = Sum.inl (G.a i) := eq_of_glueπA_eq_of_not_isGlueLabelA G G' heq0.symm hx
    exact hx (by rw [heq]; exact ⟨i, rfl⟩)
  · simp [LabelledPattern.labelVertex] at hp

theorem notMem_labelSupport_glue_inr_of_not_isGlueLabelB {x : G.F.B ⊕ G'.F.B}
    (hx : ¬ IsGlueLabelB G G' x) : Sum.inr (glueπB G G' x) ∉ (glue G G').labelSupport := by
  intro hmem
  obtain ⟨hmem1, -⟩ := Finset.mem_sdiff.mp hmem
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hmem1
  rcases p with i | j
  · simp [LabelledPattern.labelVertex] at hp
  · have heq0 : glueπB G G' (Sum.inl (G.b j)) = glueπB G G' x := Sum.inr_injective hp
    have heq : x = Sum.inl (G.b j) := eq_of_glueπB_eq_of_not_isGlueLabelB G G' heq0.symm hx
    exact hx (by rw [heq]; exact ⟨j, rfl⟩)

theorem notMem_labelSupport_glue_of_notMem_left {w0 : G.F.A ⊕ G.F.B}
    (hniso : ¬ isIsolated G.F w0) (hnl : w0 ∉ G.labelSupport) :
    embG G G' w0 ∉ (glue G G').labelSupport := by
  cases w0 with
  | inl x0 =>
      apply notMem_labelSupport_glue_inl_of_not_isGlueLabelA G G' (x := Sum.inl x0)
      intro ⟨i, hi⟩
      exact hnl (Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨Sum.inl i, Finset.mem_univ _, by
        show Sum.inl (G.a i) = Sum.inl x0; rw [hi]⟩, not_isIsolated_iff_notMem.mp hniso⟩)
  | inr y0 =>
      apply notMem_labelSupport_glue_inr_of_not_isGlueLabelB G G' (x := Sum.inl y0)
      intro ⟨j, hj⟩
      exact hnl (Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨Sum.inr j, Finset.mem_univ _, by
        show Sum.inr (G.b j) = Sum.inr y0; rw [hj]⟩, not_isIsolated_iff_notMem.mp hniso⟩)

theorem notMem_labelSupport_glue_of_notMem_right {w0' : G'.F.A ⊕ G'.F.B}
    (hniso : ¬ isIsolated G'.F w0') (hnl : w0' ∉ G'.labelSupport) :
    embG' G G' w0' ∉ (glue G G').labelSupport := by
  cases w0' with
  | inl x0' =>
      apply notMem_labelSupport_glue_inl_of_not_isGlueLabelA G G' (x := Sum.inr x0')
      intro ⟨i, hi⟩
      exact hnl (Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨Sum.inl i, Finset.mem_univ _, by
        show Sum.inl (G'.a i) = Sum.inl x0'; rw [hi]⟩, not_isIsolated_iff_notMem.mp hniso⟩)
  | inr y0' =>
      apply notMem_labelSupport_glue_inr_of_not_isGlueLabelB G G' (x := Sum.inr y0')
      intro ⟨j, hj⟩
      exact hnl (Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨Sum.inr j, Finset.mem_univ _, by
        show Sum.inr (G'.b j) = Sum.inr y0'; rw [hj]⟩, not_isIsolated_iff_notMem.mp hniso⟩)

theorem glueBag_propagate_inl {t0 : D.Node} {w0 : G.F.A ⊕ G.F.B} (hw0 : w0 ∈ G.labelSupport)
    (ht0 : w0 ∈ D.bag t0) (hroot : t0 ≠ D.root) :
    embG G G' w0 ∈ glueBag G G' D D' (glueParent G G' D D' (Sum.inl t0)) := by
  rw [glueParent_inl]
  rcases RootExactDecomposition.mem_bag_parent_of_mem_bag_root G D
      (by rw [D.bag_root]; exact hw0) ht0 with h | h
  · exact absurd h hroot
  · by_cases hr : D.parent t0 = D.root
    · rw [hr, glueBag_inl_root]
      exact embG_mem_labelSupport_of_mem G G' hw0
    · rw [glueBag_inl_of_ne G G' D D' hr]
      have hniso : w0 ∉ isolatedSet G.F := (Finset.mem_sdiff.mp hw0).2
      exact Finset.mem_image.mpr ⟨w0, Finset.mem_sdiff.mpr ⟨h, hniso⟩, rfl⟩

theorem glueBag_propagate_inr {t0' : D'.Node} {h0 : t0' ≠ D'.root} {w0' : G'.F.A ⊕ G'.F.B}
    (hw0' : w0' ∈ G'.labelSupport) (ht0' : w0' ∈ D'.bag t0') :
    embG' G G' w0' ∈ glueBag G G' D D' (glueParent G G' D D' (Sum.inr ⟨t0', h0⟩)) := by
  rcases RootExactDecomposition.mem_bag_parent_of_mem_bag_root G' D'
      (by rw [D'.bag_root]; exact hw0') ht0' with h | h
  · exact absurd h h0
  · by_cases hr : D'.parent t0' = D'.root
    · rw [glueParent_inr_root G G' D D' h0 hr, glueBag_root]
      exact embG'_mem_labelSupport_of_mem G G' hw0'
    · rw [glueParent_inr_of_ne G G' D D' h0 hr, glueBag_inr G G' D D' hr]
      have hniso : w0' ∉ isolatedSet G'.F := (Finset.mem_sdiff.mp hw0').2
      exact Finset.mem_image.mpr ⟨w0', Finset.mem_sdiff.mpr ⟨h, hniso⟩, rfl⟩

/-- A non-isolated, non-label vertex present in a bag is present (via `embG`) in the
corresponding merged bag of the *parent* node, regardless of whether that parent is the merged
root: if it were, the vertex would (since the root bag is exactly `G.labelSupport`) have to be a
label vertex, contradiction. This is the analogue of `glueBag_propagate_inl` for non-label
vertices: it does not need `RootExactDecomposition.mem_bag_parent_of_mem_bag_root` (that fact is
specific to label vertices), only the vertex's own non-isolation. -/
theorem glueBag_mem_of_mem_bag_parent {t0 : D.Node} {w0 : G.F.A ⊕ G.F.B}
    (hniso : ¬ isIsolated G.F w0) (hnl : w0 ∉ G.labelSupport) (hmem : w0 ∈ D.bag (D.parent t0)) :
    embG G G' w0 ∈ glueBag G G' D D' (glueParent G G' D D' (Sum.inl t0)) := by
  rw [glueParent_inl]
  by_cases hr : D.parent t0 = D.root
  · exact absurd (by rw [← D.bag_root, ← hr]; exact hmem) hnl
  · rw [glueBag_inl_of_ne G G' D D' hr]
    exact Finset.mem_image.mpr ⟨w0, Finset.mem_sdiff.mpr ⟨hmem,
      not_isIsolated_iff_notMem.mp hniso⟩, rfl⟩

/-- The `G'`-sided analogue of `glueBag_mem_of_mem_bag_parent`. -/
theorem glueBag_mem_of_mem_bag_parent' {t0' : D'.Node} {h0 : t0' ≠ D'.root} {w0' : G'.F.A ⊕ G'.F.B}
    (hniso : ¬ isIsolated G'.F w0') (hnl : w0' ∉ G'.labelSupport)
    (hmem : w0' ∈ D'.bag (D'.parent t0')) :
    embG' G G' w0' ∈ glueBag G G' D D' (glueParent G G' D D' (Sum.inr ⟨t0', h0⟩)) := by
  by_cases hr : D'.parent t0' = D'.root
  · exact absurd (by rw [← D'.bag_root, ← hr]; exact hmem) hnl
  · rw [glueParent_inr_of_ne G G' D D' h0 hr, glueBag_inr G G' D D' hr]
    exact Finset.mem_image.mpr ⟨w0', Finset.mem_sdiff.mpr ⟨hmem,
      not_isIsolated_iff_notMem.mp hniso⟩, rfl⟩

/-- If a vertex `t0`'s bag claims to be a "genuine entry" for `v` (non-root, with `v` absent
from the parent's bag), its witness in the original decomposition `D` must be a non-isolated,
*non*-label vertex of `G` (also exposing the fact that it is literally present in `D.bag t0`,
needed later to invoke `D.connected` directly). A label-vertex witness would, by
`glueBag_propagate_inl`, always propagate to the parent, contradicting the "genuine entry"
hypothesis. -/
theorem glueNoEntry_inl {t0 : D.Node} (h0 : t0 ≠ D.root) {v : GlueA G G' ⊕ GlueB G G'}
    (hv : v ∈ glueBag G G' D D' (Sum.inl t0))
    (hnv : v ∉ glueBag G G' D D' (glueParent G G' D D' (Sum.inl t0))) :
    ∃ w0 : G.F.A ⊕ G.F.B, embG G G' w0 = v ∧ w0 ∈ D.bag t0 ∧ ¬ isIsolated G.F w0 ∧
      w0 ∉ G.labelSupport := by
  rw [glueBag_inl_of_ne G G' D D' h0] at hv
  obtain ⟨w0, hw0mem, hw0eq⟩ := Finset.mem_image.mp hv
  obtain ⟨hw0bag, hw0niso⟩ := Finset.mem_sdiff.mp hw0mem
  refine ⟨w0, hw0eq, hw0bag, not_isIsolated_iff_notMem.mpr hw0niso, ?_⟩
  intro hlabel
  apply hnv
  rw [← hw0eq]
  exact glueBag_propagate_inl G G' D D' hlabel hw0bag h0

/-- The `G'`-sided analogue of `glueNoEntry_inl`. -/
theorem glueNoEntry_inr {t0' : D'.Node} (h0 : t0' ≠ D'.root) {v : GlueA G G' ⊕ GlueB G G'}
    (hv : v ∈ glueBag G G' D D' (Sum.inr ⟨t0', h0⟩))
    (hnv : v ∉ glueBag G G' D D' (glueParent G G' D D' (Sum.inr ⟨t0', h0⟩))) :
    ∃ w0' : G'.F.A ⊕ G'.F.B, embG' G G' w0' = v ∧ w0' ∈ D'.bag t0' ∧ ¬ isIsolated G'.F w0' ∧
      w0' ∉ G'.labelSupport := by
  rw [glueBag_inr G G' D D' h0] at hv
  obtain ⟨w0', hw0mem, hw0eq⟩ := Finset.mem_image.mp hv
  obtain ⟨hw0bag, hw0niso⟩ := Finset.mem_sdiff.mp hw0mem
  refine ⟨w0', hw0eq, hw0bag, not_isIsolated_iff_notMem.mpr hw0niso, ?_⟩
  intro hlabel
  apply hnv
  rw [← hw0eq]
  exact glueBag_propagate_inr G G' D D' hlabel hw0bag

/-- Two non-isolated, non-label original `G`-vertices that land on the same glued vertex must
already have been equal: a non-label vertex's `GlueRelA`/`GlueRelB`-class is a singleton (by
`eq_of_glueπA_eq_of_not_isGlueLabelA`/`eq_of_glueπB_eq_of_not_isGlueLabelB`), so gluing can never
identify it with anything else. -/
theorem embG_injOn_not_label {w0 w1 : G.F.A ⊕ G.F.B} (hw0 : w0 ∉ G.labelSupport)
    (hniso0 : ¬ isIsolated G.F w0) (heq : embG G G' w0 = embG G G' w1) : w0 = w1 := by
  cases w0 with
  | inl x0 =>
      cases w1 with
      | inl x1 =>
          have hxeq : glueπA G G' (Sum.inl x0) = glueπA G G' (Sum.inl x1) := Sum.inl_injective heq
          have hnl : ¬ IsGlueLabelA G G' (Sum.inl x0) := fun ⟨i, hi⟩ =>
            hw0 (Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨Sum.inl i, Finset.mem_univ _, by
              show Sum.inl (G.a i) = Sum.inl x0; rw [hi]⟩, not_isIsolated_iff_notMem.mp hniso0⟩)
          have hxx : Sum.inl x0 = (Sum.inl x1 : G.F.A ⊕ G'.F.A) :=
            eq_of_glueπA_eq_of_not_isGlueLabelA G G' hxeq hnl
          rw [Sum.inl_injective hxx]
      | inr y1 => simp [embG] at heq
  | inr y0 =>
      cases w1 with
      | inl x1 => simp [embG] at heq
      | inr y1 =>
          have hyeq : glueπB G G' (Sum.inl y0) = glueπB G G' (Sum.inl y1) := Sum.inr_injective heq
          have hnl : ¬ IsGlueLabelB G G' (Sum.inl y0) := fun ⟨j, hj⟩ =>
            hw0 (Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨Sum.inr j, Finset.mem_univ _, by
              show Sum.inr (G.b j) = Sum.inr y0; rw [hj]⟩, not_isIsolated_iff_notMem.mp hniso0⟩)
          have hyy : Sum.inl y0 = (Sum.inl y1 : G.F.B ⊕ G'.F.B) :=
            eq_of_glueπB_eq_of_not_isGlueLabelB G G' hyeq hnl
          rw [Sum.inl_injective hyy]

/-- The `G'`-sided analogue of `embG_injOn_not_label`. -/
theorem embG'_injOn_not_label {w0' w1' : G'.F.A ⊕ G'.F.B} (hw0' : w0' ∉ G'.labelSupport)
    (hniso0' : ¬ isIsolated G'.F w0') (heq : embG' G G' w0' = embG' G G' w1') : w0' = w1' := by
  cases w0' with
  | inl x0' =>
      cases w1' with
      | inl x1' =>
          have hxeq : glueπA G G' (Sum.inr x0') = glueπA G G' (Sum.inr x1') := Sum.inl_injective heq
          have hnl : ¬ IsGlueLabelA G G' (Sum.inr x0') := fun ⟨i, hi⟩ =>
            hw0' (Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨Sum.inl i, Finset.mem_univ _, by
              show Sum.inl (G'.a i) = Sum.inl x0'; rw [hi]⟩, not_isIsolated_iff_notMem.mp hniso0'⟩)
          have hxx : Sum.inr x0' = (Sum.inr x1' : G.F.A ⊕ G'.F.A) :=
            eq_of_glueπA_eq_of_not_isGlueLabelA G G' hxeq hnl
          rw [Sum.inr_injective hxx]
      | inr y1' => simp [embG'] at heq
  | inr y0' =>
      cases w1' with
      | inl x1' => simp [embG'] at heq
      | inr y1' =>
          have hyeq : glueπB G G' (Sum.inr y0') = glueπB G G' (Sum.inr y1') := Sum.inr_injective heq
          have hnl : ¬ IsGlueLabelB G G' (Sum.inr y0') := fun ⟨j, hj⟩ =>
            hw0' (Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨Sum.inr j, Finset.mem_univ _, by
              show Sum.inr (G'.b j) = Sum.inr y0'; rw [hj]⟩, not_isIsolated_iff_notMem.mp hniso0'⟩)
          have hyy : Sum.inr y0' = (Sum.inr y1' : G.F.B ⊕ G'.F.B) :=
            eq_of_glueπB_eq_of_not_isGlueLabelB G G' hyeq hnl
          rw [Sum.inr_injective hyy]

/-- A non-isolated, non-label `G`-vertex can never coincide (via gluing) with *any* `G'`-vertex:
the cross-side case of the same singleton-class fact used by `embG_injOn_not_label`. -/
theorem not_embG_eq_embG'_of_not_label {w0 : G.F.A ⊕ G.F.B} {w0' : G'.F.A ⊕ G'.F.B}
    (hniso : ¬ isIsolated G.F w0) (hnl : w0 ∉ G.labelSupport) :
    embG G G' w0 ≠ embG' G G' w0' := by
  intro heq
  cases w0 with
  | inl x0 =>
      cases w0' with
      | inl x0' =>
          have hxeq : glueπA G G' (Sum.inl x0) = glueπA G G' (Sum.inr x0') := Sum.inl_injective heq
          have hnlA : ¬ IsGlueLabelA G G' (Sum.inl x0) := fun ⟨i, hi⟩ =>
            hnl (Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨Sum.inl i, Finset.mem_univ _, by
              show Sum.inl (G.a i) = Sum.inl x0; rw [hi]⟩, not_isIsolated_iff_notMem.mp hniso⟩)
          exact absurd (eq_of_glueπA_eq_of_not_isGlueLabelA G G' hxeq hnlA) (by simp)
      | inr y0' => simp [embG, embG'] at heq
  | inr y0 =>
      cases w0' with
      | inl x0' => simp [embG, embG'] at heq
      | inr y0' =>
          have hyeq : glueπB G G' (Sum.inl y0) = glueπB G G' (Sum.inr y0') := Sum.inr_injective heq
          have hnlB : ¬ IsGlueLabelB G G' (Sum.inl y0) := fun ⟨j, hj⟩ =>
            hnl (Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨Sum.inr j, Finset.mem_univ _, by
              show Sum.inr (G.b j) = Sum.inr y0; rw [hj]⟩, not_isIsolated_iff_notMem.mp hniso⟩)
          exact absurd (eq_of_glueπB_eq_of_not_isGlueLabelB G G' hyeq hnlB) (by simp)

/-- **The merged tree's `connected` property.** Every genuine entry for `v` other than the
merged root is witnessed by a non-isolated, non-label original vertex (`glueNoEntry_inl`/`_inr`);
such witnesses never cross sides (`not_embG_eq_embG'_of_not_label`) and are unique on their own
side (`embG_injOn_not_label`/`embG'_injOn_not_label`), so the whole statement reduces to `D`'s
(or `D'`'s) own `connected`, except when one side claims the merged root as its entry, which
forces `v` into `(glue G G').labelSupport` — contradicting any non-label witness on the other
side via `notMem_labelSupport_glue_of_notMem_left`/`_right`. -/
theorem glueConnected (v : GlueA G G' ⊕ GlueB G G') (t1 t2 : GlueNode G G' D D')
    (ht1 : v ∈ glueBag G G' D D' t1)
    (hd1 : t1 = glueRoot G G' D D' ∨ v ∉ glueBag G G' D D' (glueParent G G' D D' t1))
    (ht2 : v ∈ glueBag G G' D D' t2)
    (hd2 : t2 = glueRoot G G' D D' ∨ v ∉ glueBag G G' D D' (glueParent G G' D D' t2)) :
    t1 = t2 := by
  have key1 : ∀ {t0 : D.Node}, v ∈ glueBag G G' D D' (Sum.inl t0) →
      ((Sum.inl t0 : GlueNode G G' D D') = glueRoot G G' D D' ∨
        v ∉ glueBag G G' D D' (glueParent G G' D D' (Sum.inl t0))) →
      t0 = D.root ∨ ∃ w0 : G.F.A ⊕ G.F.B, embG G G' w0 = v ∧ w0 ∈ D.bag t0 ∧
        ¬ isIsolated G.F w0 ∧ w0 ∉ G.labelSupport := by
    intro t0 hv hd
    rcases hd with hd | hd
    · exact Or.inl (Sum.inl_injective hd)
    · by_cases hr : t0 = D.root
      · exact Or.inl hr
      · exact Or.inr (glueNoEntry_inl G G' D D' hr hv hd)
  have key2 : ∀ {t0' : D'.Node} (h0 : t0' ≠ D'.root), v ∈ glueBag G G' D D' (Sum.inr ⟨t0', h0⟩) →
      ((Sum.inr ⟨t0', h0⟩ : GlueNode G G' D D') = glueRoot G G' D D' ∨
        v ∉ glueBag G G' D D' (glueParent G G' D D' (Sum.inr ⟨t0', h0⟩))) →
      ∃ w0' : G'.F.A ⊕ G'.F.B, embG' G G' w0' = v ∧ w0' ∈ D'.bag t0' ∧ ¬ isIsolated G'.F w0' ∧
        w0' ∉ G'.labelSupport := by
    intro t0' h0 hv hd
    rcases hd with hd | hd
    · exact absurd hd (by simp [glueRoot])
    · exact glueNoEntry_inr G G' D D' h0 hv hd
  rcases t1 with t10 | ⟨t10', h10⟩ <;> rcases t2 with t20 | ⟨t20', h20⟩
  · -- (inl, inl)
    rcases key1 ht1 hd1 with hr1 | ⟨w0, hw0eq, hw0bag, hw0niso, hw0nl⟩
    · rcases key1 ht2 hd2 with hr2 | ⟨w0', hw0eq', hw0bag', hw0niso', hw0nl'⟩
      · rw [hr1, hr2]
      · exfalso
        rw [hr1, glueBag_inl_root] at ht1
        exact notMem_labelSupport_glue_of_notMem_left G G' hw0niso' hw0nl'
          (by rw [hw0eq']; exact ht1)
    · rcases key1 ht2 hd2 with hr2 | ⟨w0', hw0eq', hw0bag', hw0niso', hw0nl'⟩
      · exfalso
        rw [hr2, glueBag_inl_root] at ht2
        exact notMem_labelSupport_glue_of_notMem_left G G' hw0niso hw0nl
          (by rw [hw0eq]; exact ht2)
      · have heq : w0 = w0' := embG_injOn_not_label G G' hw0nl hw0niso (hw0eq.trans hw0eq'.symm)
        subst heq
        have hd1' : t10 = D.root ∨ w0 ∉ D.bag (D.parent t10) := by
          by_cases hr : t10 = D.root
          · exact Or.inl hr
          · refine Or.inr (fun hmem => ?_)
            rcases hd1 with hd1l | hd1r
            · exact hr (Sum.inl_injective hd1l)
            · exact hd1r (by rw [← hw0eq]; exact glueBag_mem_of_mem_bag_parent G G' D D' hw0niso hw0nl hmem)
        have hd2' : t20 = D.root ∨ w0 ∉ D.bag (D.parent t20) := by
          by_cases hr : t20 = D.root
          · exact Or.inl hr
          · refine Or.inr (fun hmem => ?_)
            rcases hd2 with hd2l | hd2r
            · exact hr (Sum.inl_injective hd2l)
            · exact hd2r (by rw [← hw0eq]; exact glueBag_mem_of_mem_bag_parent G G' D D' hw0niso hw0nl hmem)
        exact congrArg Sum.inl (D.connected w0 t10 t20 hw0bag hd1' hw0bag' hd2')
  · -- (inl, inr): always contradictory.
    exfalso
    rcases key1 ht1 hd1 with hr1 | ⟨w0, hw0eq, hw0bag, hw0niso, hw0nl⟩
    · obtain ⟨w0', hw0eq', -, hw0niso', hw0nl'⟩ := key2 h20 ht2 hd2
      rw [hr1, glueBag_inl_root] at ht1
      exact notMem_labelSupport_glue_of_notMem_right G G' hw0niso' hw0nl'
        (by rw [hw0eq']; exact ht1)
    · obtain ⟨w0', hw0eq', -, hw0niso', hw0nl'⟩ := key2 h20 ht2 hd2
      exact not_embG_eq_embG'_of_not_label G G' hw0niso hw0nl (hw0eq.trans hw0eq'.symm)
  · -- (inr, inl): always contradictory, symmetric to the above.
    exfalso
    obtain ⟨w0, hw0eq, -, hw0niso, hw0nl⟩ := key2 h10 ht1 hd1
    rcases key1 ht2 hd2 with hr2 | ⟨w0', hw0eq', -, hw0niso', hw0nl'⟩
    · rw [hr2, glueBag_inl_root] at ht2
      exact notMem_labelSupport_glue_of_notMem_right G G' hw0niso hw0nl
        (by rw [hw0eq]; exact ht2)
    · exact not_embG_eq_embG'_of_not_label G G' hw0niso' hw0nl' (hw0eq'.trans hw0eq.symm)
  · -- (inr, inr)
    obtain ⟨w0, hw0eq, hw0bag, hw0niso, hw0nl⟩ := key2 h10 ht1 hd1
    obtain ⟨w0', hw0eq', hw0bag', hw0niso', hw0nl'⟩ := key2 h20 ht2 hd2
    have heq : w0 = w0' := embG'_injOn_not_label G G' hw0nl hw0niso (hw0eq.trans hw0eq'.symm)
    subst heq
    have hd1' : t10' = D'.root ∨ w0 ∉ D'.bag (D'.parent t10') := by
      by_cases hr : t10' = D'.root
      · exact Or.inl hr
      · refine Or.inr (fun hmem => ?_)
        rcases hd1 with hd1l | hd1r
        · exact absurd hd1l (by simp [glueRoot])
        · exact hd1r (by rw [← hw0eq]; exact glueBag_mem_of_mem_bag_parent' G G' D D' hw0niso hw0nl hmem)
    have hd2' : t20' = D'.root ∨ w0 ∉ D'.bag (D'.parent t20') := by
      by_cases hr : t20' = D'.root
      · exact Or.inl hr
      · refine Or.inr (fun hmem => ?_)
        rcases hd2 with hd2l | hd2r
        · exact absurd hd2l (by simp [glueRoot])
        · exact hd2r (by rw [← hw0eq]; exact glueBag_mem_of_mem_bag_parent' G G' D D' hw0niso hw0nl hmem)
    exact congrArg Sum.inr (Subtype.ext (D'.connected w0 t10' t20' hw0bag hd1' hw0bag' hd2'))

/-! ### Assembling `inClassP_glue` -/

/-- The merged root-exact decomposition of `glue G G'`, built from root-exact decompositions
`D` of `G` and `D'` of `G'` by identifying their roots. -/
noncomputable def glueDecomposition {Δ k : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)} (hP : P.card ≤ k)
    (D : RootExactDecomposition G Δ k) (D' : RootExactDecomposition G' Δ k)
    (hG : InClassP Δ k P G) (hG' : InClassP Δ k P G') :
    RootExactDecomposition (glue G G') Δ k where
  Node := GlueNode G G' D D'
  root := glueRoot G G' D D'
  parent := glueParent G G' D D'
  parent_root := glueParent_root G G' D D'
  depth_le := glueDepth_le G G' D D'
  bag := glueBag G G' D D'
  bag_root := glueBag_root G G' D D'
  card_bag_le := glueCard_bag_le G G' D D' hP hG hG'
  exists_mem_bag := glueExists_mem_bag G G' D D'
  exists_edge_mem_bag := glueExists_edge_mem_bag G G' D D'
  connected := glueConnected G G' D D'

/-- **Item 2 of `lem:labelled-ops`**: `𝒯^{Δ,k}_P(ℓ,r)` is closed under `glue`. Combined with
`labelledHom_glue`, this is what lets `span𝔗P` absorb the product of two generators (see
`span𝔗P_mul_mem`). -/
theorem inClassP_glue {Δ k : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)} (hP : P.card ≤ k)
    (hG : InClassP Δ k P G) (hG' : InClassP Δ k P G') : InClassP Δ k P (glue G G') := by
  obtain ⟨D⟩ := hG.1
  obtain ⟨D'⟩ := hG'.1
  exact ⟨⟨glueDecomposition G G' hP D D' hG hG'⟩, labelSupport_glue_subset G G' hG hG'⟩

end Lax461425Proofs.PatternsLabelledGlue
