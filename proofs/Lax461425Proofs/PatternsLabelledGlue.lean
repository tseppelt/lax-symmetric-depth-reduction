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

@[simp] theorem quotLiftEquiv_apply {α : Type*} (rel : α → α → Prop) (β : Type*)
    (H : Quot rel → β) (a : α) : ((quotLiftEquiv rel β H : {f : α → β // Respects rel f}) : α → β)
      a = H (Quot.mk rel a) := rfl

/-! ### The glued vertex sets -/

variable (G G' : LabelledPattern ℓ r)

/-- The generating relation on `G.F.A ⊕ G'.F.A` identifying `a_i` with `a'_i`. -/
def GlueRelA : G.F.A ⊕ G'.F.A → G.F.A ⊕ G'.F.A → Prop :=
  fun x y => ∃ i, x = Sum.inl (G.a i) ∧ y = Sum.inr (G'.a i)

/-- The generating relation on `G.F.B ⊕ G'.F.B` identifying `b_j` with `b'_j`. -/
def GlueRelB : G.F.B ⊕ G'.F.B → G.F.B ⊕ G'.F.B → Prop :=
  fun x y => ∃ j, x = Sum.inl (G.b j) ∧ y = Sum.inr (G'.b j)

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

/-- Functions on the glued `A`-side vertex set correspond exactly to pairs of functions on the
two original `A`-sides that agree at every identified label pair `(a_i, a'_i)`. This is the
"crux" bijection: built directly via the universal property of `Quot` (never via the closure of
`GlueRelA` under symmetry/transitivity). -/
noncomputable def glueLabelEquivA (γ : Type*) :
    (GlueA G G' → γ) ≃
      {p : (G.F.A → γ) × (G'.F.A → γ) // ∀ i, p.1 (G.a i) = p.2 (G'.a i)} where
  toFun H := ⟨(H ∘ glueπA G G' ∘ Sum.inl, H ∘ glueπA G G' ∘ Sum.inr), fun i => by
    simp [glueπA_sound G G' i]⟩
  invFun p := Quot.lift (Sum.elim p.1.1 p.1.2) (by
    rintro a b ⟨i, rfl, rfl⟩
    simpa using p.2 i)
  left_inv H := funext fun q => Quot.inductionOn q (fun a => by cases a <;> rfl)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> rfl

/-- The `B`-side analogue of `glueLabelEquivA`. -/
noncomputable def glueLabelEquivB (γ : Type*) :
    (GlueB G G' → γ) ≃
      {p : (G.F.B → γ) × (G'.F.B → γ) // ∀ j, p.1 (G.b j) = p.2 (G'.b j)} where
  toFun H := ⟨(H ∘ glueπB G G' ∘ Sum.inl, H ∘ glueπB G G' ∘ Sum.inr), fun j => by
    simp [glueπB_sound G G' j]⟩
  invFun p := Quot.lift (Sum.elim p.1.1 p.1.2) (by
    rintro a b ⟨j, rfl, rfl⟩
    simpa using p.2 j)
  left_inv H := funext fun q => Quot.inductionOn q (fun a => by cases a <;> rfl)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> rfl

@[simp] theorem glueLabelEquivA_symm_apply_inl (γ : Type*)
    (p : {p : (G.F.A → γ) × (G'.F.A → γ) // ∀ i, p.1 (G.a i) = p.2 (G'.a i)}) (x : G.F.A) :
    (glueLabelEquivA G G' γ).symm p (glueπA G G' (Sum.inl x)) = p.1.1 x := rfl

@[simp] theorem glueLabelEquivA_symm_apply_inr (γ : Type*)
    (p : {p : (G.F.A → γ) × (G'.F.A → γ) // ∀ i, p.1 (G.a i) = p.2 (G'.a i)}) (x' : G'.F.A) :
    (glueLabelEquivA G G' γ).symm p (glueπA G G' (Sum.inr x')) = p.1.2 x' := rfl

@[simp] theorem glueLabelEquivB_symm_apply_inl (γ : Type*)
    (p : {p : (G.F.B → γ) × (G'.F.B → γ) // ∀ j, p.1 (G.b j) = p.2 (G'.b j)}) (y : G.F.B) :
    (glueLabelEquivB G G' γ).symm p (glueπB G G' (Sum.inl y)) = p.1.1 y := rfl

@[simp] theorem glueLabelEquivB_symm_apply_inr (γ : Type*)
    (p : {p : (G.F.B → γ) × (G'.F.B → γ) // ∀ j, p.1 (G.b j) = p.2 (G'.b j)}) (y' : G'.F.B) :
    (glueLabelEquivB G G' γ).symm p (glueπB G G' (Sum.inr y')) = p.1.2 y' := rfl

/-! ### Dropping the compatibility constraint under a matching label condition -/

/-- If `hα` and `hα'` are *each independently* required to match a prescribed labelling `v` at
positions `p`, `p'` respectively, then they are automatically compatible (agree wherever `p i`
and `p' i` are identified); so an "outer" compatibility check, guarding an "inner" check of only
one side's condition, can be replaced by the conjunction of both sides' conditions (dropping
compatibility, since it becomes redundant). This is the fact that lets the sum defining
`labelledHom` of a glued graph split into independent choices on each side. -/
theorem ite_compat_eq {ι α α' γ M : Type*} [Fintype ι] [DecidableEq γ] [Zero M]
    (p : ι → α) (p' : ι → α') (v : ι → γ) (hα : α → γ) (hα' : α' → γ) (c : M) :
    (if (∀ i, hα (p i) = hα' (p' i)) then (if (∀ i, hα (p i) = v i) then c else 0) else 0)
      = if ((∀ i, hα (p i) = v i) ∧ ∀ i, hα' (p' i) = v i) then c else 0 := by
  by_cases hcompat : ∀ i, hα (p i) = hα' (p' i)
  · by_cases hcondA : ∀ i, hα (p i) = v i
    · have hcondA' : ∀ i, hα' (p' i) = v i := fun i => (hcompat i).symm.trans (hcondA i)
      simp [hcompat, hcondA']
    · simp [hcompat]
  · have hnand : ¬ ((∀ i, hα (p i) = v i) ∧ ∀ i, hα' (p' i) = v i) :=
      fun ⟨hA, hA'⟩ => hcompat fun i => (hA i).trans (hA' i).symm
    simp [hcompat, hnand]

end Lax461425Proofs.PatternsLabelledGlue
