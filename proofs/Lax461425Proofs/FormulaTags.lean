import Lax461425Proofs.ComputedFormula
import Lax461425Proofs.TreeFormulaOrbit
import Lax461425Proofs.FreshTags

/-!
Fresh inverse tags pin formula occurrences under every extending automorphism. Tags are
chosen independently at each operation level; their inverses avoid all child constants.
-/

namespace Lax461425Proofs.FormulaTags

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies
open ComputedFormula TreeFormulaCircuit TreeFormulaOperations TreeFormulaOrbit
open scoped Classical

noncomputable section

variable {V K : Type*} [Field K]

def labelConstants : GateLabel V K → Finset K
  | .const c => {c}
  | _ => ∅

/-- All constants actually used by the finite formula tree. -/
def constants (F : Formula V K) : Finset K :=
  Finset.univ.biUnion fun g => labelConstants (F.tree.label g)

theorem mem_constants_of_label (F : Formula V K) (g : F.tree.Gate) {c : K}
    (hg : F.tree.label g = .const c) : c ∈ constants F := by
  apply Finset.mem_biUnion.mpr
  exact ⟨g, Finset.mem_univ _, by simp [labelConstants, hg]⟩

variable {I : Type} [Fintype I]

/-- Syntactic freshness sufficient to identify every inverse marker globally. -/
structure GoodTags (F : I → Formula V K) (t : I → K) : Prop where
  nonzero : ∀ i, t i ≠ 0
  fresh : ∀ i j, t i ∉ constants (F j)
  inverse_fresh : ∀ i j, (t i)⁻¹ ∉ constants (F j)
  injective : Function.Injective t
  inverse_ne_tag : ∀ i j, (t i)⁻¹ ≠ t j

/-- Finitely many inverse-distinct tags exist over every infinite field. -/
theorem exists_goodTags [Infinite K] (F : I → Formula V K) : ∃ t, GoodTags F t := by
  let s : Finset K := Finset.univ.biUnion fun i => constants (F i)
  obtain ⟨tags, hcard, hgood, hdis⟩ := FreshTags.exists_fresh_tag_set s (Fintype.card I)
  let e : I ≃ ↥tags := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let t : I → K := fun i => (e i).val
  refine ⟨t, ?_⟩
  constructor
  · intro i; exact (hgood _ (e i).property).1
  · intro i j hij
    exact (hgood _ (e i).property).2.1
      (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hij⟩)
  · intro i j hij
    exact (hgood _ (e i).property).2.2
      (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hij⟩)
  · exact Subtype.val_injective.comp e.injective
  · intro i j hij
    apply Finset.disjoint_left.mp hdis (e j).property
    exact Finset.mem_image.mpr ⟨t i, (e i).property, hij⟩

/-- The private inverse-constant leaf is an immediate child of the tagging root. -/
def inverseMarker (t : K) (F : Formula V K) : (tag t F).tree.Gate :=
  .inr ⟨true, ()⟩

theorem inverseMarker_label (t : K) (F : Formula V K) :
    (tag t F).tree.label (inverseMarker t F) = .const t⁻¹ := rfl

theorem inverseMarker_parent (t : K) (F : Formula V K) :
    (tag t F).tree.parent (inverseMarker t F) = some (tag t F).tree.out := rfl

/-- A tagged formula introduces exactly the two displayed constants. -/
theorem tag_constant_cases (t : K) (F : Formula V K) (g : (tag t F).tree.Gate) {c : K}
    (hg : (tag t F).tree.label g = .const c) : c = t⁻¹ ∨ c = t ∨ c ∈ constants F := by
  cases g with
  | inl u => cases hg
  | inr q =>
    rcases q with ⟨b, g⟩
    cases b with
    | true => exact Or.inl (GateLabel.const.inj hg).symm
    | false =>
      cases g with
      | inl u => cases hg
      | inr q =>
        rcases q with ⟨b, g⟩
        cases b with
        | true => exact Or.inr (Or.inl (GateLabel.const.inj hg).symm)
        | false => exact Or.inr (Or.inr (mem_constants_of_label F g hg))

theorem inverseMarker_unique (t : K) (F : Formula V K) (hne : t⁻¹ ≠ t)
    (hfresh : t⁻¹ ∉ constants F) (g : (tag t F).tree.Gate)
    (hg : (tag t F).tree.label g = .const t⁻¹) : g = inverseMarker t F := by
  cases g with
  | inl u => cases hg
  | inr q =>
    rcases q with ⟨b, g⟩
    cases b with
    | true => cases g; rfl
    | false =>
      cases g with
      | inl u => cases hg
      | inr q =>
        rcases q with ⟨b, g⟩
        cases b with
        | true => exact (hne (GateLabel.const.inj hg).symm).elim
        | false => exact (hfresh (mem_constants_of_label F g hg)).elim

theorem marker_unique_in_op (F : I → Formula V K) (t : I → K) (ht : GoodTags F t)
    (mul : Bool) (i : I) (q : (op mul (fun j => tag (t j) (F j))).tree.Gate)
    (hq : (op mul (fun j => tag (t j) (F j))).tree.label q = .const (t i)⁻¹) :
    q = embed (fun j => (tag (t j) (F j)).tree) mul i (inverseMarker (t i) (F i)) := by
  cases q with
  | inl u => cases mul <;> cases hq
  | inr q =>
    rcases q with ⟨j, g⟩
    have hj : j = i := by
      rcases tag_constant_cases (t j) (F j) g hq with he | he | he
      · exact ht.injective (inv_injective he).symm
      · exact (ht.inverse_ne_tag i j he).elim
      · exact (ht.inverse_fresh i j he).elim
    subst j
    rw [inverseMarker_unique (t i) (F i) (ht.inverse_ne_tag i i) (ht.inverse_fresh i i) g hq]
    rfl

/-- Every extending automorphism fixes each child tagging root. -/
theorem roots_fixed (F : I → Formula V K) (t : I → K) (ht : GoodTags F t) (mul : Bool)
    {σ : (op mul (fun j => tag (t j) (F j))).tree.Gate ≃
      (op mul (fun j => tag (t j) (F j))).tree.Gate} {π : V → V}
    (hσ : Extends (circuit (op mul (fun j => tag (t j) (F j))).tree) σ π) (i : I) :
    σ (embed (fun j => (tag (t j) (F j)).tree) mul i (tag (t i) (F i)).tree.out) =
      embed (fun j => (tag (t j) (F j)).tree) mul i (tag (t i) (F i)).tree.out := by
  let T := fun j => (tag (t j) (F j)).tree
  let g := embed T mul i (inverseMarker (t i) (F i))
  let r := embed T mul i (T i).out
  have hσ' : Extends (circuit (join T mul)) σ π := hσ
  have hg : σ g = g := TaggedFormulaOrbit.fixes_unique_constant hσ' (t i)⁻¹ g
    (inverseMarker_label (t i) (F i)) (marker_unique_in_op F t ht mul i)
  have hp : (join T mul).parent g = some r := by
    change joinParent T (.inr ⟨i, inverseMarker (t i) (F i)⟩) = some (.inr ⟨i, (T i).out⟩)
    have hb : (T i).parent (inverseMarker (t i) (F i)) = some (T i).out :=
      inverseMarker_parent (t i) (F i)
    simp only [joinParent, hb]
  have hp' : joinParent T g = some r := hp
  change σ r = r
  apply TaggedFormulaOrbit.fixes_unique_parent hσ' hg
  · simp only [circuit, join]
    rw [if_pos hp']
    decide
  · intro p hpos
    have he : joinParent T g = some p := by
      by_contra hn
      simp only [circuit, join] at hpos
      simp [hn] at hpos
    exact Option.some.inj (he.symm.trans hp')

/-- Any number of freshly tagged blocks retain their common all-automorphism orbit bound. -/
theorem orbit_bound {A : Type*} [Group A] (ρ : A →* Equiv.Perm V)
    (F : I → Formula V K) (t : I → K) (ht : GoodTags F t) (mul : Bool)
    (B : ℕ) (hB : 1 ≤ B)
    (hchild : ∀ i, orbitSize ρ (circuit (tag (t i) (F i)).tree) ≤ B) :
    orbitSize ρ (circuit (op mul (fun j => tag (t j) (F j))).tree) ≤ B := by
  apply join_orbitSize_le (fun j => (tag (t j) (F j)).tree) mul ρ B hB hchild
  intro γ σ hσ i
  exact roots_fixed F t ht mul hσ i

end
end Lax461425Proofs.FormulaTags
