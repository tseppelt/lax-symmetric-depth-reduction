import Lax461425.SymmetricClasses
import Lax461425.SymmetricVNP
import Lax461425Proofs.TreeFormulaOperations
import Lax461425Proofs.TaggedFormulaOrbit
import Lax461425Proofs.CircuitFacts

/-!
All-automorphism orbit bounds for private-leaf formula operations. Fixed child roots pin
the entire child occurrence, including its private input leaves. Restrictions are genuine
automorphisms of the child circuit, so its previously proved orbit bound can be reused.
-/

namespace Lax461425Proofs.TreeFormulaOrbit

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies Lax461425.SymmetricVNP
open Lax461425.SymmetricClasses
open TreeFormulaCircuit TreeFormulaOperations
open scoped Classical

noncomputable section

variable {V K : Type*}

/-- Variable, constant, addition, multiplication: variable renaming preserves these kinds. -/
def labelKind : GateLabel V K → Fin 4
  | .var _ => 0
  | .const _ => 1
  | .add => 2
  | .mul => 3

theorem labelKind_map (π : V → V) (l : GateLabel V K) : labelKind (l.map π) = labelKind l := by
  cases l <;> rfl

/-- A single kind-count bound controls all gate orbits, including private input occurrences. -/
theorem orbitSize_le_of_kind_bound {A : Type*} [Group A] (ρ : A →* Equiv.Perm V)
    (C : Circuit V K) (B : ℕ)
    (hB : ∀ k, ({g | labelKind (C.label g) = k} : Set C.Gate).ncard ≤ B) :
    orbitSize ρ C ≤ B := by
  apply Finset.sup_le
  intro g _
  have hs : orbit ρ C g ⊆ {h | labelKind (C.label h) = labelKind (C.label g)} := by
    rintro h ⟨γ, σ, hσ, rfl⟩
    change labelKind (C.label (σ g)) = labelKind (C.label g)
    rw [hσ.1, labelKind_map]
  exact (Set.ncard_le_ncard hs).trans (hB _)

variable {I : Type} [Fintype I] (T : I → Tree V K) (mul : Bool)

def embed (i : I) (g : (T i).Gate) : (join T mul).Gate := .inr ⟨i, g⟩

theorem embed_injective (i : I) : Function.Injective (embed T mul i) := by
  intro g h he
  cases he
  rfl

theorem embed_wire (i : I) (g h : (T i).Gate) :
    (circuit (join T mul)).wire (embed T mul i g) (embed T mul i h) =
      (circuit (T i)).wire g h := by
  simp only [circuit, embed, join]
  cases hp : (T i).parent h <;> simp [joinParent, hp]

theorem edge_to_child {q : (join T mul).Gate} {i : I} {r : (T i).Gate}
    (hq : 0 < (circuit (join T mul)).wire (embed T mul i r) q) :
    ∃ g : (T i).Gate, q = embed T mul i g := by
  cases q with
  | inl u => simp [circuit, joinParent] at hq
  | inr q =>
    rcases q with ⟨j, g⟩
    cases hp : (T j).parent g with
    | none => simp [circuit, embed, joinParent, hp] at hq
    | some p =>
      have he : (Sigma.mk j p : Σ j, (T j).Gate) = ⟨i, r⟩ := by
        by_contra hn
        simp [circuit, embed, joinParent, hp, hn] at hq
      cases he
      exact ⟨g, rfl⟩

theorem path_to_child {q : (join T mul).Gate} {i : I} {r : (T i).Gate}
    (hq : Relation.ReflTransGen
      (fun a b => 0 < (circuit (join T mul)).wire b a) q (embed T mul i r)) :
    ∃ g : (T i).Gate, q = embed T mul i g := by
  suffices hh : ∀ {a b : (join T mul).Gate},
      Relation.ReflTransGen (fun a b => 0 < (circuit (join T mul)).wire b a) a b →
      ∀ (i : I) (r : (T i).Gate), b = embed T mul i r → ∃ g, a = embed T mul i g from
    hh hq i r rfl
  intro a b hab
  induction hab with
  | refl => intro i r he; exact ⟨r, he⟩
  | tail hab hstep ih =>
    intro i r he
    subst he
    obtain ⟨g, hg⟩ := edge_to_child T mul hstep
    exact ih i g hg

theorem embed_reaches_child_root (i : I) (g : (T i).Gate) :
    Relation.ReflTransGen (fun a b => 0 < (circuit (join T mul)).wire b a)
      (embed T mul i g) (embed T mul i (T i).out) := by
  have hm : ∀ {g h : (T i).Gate},
      Relation.ReflTransGen (fun a b => 0 < (circuit (T i)).wire b a) g h →
      Relation.ReflTransGen (fun a b => 0 < (circuit (join T mul)).wire b a)
        (embed T mul i g) (embed T mul i h) := by
    intro g h hp
    induction hp with
    | refl => exact .refl
    | tail hp hstep ih =>
      apply ih.tail
      rwa [embed_wire]
  exact hm ((circuit (T i)).reaches_out g)

theorem auto_preserves_child {σ : (join T mul).Gate ≃ (join T mul).Gate} {π : V → V}
    (hσ : Extends (circuit (join T mul)) σ π) (i : I)
    (hi : σ (embed T mul i (T i).out) = embed T mul i (T i).out) (g : (T i).Gate) :
    ∃ h : (T i).Gate, σ (embed T mul i g) = embed T mul i h := by
  have hp := TaggedFormulaOrbit.maps_path hσ (embed_reaches_child_root T mul i g)
  rw [hi] at hp
  exact path_to_child T mul hp

variable (σ : (join T mul).Gate ≃ (join T mul).Gate) (π : V → V)
variable (hσ : Extends (circuit (join T mul)) σ π) (i : I)
variable (hi : σ (embed T mul i (T i).out) = embed T mul i (T i).out)

def restrictMap (g : (T i).Gate) : (T i).Gate :=
  Classical.choose (auto_preserves_child T mul hσ i hi g)

theorem restrictMap_spec (g : (T i).Gate) :
    σ (embed T mul i g) = embed T mul i (restrictMap T mul σ π hσ i hi g) :=
  Classical.choose_spec (auto_preserves_child T mul hσ i hi g)

theorem restrictMap_injective : Function.Injective (restrictMap T mul σ π hσ i hi) := by
  intro g h hgh
  apply embed_injective T mul i
  apply σ.injective
  rw [restrictMap_spec T mul σ π hσ i hi, restrictMap_spec T mul σ π hσ i hi, hgh]

def restrict : (T i).Gate ≃ (T i).Gate :=
  Equiv.ofBijective (restrictMap T mul σ π hσ i hi)
    ⟨restrictMap_injective T mul σ π hσ i hi,
      Finite.surjective_of_injective (restrictMap_injective T mul σ π hσ i hi)⟩

theorem restrict_extends : Extends (circuit (T i)) (restrict T mul σ π hσ i hi) π := by
  constructor
  · intro g
    have hl := hσ.1 (embed T mul i g)
    rw [restrictMap_spec T mul σ π hσ i hi] at hl
    exact hl
  · intro g h
    have hw : (circuit (join T mul)).wire (σ (embed T mul i g)) (σ (embed T mul i h)) =
        (circuit (join T mul)).wire (embed T mul i g) (embed T mul i h) :=
      hσ.2 (embed T mul i g) (embed T mul i h)
    rw [restrictMap_spec T mul σ π hσ i hi, restrictMap_spec T mul σ π hσ i hi,
      embed_wire, embed_wire] at hw
    exact hw

section OrbitBounds

variable {A : Type*} [Group A] (ρ : A →* Equiv.Perm V)

/-- Restricting all extensions to a fixed child occurrence bounds its orbits by the
child circuit's own all-automorphism orbits. -/
theorem orbit_child_le (j : I) (g : (T j).Gate)
    (hfixed : ∀ (γ : A) (τ : (join T mul).Gate ≃ (join T mul).Gate),
      Extends (circuit (join T mul)) τ (ρ γ) →
        τ (embed T mul j (T j).out) = embed T mul j (T j).out) :
    (orbit ρ (circuit (join T mul)) (embed T mul j g)).ncard ≤
      orbitSize ρ (circuit (T j)) := by
  have hs : orbit ρ (circuit (join T mul)) (embed T mul j g) ⊆
      (embed T mul j) '' orbit ρ (circuit (T j)) g := by
    rintro w ⟨γ, τ, hτ, rfl⟩
    let fixed := hfixed γ τ hτ
    let e := restrict T mul τ (ρ γ) hτ j fixed
    refine ⟨e g, ⟨γ, e, restrict_extends T mul τ (ρ γ) hτ j fixed, rfl⟩, ?_⟩
    exact (restrictMap_spec T mul τ (ρ γ) hτ j fixed g).symm
  have hc : ((embed T mul j) '' orbit ρ (circuit (T j)) g).ncard ≤
      (orbit ρ (circuit (T j)) g).ncard := Set.ncard_image_le
  exact (Set.ncard_le_ncard hs).trans (hc.trans
    (Finset.le_sup (f := fun h => (orbit ρ (circuit (T j)) h).ncard) (Finset.mem_univ g)))

/-- The operation root is fixed under every extending automorphism. -/
theorem orbit_root_le_one :
    (orbit ρ (circuit (join T mul)) (.inl ())).ncard ≤ 1 := by
  have hs : orbit ρ (circuit (join T mul)) (.inl ()) ⊆ {Sum.inl ()} := by
    rintro w ⟨γ, τ, hτ, rfl⟩
    exact PatternsSupportBasic.extends_fixes_out hτ
  calc
    _ ≤ ({Sum.inl ()} : Set (join T mul).Gate).ncard := Set.ncard_le_ncard hs
    _ = 1 := Set.ncard_singleton _

/-- Any number of pinned children may be summed or multiplied without increasing their
common orbit bound (apart from the fixed operation root). -/
theorem join_orbitSize_le (B : ℕ) (hB : 1 ≤ B)
    (hchild : ∀ j, orbitSize ρ (circuit (T j)) ≤ B)
    (hfixed : ∀ (γ : A) (τ : (join T mul).Gate ≃ (join T mul).Gate),
      Extends (circuit (join T mul)) τ (ρ γ) →
        ∀ j, τ (embed T mul j (T j).out) = embed T mul j (T j).out) :
    orbitSize ρ (circuit (join T mul)) ≤ B := by
  apply Finset.sup_le
  intro g _
  cases g with
  | inl u =>
    cases u
    exact (orbit_root_le_one T mul ρ).trans hB
  | inr p =>
    rcases p with ⟨j, g⟩
    exact (orbit_child_le T mul ρ j g (fun γ τ hτ => hfixed γ τ hτ j)).trans (hchild j)

end OrbitBounds

end
end Lax461425Proofs.TreeFormulaOrbit
