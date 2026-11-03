import Lax461425.CircuitProperties
import Lax461425Proofs.PatternsInductionChild

/-!
The skew-specific support step. A product gate has at most one noninput child, with
multiplicity one. Every automorphism fixing the product gate fixes that child, so the
existing least-support machinery puts the child's support inside the parent's support.
-/

namespace Lax461425Proofs.PathRefinementSkew

open Lax461425.Circuits Lax461425.CircuitProperties Lax461425.MatrixSymmetry Lax461425.Supports
open PatternsInductionSetup PatternsSupportAction PatternsSupportBasic
open scoped Classical

variable {V K : Type*} {C : Circuit V K}

theorem internal_wire_le_one (hskew : IsSkew C) {g h : C.Gate}
    (hg : C.label g = .mul) (hi : ¬ (C.label h).IsInput) : C.wire g h ≤ 1 := by
  have hs := Finset.single_le_sum
    (f := fun h => if (C.label h).IsInput then 0 else C.wire g h)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ h)
  simp only [if_neg hi] at hs
  exact hs.trans (hskew g hg)

theorem internal_wire_eq_one (hskew : IsSkew C) {g h : C.Gate}
    (hg : C.label g = .mul) (hi : ¬ (C.label h).IsInput) (hw : 0 < C.wire g h) :
    C.wire g h = 1 := by
  have hh := internal_wire_le_one hskew hg hi
  omega

theorem internal_child_unique (hskew : IsSkew C) {g h h' : C.Gate}
    (hg : C.label g = .mul) (hi : ¬ (C.label h).IsInput) (hi' : ¬ (C.label h').IsInput)
    (hw : 0 < C.wire g h) (hw' : 0 < C.wire g h') : h = h' := by
  by_contra he
  let f : C.Gate → ℕ := fun h => if (C.label h).IsInput then 0 else C.wire g h
  have hs : ∑ h, f h ≤ 1 := hskew g hg
  have ht : f h' ≤ ∑ x ∈ Finset.univ.erase h, f x :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.mpr ⟨Ne.symm he, Finset.mem_univ _⟩)
  have hsum := Finset.sum_erase_add (s := Finset.univ) f (Finset.mem_univ h)
  have hh : f h = C.wire g h := if_neg hi
  have hh' : f h' = C.wire g h' := if_neg hi'
  rw [hh'] at ht
  rw [hh] at hsum
  omega

theorem isInput_map (π : V → V) (l : GateLabel V K) :
    (l.map π).IsInput ↔ l.IsInput := by cases l <;> rfl

theorem isInput_image {σ : C.Gate ≃ C.Gate} {π : V → V} (hσ : Extends C σ π) (h : C.Gate) :
    (C.label (σ h)).IsInput ↔ (C.label h).IsInput := by
  rw [hσ.1]
  exact isInput_map π _

variable {n : ℕ} {C : Circuit (Fin n × Fin n) K}

theorem internal_child_support (hskew : IsSkew C) {g h : C.Gate}
    (hg : C.label g = .mul) (hi : ¬ (C.label h).IsInput) (hw : 0 < C.wire g h)
    {S : Set (Fin n ⊕ Fin n)} (hS : IsSupport C g S) : IsSupport C h S := by
  intro γ σ hfix hσ
  have hgfix := hS γ σ hfix hσ
  have hw' : 0 < C.wire g (σ h) := by
    have hs : C.wire (σ g) (σ h) = C.wire g h := hσ.2 g h
    rw [hgfix] at hs
    rwa [hs]
  exact (internal_child_unique hskew hg hi
    (fun hh => hi ((isInput_image hσ h).mp hh)) hw hw').symm

theorem internal_sup_subset [Field K] (hrig : IsRigid C) (hn : 2 * supportSize C < n)
    (hskew : IsSkew C) {g h : C.Gate} (hg : C.label g = .mul)
    (hi : ¬ (C.label h).IsInput) (hw : 0 < C.wire g h) :
    supOf hrig hn h ⊆ supOf hrig hn g :=
  supOf_subset hrig hn h
    (internal_child_support hskew hg hi hw (isSupport_supOf hrig hn g))
    (ncard_supOf_le hrig hn g)

noncomputable section

def inputChildren (C : Circuit V K) (g : C.Gate) : Finset C.Gate :=
  Finset.univ.filter (fun h => 0 < C.wire g h ∧ (C.label h).IsInput)

variable {R : Type*} [CommMonoid R]

theorem product_all_inputs {C : Circuit V K} (g : C.Gate)
    (hinputs : ∀ h, 0 < C.wire g h → (C.label h).IsInput) (q : C.Gate → R) :
    (∏ h, q h ^ C.wire g h) = ∏ h ∈ inputChildren C g, q h ^ C.wire g h := by
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro h _ hn
  have hz : C.wire g h = 0 := by
    by_contra hh
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hh, hinputs h (Nat.pos_of_ne_zero hh)⟩)
  rw [hz, pow_zero]

theorem product_one_internal {C : Circuit V K} (hskew : IsSkew C) {g h : C.Gate}
    (hg : C.label g = .mul) (hi : ¬ (C.label h).IsInput) (hw : 0 < C.wire g h)
    (q : C.Gate → R) :
    (∏ h', q h' ^ C.wire g h') = q h * ∏ h' ∈ inputChildren C g, q h' ^ C.wire g h' := by
  have hhS : h ∉ inputChildren C g := by simp [inputChildren, hi]
  have hp : (∏ h' ∈ insert h (inputChildren C g), q h' ^ C.wire g h') =
      ∏ h', q h' ^ C.wire g h' := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro h' _ hh'
    have hz : C.wire g h' = 0 := by
      by_contra hn
      have hw' := Nat.pos_of_ne_zero hn
      by_cases hi' : (C.label h').IsInput
      · exact hh' (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw', hi'⟩))
      · have he := internal_child_unique hskew hg hi hi' hw hw'
        exact hh' (by simp [← he])
    rw [hz, pow_zero]
  rw [Finset.prod_insert hhS, internal_wire_eq_one hskew hg hi hw, pow_one] at hp
  exact hp.symm

end

end Lax461425Proofs.PathRefinementSkew
