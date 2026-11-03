import Lax461425.CircuitProperties
import Lax461425Proofs.InputSharingConstruction
import Lax461425Proofs.CircuitFamilyFacts

open Lax461425.CircuitProperties

/-!
Every automorphism of the input quotient lifts to the original private-input circuit.
Internal gate occurrences are retained, and an input occurrence is recovered uniquely
from its parent and label. Thus identifying inputs does not enlarge internal gate orbits.
-/

namespace Lax461425Proofs.InputSharingOrbits

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies
open InputSharingConstruction
open scoped Classical

noncomputable section

variable {V K : Type*} (C : Circuit V K)
variable (hp : (PrivateInputs C)) (hd : (InputSiblingsDistinct C))

def parent (g : Input C) : C.Gate := Classical.choose (hp.2 g.val g.property)

theorem parent_wire (g : Input C) : C.wire (parent C hp g) g.val = 1 :=
  (Classical.choose_spec (hp.2 g.val g.property)).1

theorem parent_unique (g : Input C) {p : C.Gate} (h : 0 < C.wire p g.val) :
    p = parent C hp g := (Classical.choose_spec (hp.2 g.val g.property)).2 p h

theorem parent_internal (g : Input C) : ¬ (C.label (parent C hp g)).IsInput := by
  intro h
  have hz := C.wire_eq_zero_of_isInput (parent C hp g) g.val h
  rw [parent_wire] at hz
  contradiction

def internalParent (g : Input C) : Internal C := ⟨parent C hp g, parent_internal C hp g⟩

theorem input_wire (p : C.Gate) (g : Input C) :
    C.wire p g.val = if p = parent C hp g then 1 else 0 := by
  split_ifs with he
  · subst p; exact parent_wire C hp g
  · exact Nat.eq_zero_of_not_pos (fun h => he (parent_unique C hp g h))

include hd in
theorem input_unique (g h : Input C)
    (he : parent C hp g = parent C hp h) (hl : inputClass C g = inputClass C h) : g = h := by
  apply Subtype.ext
  apply hd (parent C hp g) g.val h.val g.property h.property
  · rw [parent_wire]; decide
  · rw [he, parent_wire]; decide
  · exact (inputClass_eq_iff C g h).mp hl

theorem exists_input (p : Internal C) (q : InputClass C)
    (h : 0 < wire C (.inl p) (.inr q)) :
    ∃ g : Input C, internalParent C hp g = p ∧ inputClass C g = q := by
  change 0 < ∑ g : Input C, if inputClass C g = q then C.wire p.val g.val else 0 at h
  obtain ⟨g, _, hg⟩ := (Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp h
  split_ifs at hg with he
  · refine ⟨g, ?_, he⟩
    apply Subtype.ext
    exact (parent_unique C hp g hg).symm
  · omega

variable {C}

theorem label_isInput_map (π : V → V) (l : GateLabel V K) :
    (l.map π).IsInput ↔ l.IsInput := by cases l <;> rfl

variable (C) (σ : (circuit C hp.1).Gate ≃ (circuit C hp.1).Gate)
variable (π : V → V) (hσ : Extends (circuit C hp.1) σ π)

include hσ

theorem exists_internal_image (p : Internal C) :
    ∃ q : Internal C, σ (.inl p) = .inl q := by
  cases he : σ (.inl p) with
  | inl q => exact ⟨q, rfl⟩
  | inr q =>
    have hl := hσ.1 (.inl p)
    rw [he] at hl
    change classLabel C q = (C.label p.val).map π at hl
    have hi : ((C.label p.val).map π).IsInput := by
      rw [← hl]
      exact classLabel_isInput C q
    exact (p.property ((label_isInput_map π _).mp hi)).elim

def internalMap (p : Internal C) : Internal C :=
  Classical.choose (exists_internal_image C hp σ π hσ p)

theorem internalMap_spec (p : Internal C) :
    σ (.inl p) = .inl (internalMap C hp σ π hσ p) :=
  Classical.choose_spec (exists_internal_image C hp σ π hσ p)

theorem exists_class_image (q : InputClass C) :
    ∃ r : InputClass C, σ (.inr q) = .inr r := by
  cases he : σ (.inr q) with
  | inr r => exact ⟨r, rfl⟩
  | inl r =>
    have hl := hσ.1 (.inr q)
    rw [he] at hl
    change C.label r.val = (classLabel C q).map π at hl
    have hi : (C.label r.val).IsInput := by
      rw [hl]
      exact (label_isInput_map π _).mpr (classLabel_isInput C q)
    exact (r.property hi).elim

def classMap (q : InputClass C) : InputClass C :=
  Classical.choose (exists_class_image C hp σ π hσ q)

theorem classMap_spec (q : InputClass C) :
    σ (.inr q) = .inr (classMap C hp σ π hσ q) :=
  Classical.choose_spec (exists_class_image C hp σ π hσ q)

theorem exists_input_image (g : Input C) :
    ∃ h : Input C,
      internalParent C hp h = internalMap C hp σ π hσ (internalParent C hp g) ∧
      inputClass C h = classMap C hp σ π hσ (inputClass C g) := by
  apply exists_input C hp
  have hw := hσ.2 (.inl (internalParent C hp g)) (.inr (inputClass C g))
  rw [internalMap_spec C hp σ π hσ, classMap_spec C hp σ π hσ] at hw
  simp only [circuit] at hw
  rw [hw]
  exact (by rw [parent_wire C hp g]; decide : 0 < C.wire (parent C hp g) g.val).trans_le
    (wire_input_le C (internalParent C hp g) g)

def inputMap (g : Input C) : Input C := Classical.choose (exists_input_image C hp σ π hσ g)

theorem inputMap_parent (g : Input C) :
    internalParent C hp (inputMap C hp σ π hσ g) =
      internalMap C hp σ π hσ (internalParent C hp g) :=
  (Classical.choose_spec (exists_input_image C hp σ π hσ g)).1

theorem inputMap_class (g : Input C) :
    inputClass C (inputMap C hp σ π hσ g) = classMap C hp σ π hσ (inputClass C g) :=
  (Classical.choose_spec (exists_input_image C hp σ π hσ g)).2

def liftMap (g : C.Gate) : C.Gate :=
  if hi : (C.label g).IsInput then (inputMap C hp σ π hσ ⟨g, hi⟩).val
  else (internalMap C hp σ π hσ ⟨g, hi⟩).val

@[simp] theorem liftMap_input (g : Input C) :
    liftMap C hp σ π hσ g.val = (inputMap C hp σ π hσ g).val := by
  simp [liftMap, g.property]

@[simp] theorem liftMap_internal (g : Internal C) :
    liftMap C hp σ π hσ g.val = (internalMap C hp σ π hσ g).val := by
  simp [liftMap, g.property]

theorem project_liftMap (g : C.Gate) :
    project C (liftMap C hp σ π hσ g) = σ (project C g) := by
  by_cases hi : (C.label g).IsInput
  · rw [liftMap_input C hp σ π hσ ⟨g, hi⟩, project_input, project_input C ⟨g, hi⟩,
      classMap_spec, inputMap_class]
  · rw [liftMap_internal C hp σ π hσ ⟨g, hi⟩, project_internal,
      project_internal C ⟨g, hi⟩, internalMap_spec]

theorem internalMap_injective : Function.Injective (internalMap C hp σ π hσ) := by
  intro p q he
  apply Sum.inl_injective
  apply σ.injective
  rw [internalMap_spec C hp σ π hσ, internalMap_spec C hp σ π hσ, he]

include hd in
theorem inputMap_injective : Function.Injective (inputMap C hp σ π hσ) := by
  intro g h he
  apply input_unique C hp hd g h
  · have hh : internalParent C hp g = internalParent C hp h :=
      internalMap_injective C hp σ π hσ (by
        rw [← inputMap_parent C hp σ π hσ, ← inputMap_parent C hp σ π hσ, he])
    exact congrArg (fun p : Internal C => p.val) hh
  · apply Sum.inr_injective
    apply σ.injective
    rw [classMap_spec C hp σ π hσ, classMap_spec C hp σ π hσ,
      ← inputMap_class C hp σ π hσ, ← inputMap_class C hp σ π hσ, he]

/-- The lifted gate permutation recovers input occurrences using their parent and label. -/
def lift : C.Gate ≃ C.Gate :=
  (oldGateEquiv C).trans ((Equiv.sumCongr
    (Equiv.ofBijective (internalMap C hp σ π hσ)
      (internalMap_injective C hp σ π hσ).bijective_of_finite)
    (Equiv.ofBijective (inputMap C hp σ π hσ)
      (inputMap_injective C hp hd σ π hσ).bijective_of_finite)).trans (oldGateEquiv C).symm)

@[simp] theorem lift_internal (g : Internal C) :
    lift C hp hd σ π hσ g.val = (internalMap C hp σ π hσ g).val := by
  simp [lift, oldGateEquiv, g.property]

@[simp] theorem lift_input (g : Input C) :
    lift C hp hd σ π hσ g.val = (inputMap C hp σ π hσ g).val := by
  simp [lift, oldGateEquiv, g.property]

theorem project_lift (g : C.Gate) :
    project C (lift C hp hd σ π hσ g) = σ (project C g) := by
  convert project_liftMap C hp σ π hσ g using 2
  by_cases hi : (C.label g).IsInput
  · rw [lift_input C hp hd σ π hσ ⟨g, hi⟩, liftMap_input C hp σ π hσ ⟨g, hi⟩]
  · rw [lift_internal C hp hd σ π hσ ⟨g, hi⟩, liftMap_internal C hp σ π hσ ⟨g, hi⟩]

theorem lift_extends : Extends C (lift C hp hd σ π hσ) π := by
  constructor
  · intro g
    rw [← label_project C, project_lift]
    exact hσ.1 (project C g) |>.trans (congrArg (fun l => l.map π) (label_project C g))
  · intro p g
    by_cases hpi : (C.label p).IsInput
    · rw [lift_input C hp hd σ π hσ ⟨p, hpi⟩]
      rw [C.wire_eq_zero_of_isInput _ _ (inputMap C hp σ π hσ ⟨p, hpi⟩).property,
        C.wire_eq_zero_of_isInput _ _ hpi]
    · rw [lift_internal C hp hd σ π hσ ⟨p, hpi⟩]
      by_cases hgi : (C.label g).IsInput
      · rw [lift_input C hp hd σ π hσ ⟨g, hgi⟩]
        rw [input_wire C hp _ (inputMap C hp σ π hσ ⟨g, hgi⟩),
          input_wire C hp _ ⟨g, hgi⟩]
        have he : (internalMap C hp σ π hσ ⟨p, hpi⟩).val =
            parent C hp (inputMap C hp σ π hσ ⟨g, hgi⟩) ↔ p = parent C hp ⟨g, hgi⟩ := by
          change (internalMap C hp σ π hσ ⟨p, hpi⟩).val =
            (internalParent C hp (inputMap C hp σ π hσ ⟨g, hgi⟩)).val ↔ _
          rw [inputMap_parent]
          exact (Subtype.ext_iff.symm.trans
            (internalMap_injective C hp σ π hσ).eq_iff).trans Subtype.ext_iff
        rw [he]
      · rw [lift_internal C hp hd σ π hσ ⟨g, hgi⟩]
        have hw := hσ.2 (.inl ⟨p, hpi⟩) (.inl ⟨g, hgi⟩)
        rw [internalMap_spec, internalMap_spec] at hw
        exact hw

variable {A : Type*} [Group A]

omit hσ

include hd in
/-- The quotient orbit is covered by the projection of the old orbit. This uses every
extending automorphism, rather than a chosen set of symmetry witnesses. -/
theorem orbit_project_subset (ρ : A →* Equiv.Perm V) (g : C.Gate) :
    orbit ρ (circuit C hp.1) (project C g) ⊆ project C '' orbit ρ C g := by
  rintro _ ⟨γ, τ, hτ, rfl⟩
  exact ⟨lift C hp hd τ (ρ γ) hτ g, ⟨γ, lift C hp hd τ (ρ γ) hτ,
    lift_extends C hp hd τ (ρ γ) hτ, rfl⟩, project_lift C hp hd τ (ρ γ) hτ g⟩

include hd in
/-- Identifying equal inputs of a private-input circuit cannot increase any gate orbit. -/
theorem orbitSize_le (ρ : A →* Equiv.Perm V) :
    orbitSize ρ (circuit C hp.1) ≤ orbitSize ρ C := by
  apply Finset.sup_le
  intro q _
  have hq : ∃ g : C.Gate, project C g = q := by
    cases q with
    | inl g => exact ⟨g.val, project_internal C g⟩
    | inr q =>
      obtain ⟨g, rfl⟩ := Quotient.exists_rep q
      exact ⟨g.val, project_input C g⟩
  obtain ⟨g, rfl⟩ := hq
  calc
    (orbit ρ (circuit C hp.1) (project C g)).ncard ≤ (project C '' orbit ρ C g).ncard :=
      Set.ncard_le_ncard (orbit_project_subset C hp hd ρ g)
    _ ≤ (orbit ρ C g).ncard := Set.ncard_image_le
    _ ≤ orbitSize ρ C := Finset.le_sup (f := fun g => (orbit ρ C g).ncard) (Finset.mem_univ g)

end

end Lax461425Proofs.InputSharingOrbits
