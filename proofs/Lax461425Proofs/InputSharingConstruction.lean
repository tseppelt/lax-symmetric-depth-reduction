import Lax461425.CircuitProperties
import Lax461425Proofs.RigidHeight
import Mathlib.Tactic

open Lax461425.CircuitProperties

/-!
Identify only input gates with equal labels. Internal gates retain their occurrences.
Wire multiplicities into a merged input are the sums of the old multiplicities, so the
construction is an actual finite circuit and retains the original algebraic semantics.
-/

namespace Lax461425Proofs.InputSharingConstruction

open Lax461425.Circuits
open scoped Classical

variable {V K : Type*} (C : Circuit V K)

abbrev Input := {g : C.Gate // (C.label g).IsInput}
abbrev Internal := {g : C.Gate // ¬ (C.label g).IsInput}

def inputSetoid : Setoid (Input C) where
  r g h := C.label g.val = C.label h.val
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

abbrev InputClass := Quotient (inputSetoid C)

noncomputable instance : Fintype (InputClass C) := Fintype.ofFinite _

abbrev Gate := Internal C ⊕ InputClass C

def inputClass (g : Input C) : InputClass C := Quotient.mk (inputSetoid C) g

theorem inputClass_eq_iff (g h : Input C) :
    inputClass C g = inputClass C h ↔ C.label g.val = C.label h.val := Quotient.eq

def classLabel : InputClass C → GateLabel V K :=
  Quotient.lift (fun g : Input C => C.label g.val) (fun _ _ h => h)

@[simp] theorem classLabel_inputClass (g : Input C) :
    classLabel C (inputClass C g) = C.label g.val := rfl

theorem classLabel_injective : Function.Injective (classLabel C) := by
  intro g h
  induction g using Quotient.inductionOn with
  | h g =>
    induction h using Quotient.inductionOn with
    | h h => exact fun he => Quotient.sound he

theorem classLabel_isInput (g : InputClass C) : (classLabel C g).IsInput := by
  induction g using Quotient.inductionOn with
  | h g => exact g.property

def label : Gate C → GateLabel V K
  | .inl g => C.label g.val
  | .inr g => classLabel C g

noncomputable def project (g : C.Gate) : Gate C :=
  if h : (C.label g).IsInput then .inr (inputClass C ⟨g, h⟩) else .inl ⟨g, h⟩

@[simp] theorem project_input (g : Input C) :
    project C g.val = .inr (inputClass C g) := by simp [project, g.property]

@[simp] theorem project_internal (g : Internal C) :
    project C g.val = .inl g := by simp [project, g.property]

@[simp] theorem label_project (g : C.Gate) : label C (project C g) = C.label g := by
  unfold project
  split <;> rfl

theorem project_surjective : Function.Surjective (project C) := by
  intro g
  cases g with
  | inl g => exact ⟨g.val, project_internal C g⟩
  | inr q =>
    induction q using Quotient.inductionOn with
    | h g => exact ⟨g.val, project_input C g⟩

theorem project_eq_internal_iff (g : C.Gate) (p : Internal C) :
    project C g = .inl p ↔ g = p.val := by
  constructor
  · intro h
    unfold project at h
    split at h
    · cases h
    · exact congrArg Subtype.val (Sum.inl.inj h)
  · rintro rfl
    exact project_internal C p

/-- Split the old gate type into the two genuine subtypes. -/
noncomputable def oldGateEquiv : C.Gate ≃ Internal C ⊕ Input C where
  toFun g := if h : (C.label g).IsInput then .inr ⟨g, h⟩ else .inl ⟨g, h⟩
  invFun := Sum.elim Subtype.val Subtype.val
  left_inv g := by
    by_cases h : (C.label g).IsInput <;> simp [h]
  right_inv g := by cases g with
    | inl g => simp [g.property]
    | inr g => simp [g.property]

noncomputable def wire : Gate C → Gate C → ℕ
  | .inl p, .inl g => C.wire p.val g.val
  | .inl p, .inr q => ∑ g : Input C, if inputClass C g = q then C.wire p.val g.val else 0
  | .inr _, _ => 0

/-- Internal wires retain their original multiplicities. -/
@[simp] theorem wire_internal_internal (p g : Internal C) :
    wire C (.inl p) (.inl g) = C.wire p.val g.val := rfl

/-- Each old input wire contributes to the wire into its merged input class. -/
theorem wire_input_le (p : Internal C) (g : Input C) :
    C.wire p.val g.val ≤ wire C (.inl p) (.inr (inputClass C g)) := by
  unfold wire
  have h := Finset.single_le_sum
    (f := fun h : Input C => if inputClass C h = inputClass C g then C.wire p.val h.val else 0)
    (fun h hh => Nat.zero_le _) (Finset.mem_univ g)
  simpa using h

theorem wire_project_pos {p g : C.Gate} (h : 0 < C.wire p g) :
    0 < wire C (project C p) (project C g) := by
  have hp : ¬ (C.label p).IsInput := by
    intro hp
    rw [C.wire_eq_zero_of_isInput p g hp] at h
    omega
  rw [project_internal C ⟨p, hp⟩]
  by_cases hg : (C.label g).IsInput
  · rw [project_input C ⟨g, hg⟩]
    exact h.trans_le (wire_input_le C ⟨p, hp⟩ ⟨g, hg⟩)
  · rw [project_internal C ⟨g, hg⟩]
    exact h

theorem project_path {a b : C.Gate}
    (h : Relation.ReflTransGen (fun g p => 0 < C.wire p g) a b) :
    Relation.ReflTransGen (fun g p => 0 < wire C p g) (project C a) (project C b) := by
  induction h with
  | refl => exact .refl
  | tail h hw ih => exact ih.tail (wire_project_pos C hw)

noncomputable def rank : Gate C → ℕ
  | .inl g => RigidHeight.height C g.val
  | .inr _ => 0

theorem wire_rank {p g : Gate C} (h : 0 < wire C p g) : rank C g < rank C p := by
  cases p with
  | inr p => simp [wire] at h
  | inl p =>
    cases g with
    | inl g => exact RigidHeight.height_lt_of_wire_pos C h
    | inr q =>
      change 0 < ∑ g : Input C, if inputClass C g = q then C.wire p.val g.val else 0 at h
      obtain ⟨g, hg, hpos⟩ := (Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp h
      split_ifs at hpos with he
      · have hh := RigidHeight.height_lt_of_wire_pos C hpos
        rw [RigidHeight.height_isInput C g.property] at hh
        exact hh
      · omega

variable (hout : ¬ (C.label C.out).IsInput)

/-- The quotient circuit keeps every internal occurrence and merges only equal inputs. -/
noncomputable def circuit : Circuit V K where
  Gate := Gate C
  label := label C
  wire := wire C
  out := .inl ⟨C.out, hout⟩
  wire_eq_zero_of_isInput p g hp := by
    cases p with
    | inl p => exact (p.property hp).elim
    | inr p => rfl
  acyclic g h := by
    have hh : ∀ {g p : Gate C}, Relation.TransGen (fun g p => 0 < wire C p g) g p →
        rank C g < rank C p := by
      intro g p h
      induction h with
      | single h => exact wire_rank C h
      | tail h h' ih => exact ih.trans (wire_rank C h')
    exact (Nat.lt_irrefl _) (hh h)
  reaches_out g := by
    have hp : ∀ v : C.Gate, Relation.ReflTransGen (fun g p => 0 < wire C p g)
        (project C v) (.inl ⟨C.out, hout⟩) := by
      intro v
      have h := C.reaches_out v
      have hm := project_path C h
      simpa only [project_internal C ⟨C.out, hout⟩] using hm
    cases g with
    | inl g => simpa only [project_internal] using hp g.val
    | inr g =>
      obtain ⟨g, rfl⟩ := Quotient.exists_rep g
      change Relation.ReflTransGen (fun g p => 0 < wire C p g)
        (.inr (inputClass C g)) (.inl ⟨C.out, hout⟩)
      simpa only [project_input] using hp g.val

@[simp] theorem circuit_label_project (g : C.Gate) :
    (circuit C hout).label (project C g) = C.label g := label_project C g

theorem inputsIdentified : (InputsIdentified (circuit C hout)) := by
  intro g h hg hgh
  cases g with
  | inl g => exact (g.property hg).elim
  | inr g =>
    cases h with
    | inl h =>
      have hh : (C.label h.val).IsInput := by
        change (classLabel C g).IsInput at hg
        change classLabel C g = C.label h.val at hgh
        rw [← hgh]
        exact hg
      exact (h.property hh).elim
    | inr h => exact congrArg Sum.inr (classLabel_injective C hgh)

end Lax461425Proofs.InputSharingConstruction
