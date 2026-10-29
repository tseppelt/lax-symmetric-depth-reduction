import Lax461425Proofs.RigidHeight

/-!
Helper material for the rigidification proof: the equivalence relation on gates obtained by
merging gates of the same height, label, and pattern of wires into lower classes, defined by
recursion on a natural number level that bounds the height of the gates being compared.
-/

namespace Lax461425Proofs.RigidEquiv

open Lax461425.Circuits RigidHeight

open scoped Classical

variable {V K : Type*}

/-- `EquivRel C k g g'` says that `g` and `g'` are identified by the equivalence relation,
witnessed at level `k`. The relation is cumulative in `k`: once two gates are identified at some
level, they stay identified at every higher level. A pair of gates of height `k + 1` is
newly identified at level `k + 1` when they have the same label and send the same total
multiplicity of wires into every class of gates of height `≤ k`, as witnessed by level `k`. -/
noncomputable def EquivRel (C : Circuit V K) : ℕ → C.Gate → C.Gate → Prop
  | 0, g, g' => C.label g = C.label g' ∧ height C g = 0 ∧ height C g' = 0
  | k + 1, g, g' => EquivRel C k g g' ∨
      (C.label g = C.label g' ∧ height C g = k + 1 ∧ height C g' = k + 1 ∧
        ∀ b : C.Gate, height C b ≤ k →
          (∑ h, if EquivRel C k h b then C.wire g h else 0) =
            (∑ h, if EquivRel C k h b then C.wire g' h else 0))

variable (C : Circuit V K)

/-- The final equivalence relation on gates: `g` and `g'` are equivalent if they are identified
at level `height C g`. -/
noncomputable def Equiv (g g' : C.Gate) : Prop := EquivRel C (height C g) g g'

/-- `EquivRel` is monotone in the level. -/
theorem equivRel_mono {k k' : ℕ} (hk : k ≤ k') {g g' : C.Gate} (h : EquivRel C k g g') :
    EquivRel C k' g g' := by
  induction hk with
  | refl => exact h
  | step _ ih => exact Or.inl ih

/-- Any witness of `EquivRel C k g g'` shows that `g` and `g'` have height `≤ k`. -/
theorem equivRel_height_le : ∀ {k : ℕ} {g g' : C.Gate}, EquivRel C k g g' →
    height C g ≤ k ∧ height C g' ≤ k := by
  intro k
  induction k with
  | zero => intro g g' h; simp [EquivRel] at h; omega
  | succ k ih =>
    intro g g' h
    rcases h with h | h
    · obtain ⟨h1, h2⟩ := ih h; omega
    · obtain ⟨_, h2, h3, _⟩ := h; omega

/-- `EquivRel` is stable: once a pair is already identified at some level `k` with
`height g ≤ k`, raising the level further does not change the verdict. -/
theorem equivRel_stable {g b : C.Gate} : ∀ {k : ℕ}, height C g ≤ k →
    (EquivRel C k g b ↔ EquivRel C (height C g) g b) := by
  intro k
  induction k with
  | zero =>
    intro hle
    have : height C g = 0 := Nat.le_zero.mp hle
    rw [this]
  | succ k ih =>
    intro hle
    rcases Nat.lt_or_ge (height C g) (k + 1) with hlt | hge
    · have hle' : height C g ≤ k := by omega
      rw [show EquivRel C (k+1) g b ↔ EquivRel C k g b from by
        constructor
        · intro h
          rcases h with h | h
          · exact h
          · obtain ⟨_, h2, _⟩ := h; omega
        · exact fun h => Or.inl h]
      exact ih hle'
    · have : height C g = k + 1 := by omega
      rw [this]

/-- `EquivRel` is reflexive at the level matching the gate's own height. -/
theorem equivRel_refl_of_height : ∀ (k : ℕ) (g : C.Gate), height C g = k → EquivRel C k g g := by
  intro k
  induction k with
  | zero => intro g hg; exact ⟨rfl, hg, hg⟩
  | succ k _ih => intro g hg; exact Or.inr ⟨rfl, hg, hg, fun _ _ => rfl⟩

/-- The equivalence relation `Equiv` is reflexive. -/
theorem equiv_refl (g : C.Gate) : Equiv C g g :=
  equivRel_refl_of_height C (height C g) g rfl

/-- `EquivRel` is symmetric at each fixed level. -/
theorem equivRel_symm : ∀ {k : ℕ} {g g' : C.Gate}, EquivRel C k g g' → EquivRel C k g' g := by
  intro k
  induction k with
  | zero => intro g g' h; obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1.symm, h3, h2⟩
  | succ k ih =>
    intro g g' h
    rcases h with h | h
    · exact Or.inl (ih h)
    · obtain ⟨h1, h2, h3, h4⟩ := h
      exact Or.inr ⟨h1.symm, h3, h2, fun b hb => (h4 b hb).symm⟩

/-- The equivalence relation `Equiv` is symmetric. -/
theorem equiv_symm {g g' : C.Gate} (h : Equiv C g g') : Equiv C g' g := by
  have hsymm : EquivRel C (height C g) g' g := equivRel_symm C h
  have hle : height C g' ≤ height C g := (equivRel_height_le C h).2
  exact (equivRel_stable C hle).mp hsymm

/-- Equivalent gates have equal height. -/
theorem equiv_height_eq {g g' : C.Gate} (h : Equiv C g g') : height C g = height C g' := by
  have h1 : height C g' ≤ height C g := (equivRel_height_le C h).2
  have h2 : height C g ≤ height C g' := (equivRel_height_le C (equiv_symm C h)).2
  omega

/-- `EquivRel` is transitive at each fixed level. -/
theorem equivRel_trans : ∀ {k : ℕ} {g g' g'' : C.Gate}, EquivRel C k g g' → EquivRel C k g' g'' →
    EquivRel C k g g'' := by
  intro k
  induction k with
  | zero =>
    intro g g' g'' h1 h2
    obtain ⟨l1, hg0, _hg'0⟩ := h1
    obtain ⟨l2, _, hg''0⟩ := h2
    exact ⟨l1.trans l2, hg0, hg''0⟩
  | succ k ih =>
    intro g g' g'' h1 h2
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact Or.inl (ih h1 h2)
      · obtain ⟨_, hg'le⟩ := equivRel_height_le C h1
        obtain ⟨_, hg'eq, _, _⟩ := h2
        omega
    · rcases h2 with h2 | h2
      · obtain ⟨hg'le, _⟩ := equivRel_height_le C h2
        obtain ⟨_, _, hg'eq, _⟩ := h1
        omega
      · obtain ⟨l1, hg1, _hg'1, w1⟩ := h1
        obtain ⟨l2, _hg'2, hg''2, w2⟩ := h2
        refine Or.inr ⟨l1.trans l2, hg1, hg''2, ?_⟩
        intro b hb
        rw [w1 b hb, w2 b hb]

/-- The equivalence relation `Equiv` is transitive. -/
theorem equiv_trans {g g' g'' : C.Gate} (h1 : Equiv C g g') (h2 : Equiv C g' g'') :
    Equiv C g g'' := by
  have hgg' : height C g = height C g' := equiv_height_eq C h1
  have h2' : EquivRel C (height C g) g' g'' := by rw [hgg']; exact h2
  exact equivRel_trans C h1 h2'

/-- Gates identified by `EquivRel` carry the same label. -/
theorem equivRel_label_eq : ∀ {k : ℕ} {g g' : C.Gate}, EquivRel C k g g' →
    C.label g = C.label g' := by
  intro k
  induction k with
  | zero => intro g g' h; exact h.1
  | succ k ih =>
    intro g g' h
    rcases h with h | h
    · exact ih h
    · exact h.1

/-- Equivalent gates carry the same label. -/
theorem equiv_label_eq {g g' : C.Gate} (h : Equiv C g g') : C.label g = C.label g' :=
  equivRel_label_eq C h
