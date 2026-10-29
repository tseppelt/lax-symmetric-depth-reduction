import Lax461425Proofs.RigidEquiv

/-!
Helper material for the rigidification proof: the aggregated wire weight `W C a b` that a gate
`a` sends into the equivalence class of `b`, and the fact that it only depends on the
equivalence class of `a`.
-/

namespace Lax461425Proofs.RigidWeight

open Lax461425.Circuits RigidHeight RigidEquiv

open scoped Classical

variable {V K : Type*} (C : Circuit V K)

/-- The total multiplicity of wires from `a` into gates equivalent to `b`. -/
noncomputable def W (a b : C.Gate) : ℕ := ∑ h, if Equiv C h b then C.wire a h else 0

/-- If `a` has height `≤` the height of `b`, `a` sends no wires into the class of `b`: any
child of `a` has height strictly less than that of `a`, hence strictly less than that of `b`,
so it cannot be equivalent to `b`. -/
theorem W_eq_zero_of_height_le {a b : C.Gate} (hab : height C a ≤ height C b) :
    W C a b = 0 := by
  apply Finset.sum_eq_zero
  intro h _
  rcases Nat.eq_zero_or_pos (C.wire a h) with hw0 | hwpos
  · simp [hw0]
  · have hh : height C h < height C a := height_lt_of_wire_pos C hwpos
    have : ¬ Equiv C h b := by
      intro heq
      have := equiv_height_eq C heq
      omega
    simp [this]

/-- For a gate `g` of height `≤ k + 1`, the sum over the level-`k` equivalence class of `b`
agrees with the sum over the full equivalence class of `b`: any child contributing to the sum
has height `≤ k`, where the two notions of class membership coincide. -/
theorem sum_equivRel_eq_W {g b : C.Gate} {k : ℕ} (hg : height C g ≤ k + 1) :
    (∑ h, if EquivRel C k h b then C.wire g h else 0) = W C g b := by
  apply Finset.sum_congr rfl
  intro h _
  rcases Nat.eq_zero_or_pos (C.wire g h) with hw0 | hwpos
  · simp [hw0]
  · have hh : height C h < height C g := height_lt_of_wire_pos C hwpos
    have hhk : height C h ≤ k := by omega
    have heq : EquivRel C k h b = Equiv C h b := propext (equivRel_stable C hhk)
    simp only [heq]

/-- Extracting the defining condition of `EquivRel C (k + 1) g g'` when `g` has height
`k + 1`: the carried-forward disjunct is impossible since it would force `height g ≤ k`. -/
theorem equivRel_succ_elim {k : ℕ} {g g' : C.Gate} (h : EquivRel C (k + 1) g g')
    (hgk : height C g = k + 1) :
    ∀ b : C.Gate, height C b ≤ k →
      (∑ h, if EquivRel C k h b then C.wire g h else 0) =
        (∑ h, if EquivRel C k h b then C.wire g' h else 0) := by
  rcases h with h | h
  · exfalso
    have := (equivRel_height_le C h).1
    omega
  · exact h.2.2.2

/-- The aggregated weight `W C a b` depends only on the equivalence class of `a`. -/
theorem W_eq_of_equiv {a a' b : C.Gate} (h : Equiv C a a') : W C a b = W C a' b := by
  have hheq : height C a = height C a' := equiv_height_eq C h
  rcases Nat.lt_or_ge (height C b) (height C a) with hlt | hge
  · set k := height C a - 1 with hkdef
    have hgk : height C a = k + 1 := by omega
    have h' : EquivRel C (k + 1) a a' := by
      have : EquivRel C (height C a) a a' := h
      rwa [hgk] at this
    have hb : height C b ≤ k := by omega
    have hwires := equivRel_succ_elim C h' hgk b hb
    have h1 := sum_equivRel_eq_W C (g := a) (b := b) (k := k) (by omega)
    have h2 := sum_equivRel_eq_W C (g := a') (b := b) (k := k) (by omega)
    rw [← h1, ← h2, hwires]
  · have hb' : height C a' ≤ height C b := by omega
    rw [W_eq_zero_of_height_le C hge, W_eq_zero_of_height_le C hb']

/-- If `a` sends positive total weight into the class of `b`, some actual gate of that class is
a child of `a`. -/
theorem exists_of_W_pos {a b : C.Gate} (hpos : 0 < W C a b) :
    ∃ h, Equiv C h b ∧ 0 < C.wire a h := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt, Nat.le_zero] at hcon
  have hz : W C a b = 0 := by
    apply Finset.sum_eq_zero
    intro h _
    by_cases he : Equiv C h b
    · simp [he, hcon h he]
    · simp [he]
  omega

/-- Positive weight into a class forces the class to have strictly smaller height. -/
theorem W_pos_height_lt {a b : C.Gate} (h : 0 < W C a b) : height C b < height C a := by
  by_contra hcon
  have := W_eq_zero_of_height_le C (not_lt.mp hcon)
  omega

/-- A relation whose steps strictly decrease a natural-number measure cannot contain a
nontrivial cycle. -/
theorem transGen_strict {α : Type*} {r : α → α → Prop} {f : α → ℕ}
    (hr : ∀ x y, r x y → f x < f y) {x y : α} (h : Relation.TransGen r x y) : f x < f y := by
  induction h with
  | single hxy => exact hr _ _ hxy
  | tail _ hyz ih => exact lt_trans ih (hr _ _ hyz)

end Lax461425Proofs.RigidWeight
