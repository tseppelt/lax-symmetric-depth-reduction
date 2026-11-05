import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
Width-one path schedules for the rooted trees used by Tim's labelled-pattern machinery.
The last bag is the root singleton. A star has such a schedule, and attaching additional
leaves at the root preserves it. These certificates refine the existing decompositions;
they do not replace the existing notions of labelled pattern or homomorphism polynomial.
-/

namespace Lax461425Proofs.PathRefinementSchedule

open scoped Classical

/-- A path decomposition of a parent tree, with its root at the final endpoint. -/
structure Schedule {A : Type*} (parent : A → A) (root : A) where
  length : ℕ
  bag : Fin (length + 1) → Finset A
  last : bag (Fin.last length) = {root}
  card : ∀ i, (bag i).card ≤ 2
  cover : ∀ a, ∃ i, a ∈ bag i
  edge : ∀ a, ∃ i, a ∈ bag i ∧ parent a ∈ bag i
  interval : ∀ a i j l, i ≤ j → j ≤ l → a ∈ bag i → a ∈ bag l → a ∈ bag j

noncomputable section

variable {A : Type*} [Fintype A] (parent : A → A) (root : A)

def starBag (i : Fin (Fintype.card A + 1)) : Finset A :=
  if h : i.val < Fintype.card A then {root, (Fintype.equivFin A).symm ⟨i.val, h⟩}
  else {root}

theorem root_mem_starBag (i : Fin (Fintype.card A + 1)) : root ∈ starBag root i := by
  unfold starBag
  split <;> simp

theorem starBag_nonroot {a : A} (ha : a ≠ root) {i : Fin (Fintype.card A + 1)}
    (hi : a ∈ starBag root i) : i.val = (Fintype.equivFin A a).val := by
  unfold starBag at hi
  split_ifs at hi with h
  · have he : a = (Fintype.equivFin A).symm ⟨i.val, h⟩ := by simpa [ha] using hi
    simpa only [Equiv.apply_symm_apply] using
      (congrArg (fun a => (Fintype.equivFin A a).val) he).symm
  · simp [ha] at hi

/-- A decomposition tree of depth at most one is a star, regardless of its number of leaves. -/
def star (hparent : ∀ a, parent a = root) : Schedule parent root where
  length := Fintype.card A
  bag := starBag root
  last := by simp [starBag]
  card i := by
    unfold starBag
    split
    · exact (Finset.card_insert_le _ _).trans (by simp)
    · simp
  cover a := by
    refine ⟨⟨(Fintype.equivFin A a).val, by omega⟩, ?_⟩
    simp [starBag, (Fintype.equivFin A a).isLt]
  edge a := by
    refine ⟨⟨(Fintype.equivFin A a).val, by omega⟩, ?_, ?_⟩
    · simp [starBag, (Fintype.equivFin A a).isLt]
    · rw [hparent]
      exact root_mem_starBag root _
  interval a i j l hij hjl hi hl := by
    by_cases ha : a = root
    · subst a; exact root_mem_starBag root j
    · have hi' := starBag_nonroot root ha hi
      have hl' := starBag_nonroot root ha hl
      have he : j = i := Fin.ext (by have h₁ := hij; have h₂ := hjl; change i.val ≤ j.val at h₁; change j.val ≤ l.val at h₂; omega)
      simpa [he] using hi

variable {parent root}

/-- The parent map after attaching a finite set of new leaves to the old root. -/
def leafParent {B : Type*} : A ⊕ B → A ⊕ B :=
  Sum.elim (fun a => .inl (parent a)) (fun _ => .inl root)

variable {B : Type*} [Fintype B] (S : Schedule parent root)

def leafBag (i : Fin (S.length + Fintype.card B + 2)) : Finset (A ⊕ B) :=
  if h : i.val ≤ S.length then (S.bag ⟨i.val, by omega⟩).image Sum.inl
  else if h' : i.val ≤ S.length + Fintype.card B then
    {Sum.inl root, Sum.inr ((Fintype.equivFin B).symm ⟨i.val - (S.length + 1), by omega⟩)}
  else {Sum.inl root}

theorem leafBag_old (i : Fin (S.length + 1)) :
    leafBag (B := B) S ⟨i.val, by omega⟩ = (S.bag i).image Sum.inl := by
  simp [leafBag, Nat.le_of_lt_succ i.isLt]

theorem leafBag_inl {a : A} (i : Fin (S.length + Fintype.card B + 2)) :
    Sum.inl a ∈ leafBag (B := B) S i ↔
      if h : i.val ≤ S.length then a ∈ S.bag ⟨i.val, by omega⟩ else a = root := by
  unfold leafBag
  split_ifs <;> simp

theorem leafBag_inr {b : B} (i : Fin (S.length + Fintype.card B + 2)) :
    Sum.inr b ∈ leafBag (B := B) S i ↔
      i.val = S.length + 1 + (Fintype.equivFin B b).val := by
  unfold leafBag
  split_ifs with h h'
  · simp only [Finset.mem_image]
    constructor
    · rintro ⟨a, _, he⟩; cases he
    · intro he; have hb := (Fintype.equivFin B b).isLt; omega
  · simp only [Finset.mem_insert, Sum.inr.injEq, Sum.inr_ne_inl, Finset.mem_singleton,
      false_or]
    constructor
    · intro he
      have he' := congrArg (fun b => (Fintype.equivFin B b).val) he
      simpa using (show i.val = S.length + 1 + (Fintype.equivFin B b).val by
        simp only [Equiv.apply_symm_apply] at he'; omega)
    · intro he
      apply (Fintype.equivFin B).injective
      simp only [Equiv.apply_symm_apply]
      apply Fin.ext
      change (Fintype.equivFin B b).val = i.val - (S.length + 1)
      omega
  · simp only [Finset.mem_singleton, Sum.inr_ne_inl]
    constructor
    · exact False.elim
    · intro he; have hb := (Fintype.equivFin B b).isLt; omega

/-- Arbitrarily many root leaves do not increase the width-one node schedule. -/
def leaves : Schedule (leafParent (B := B) (parent := parent) (root := root)) (Sum.inl root) where
  length := S.length + Fintype.card B + 1
  bag := leafBag S
  last := by simp [leafBag]
  card i := by
    unfold leafBag
    split_ifs
    · exact Finset.card_image_le.trans (S.card _)
    · exact (Finset.card_insert_le _ _).trans (by simp)
    · simp
  cover a := by
    cases a with
    | inl a =>
      obtain ⟨i, hi⟩ := S.cover a
      refine ⟨⟨i.val, by omega⟩, ?_⟩
      rw [leafBag_old]
      exact Finset.mem_image.mpr ⟨a, hi, rfl⟩
    | inr b =>
      refine ⟨⟨S.length + 1 + (Fintype.equivFin B b).val, by have hb := (Fintype.equivFin B b).isLt; omega⟩, ?_⟩
      exact (leafBag_inr S _).mpr rfl
  edge a := by
    cases a with
    | inl a =>
      obtain ⟨i, hi, hp⟩ := S.edge a
      refine ⟨⟨i.val, by omega⟩, ?_, ?_⟩
      · rw [leafBag_old]; exact Finset.mem_image.mpr ⟨a, hi, rfl⟩
      · change Sum.inl (parent a) ∈ _
        rw [leafBag_old]; exact Finset.mem_image.mpr ⟨parent a, hp, rfl⟩
    | inr b =>
      let i : Fin (S.length + Fintype.card B + 2) :=
        ⟨S.length + 1 + (Fintype.equivFin B b).val, by have hb := (Fintype.equivFin B b).isLt; omega⟩
      refine ⟨i, (leafBag_inr S i).mpr rfl, ?_⟩
      change Sum.inl root ∈ _
      rw [leafBag_inl]
      rw [dif_neg (by dsimp [i]; omega)]
  interval a i j l hij hjl hi hl := by
    cases a with
    | inr b =>
      rw [leafBag_inr] at hi hl ⊢
      have h₁ := hij; have h₂ := hjl
      change i.val ≤ j.val at h₁
      change j.val ≤ l.val at h₂
      omega
    | inl a =>
      rw [leafBag_inl] at hi hl ⊢
      have h₁ := hij; have h₂ := hjl
      change i.val ≤ j.val at h₁
      change j.val ≤ l.val at h₂
      by_cases hj : j.val ≤ S.length
      · rw [dif_pos hj]
        have hi' : i.val ≤ S.length := by omega
        rw [dif_pos hi'] at hi
        by_cases hl' : l.val ≤ S.length
        · rw [dif_pos hl'] at hl
          exact S.interval a _ _ _ (by exact hij) (by exact hjl) hi hl
        · rw [dif_neg hl'] at hl
          subst a
          apply S.interval root ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ (Fin.last S.length)
            (by exact hij) (by exact hj) hi
          rw [S.last]; simp
      · rw [dif_neg hj]
        have hl' : ¬ l.val ≤ S.length := by omega
        rwa [dif_neg hl'] at hl

end

end Lax461425Proofs.PathRefinementSchedule
