import Lax461425Proofs.PathRefinementSchedule

/-! Adding a root preserves the linear schedule of the decomposition tree. -/

namespace Lax461425Proofs.PathRefinementSchedule

open scoped Classical

noncomputable section

variable {A : Type*} {parent : A → A} {root : A} (S : Schedule parent root)

def newParent : Unit ⊕ A → Unit ⊕ A :=
  Sum.elim (fun _ => .inl ()) (fun a => if a = root then .inl () else .inr (parent a))

def newBag (i : Fin (S.length + 3)) : Finset (Unit ⊕ A) :=
  if h : i.val ≤ S.length then (S.bag ⟨i.val, by omega⟩).image Sum.inr
  else if i.val = S.length + 1 then {Sum.inl (), Sum.inr root} else {Sum.inl ()}

theorem newBag_old (i : Fin (S.length + 1)) :
    newBag S ⟨i.val, by omega⟩ = (S.bag i).image Sum.inr := by
  simp [newBag, Nat.le_of_lt_succ i.isLt]

theorem newBag_inr {a : A} (i : Fin (S.length + 3)) :
    Sum.inr a ∈ newBag S i ↔
      if h : i.val ≤ S.length then a ∈ S.bag ⟨i.val, by omega⟩
      else i.val = S.length + 1 ∧ a = root := by
  unfold newBag
  split_ifs <;> simp_all

theorem newBag_inl (i : Fin (S.length + 3)) :
    Sum.inl () ∈ newBag S i ↔ S.length + 1 ≤ i.val := by
  unfold newBag
  split_ifs <;> simp_all <;> omega

/-- A new root extends the endpoint by a single edge, using only bags of size two. -/
def newRoot : Schedule (newParent (parent := parent) (root := root)) (Sum.inl ()) where
  length := S.length + 2
  bag := newBag S
  last := by simp [newBag]
  card i := by
    unfold newBag
    split_ifs
    · exact Finset.card_image_le.trans (S.card _)
    · exact (Finset.card_insert_le _ _).trans (by simp)
    · simp
  cover a := by
    cases a with
    | inl a =>
      cases a
      exact ⟨Fin.last (S.length + 2), (newBag_inl S _).mpr (by simp)⟩
    | inr a =>
      obtain ⟨i, hi⟩ := S.cover a
      refine ⟨⟨i.val, by omega⟩, ?_⟩
      rw [newBag_old]
      exact Finset.mem_image.mpr ⟨a, hi, rfl⟩
  edge a := by
    cases a with
    | inl a =>
      cases a
      exact ⟨Fin.last (S.length + 2), (newBag_inl S _).mpr (by simp),
        (newBag_inl S _).mpr (by simp)⟩
    | inr a =>
      by_cases ha : a = root
      · subst a
        let i : Fin (S.length + 3) := ⟨S.length + 1, by omega⟩
        refine ⟨i, ?_, ?_⟩
        · rw [newBag_inr, dif_neg (by dsimp [i]; omega)]
          exact ⟨rfl, rfl⟩
        · simpa [newParent] using (newBag_inl S i).mpr (by dsimp [i]; exact le_rfl)
      · obtain ⟨i, hi, hp⟩ := S.edge a
        refine ⟨⟨i.val, by omega⟩, ?_, ?_⟩
        · rw [newBag_old]; exact Finset.mem_image.mpr ⟨a, hi, rfl⟩
        · change (if a = root then Sum.inl () else Sum.inr (parent a)) ∈ _
          rw [if_neg ha, newBag_old]
          exact Finset.mem_image.mpr ⟨parent a, hp, rfl⟩
  interval a i j l hij hjl hi hl := by
    have h₁ := hij; have h₂ := hjl
    change i.val ≤ j.val at h₁
    change j.val ≤ l.val at h₂
    cases a with
    | inl a =>
      cases a
      rw [newBag_inl] at hi hl ⊢
      omega
    | inr a =>
      rw [newBag_inr] at hi hl ⊢
      by_cases hj : j.val ≤ S.length
      · rw [dif_pos hj]
        have hi' : i.val ≤ S.length := by omega
        rw [dif_pos hi'] at hi
        by_cases hl' : l.val ≤ S.length
        · rw [dif_pos hl'] at hl
          exact S.interval a _ _ _ (by exact hij) (by exact hjl) hi hl
        · rw [dif_neg hl'] at hl
          rcases hl with ⟨_, har⟩
          subst a
          apply S.interval root ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ (Fin.last S.length)
            (by exact hij) (by exact hj) hi
          rw [S.last]; simp
      · rw [dif_neg hj]
        have hl' : ¬ l.val ≤ S.length := by omega
        rw [dif_neg hl'] at hl
        refine ⟨?_, hl.2⟩
        omega

end

end Lax461425Proofs.PathRefinementSchedule
