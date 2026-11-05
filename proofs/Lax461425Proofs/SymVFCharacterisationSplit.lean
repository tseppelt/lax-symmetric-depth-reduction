import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

/-!
Splitting coefficients: every coefficient `c i` is written as `a i + (c i - a i)` such that
all `2m` resulting numbers are pairwise distinct and avoid a prescribed finite set.
-/

namespace Lax461425Proofs.SymVFCharacterisationSplit

open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

/-- The pairwise freshness conditions on a split. -/
def Good (S : Finset K) {m : ℕ} (c a : Fin m → K) : Prop :=
  (∀ i, a i ∉ S ∧ c i - a i ∉ S ∧ a i ≠ c i - a i) ∧
    ∀ i j, i ≠ j → a i ≠ a j ∧ c i - a i ≠ c j - a j ∧ a i ≠ c j - a j

theorem exists_good (S : Finset K) : ∀ (m : ℕ) (c : Fin m → K), ∃ a, Good S c a
  | 0, c => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | m + 1, c => by
    obtain ⟨a', h1, h2⟩ := exists_good S m (Fin.tail c)
    let X : Finset K := S ∪ Finset.univ.image a' ∪ Finset.univ.image (fun i => Fin.tail c i - a' i)
    obtain ⟨a0, ha0⟩ := Infinite.exists_notMem_finset
      (X ∪ X.image (fun x => c 0 - x) ∪ {c 0 / 2})
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, not_or] at ha0
    obtain ⟨⟨hX, hXc⟩, hhalf⟩ := ha0
    have hX' : ∀ x ∈ X, a0 ≠ x := fun x hx h => hX (h ▸ hx)
    have hXc' : ∀ x ∈ X, c 0 - a0 ≠ x := by
      intro x hx h
      exact hXc ⟨x, hx, by rw [← h]; ring⟩
    have hmemS : ∀ s ∈ S, s ∈ X := fun s hs => by simp [X, hs]
    have hmema : ∀ k, a' k ∈ X := fun k => by simp [X]
    have hmemb : ∀ k, Fin.tail c k - a' k ∈ X := fun k => by
      simp only [X, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inr ⟨k, rfl⟩
    have hself : a0 ≠ c 0 - a0 := by
      intro h
      apply hhalf
      have h2 : (2 : K) ≠ 0 := by exact_mod_cast (two_ne_zero : (2 : ℕ) ≠ 0)
      rw [eq_div_iff h2]
      linear_combination h
    refine ⟨Fin.cons a0 a', ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp only [Fin.cons_zero]
        exact ⟨fun h => hX' _ (hmemS _ h) rfl, fun h => hXc' _ (hmemS _ h) rfl, hself⟩
      · simp only [Fin.cons_succ]
        exact h1 k
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ l =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          have hl : c l.succ = Fin.tail c l := rfl
          rw [hl]
          exact ⟨hX' _ (hmema l), hXc' _ (hmemb l), hX' _ (hmemb l)⟩
      | succ k =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          have hk : c k.succ = Fin.tail c k := rfl
          rw [hk]
          exact ⟨(hX' _ (hmema k)).symm, (hXc' _ (hmemb k)).symm, (hXc' _ (hmema k)).symm⟩
        | succ l =>
          simp only [Fin.cons_succ]
          exact h2 k l (fun h => hij (by rw [h]))

end Lax461425Proofs.SymVFCharacterisationSplit
