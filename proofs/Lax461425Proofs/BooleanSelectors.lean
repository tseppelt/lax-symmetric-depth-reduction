import Lax461425.SymmetricFamilies
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
The exactly-one Boolean selector used by the formula witness in Section 7. These identities
are proved over a commutative ring; no characteristic-zero assumption is needed here.
-/

namespace Lax461425Proofs.BooleanSelectors

open scoped Classical BigOperators

variable {K : Type*} [CommRing K] {n : ℕ}

/-- A Boolean as a ring element. -/
def bit (b : Bool) : K := if b then 1 else 0

/-- The paper's selector: at least one image, and no pair of selected images. -/
def exactlyOne (e : Fin n → Bool) : K :=
  (∑ i, bit (e i)) * ∏ i, ∏ j ∈ Finset.univ.filter (i < ·),
    (1 - bit (e i) * bit (e j))

/-- A pair of selected coordinates makes the selector vanish. -/
theorem exactlyOne_eq_zero_of_pair (e : Fin n → Bool) {i j : Fin n}
    (hij : i < j) (hi : e i = true) (hj : e j = true) : exactlyOne (K := K) e = 0 := by
  unfold exactlyOne
  have hz : (∏ a : Fin n, ∏ b ∈ Finset.univ.filter (a < ·),
      (1 - bit (K := K) (e a) * bit (e b))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hij⟩)
    simp [hi, hj, bit]
  rw [hz, mul_zero]

/-- Selecting no coordinate also makes the selector vanish. -/
theorem exactlyOne_eq_zero_of_none (e : Fin n → Bool) (he : ∀ i, e i = false) :
    exactlyOne (K := K) e = 0 := by
  simp [exactlyOne, he, bit]

/-- If just one coordinate is selected, the selector is one. -/
theorem exactlyOne_eq_one (e : Fin n → Bool) (i : Fin n)
    (hi : e i = true) (he : ∀ j, j ≠ i → e j = false) : exactlyOne (K := K) e = 1 := by
  have hsum : (∑ j : Fin n, bit (K := K) (e j)) = 1 := by
    rw [Finset.sum_eq_single i]
    · simp [hi, bit]
    · intro j hj hji
      simp [he j hji, bit]
    · simp
  have hprod : (∏ a : Fin n, ∏ b ∈ Finset.univ.filter (a < ·),
      (1 - bit (K := K) (e a) * bit (e b))) = 1 := by
    apply Finset.prod_eq_one
    intro a ha
    apply Finset.prod_eq_one
    intro b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    by_cases hai : a = i
    · subst a
      have hbi : b ≠ i := ne_of_gt hab
      simp [he b hbi, bit]
    · simp [he a hai, bit]
  simp [exactlyOne, hsum, hprod]

/-- The value is precisely the indicator of a unique selected coordinate. -/
theorem exactlyOne_eq_indicator (e : Fin n → Bool) :
    exactlyOne (K := K) e = if ∃! i, e i = true then 1 else 0 := by
  by_cases h : ∃! i, e i = true
  · obtain ⟨i, hi, hu⟩ := h
    rw [if_pos ⟨i, hi, hu⟩]
    apply exactlyOne_eq_one e i hi
    intro j hji
    cases hej : e j
    · rfl
    · exact False.elim (hji (hu j hej))
  · rw [if_neg h]
    by_cases he : ∃ i, e i = true
    · obtain ⟨i, hi⟩ := he
      have hj : ∃ j, e j = true ∧ j ≠ i := by
        by_contra hn
        apply h
        refine ⟨i, hi, ?_⟩
        intro j hj
        by_contra hji
        exact hn ⟨j, hj, hji⟩
      obtain ⟨j, hj, hji⟩ := hj
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · exact exactlyOne_eq_zero_of_pair e hlt hj hi
      · exact exactlyOne_eq_zero_of_pair e hgt hi hj
    · apply exactlyOne_eq_zero_of_none
      intro i
      cases hei : e i
      · rfl
      · exact False.elim (he ⟨i, hei⟩)

/-- The assignment encoding a chosen image. -/
def encode (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

theorem encode_unique (i : Fin n) : ∃! j, encode i j = true := by
  refine ⟨i, by simp [encode], ?_⟩
  intro j hj
  simpa [encode] using hj

/-- Exactly-one Boolean assignments are in bijection with image choices, including the
empty-index case. -/
noncomputable def encodingEquiv : Fin n ≃ {e : Fin n → Bool // ∃! i, e i = true} where
  toFun i := ⟨encode i, encode_unique i⟩
  invFun e := Classical.choose e.property
  left_inv i := by
    have h := (Classical.choose_spec (encode_unique i)).1
    simpa [encode] using h
  right_inv e := by
    apply Subtype.ext
    funext j
    let i := Classical.choose e.property
    have hi : e.val i = true := (Classical.choose_spec e.property).1
    have hu : ∀ j, e.val j = true → j = i := (Classical.choose_spec e.property).2
    change encode i j = e.val j
    by_cases hji : j = i
    · subst j
      simp [encode, hi]
    · cases hej : e.val j
      · simp [encode, hji]
      · exact False.elim (hji (hu j hej))

/-- Summing a function against the exactly-one selector enumerates image choices once. -/
theorem sum_exactlyOne (f : (Fin n → Bool) → K) :
    (∑ e : Fin n → Bool, exactlyOne e * f e) = ∑ i : Fin n, f (encode i) := by
  let P (e : Fin n → Bool) := ∃! i, e i = true
  have hsplit := Fintype.sum_subtype_add_sum_subtype P (fun e => exactlyOne (K := K) e * f e)
  have hz : (∑ e : {e : Fin n → Bool // ¬P e}, exactlyOne (K := K) e.val * f e.val) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    rw [exactlyOne_eq_indicator, if_neg e.property, zero_mul]
  rw [hz, add_zero] at hsplit
  rw [← hsplit]
  calc
    (∑ e : {e : Fin n → Bool // P e}, exactlyOne (K := K) e.val * f e.val) =
        ∑ e : {e : Fin n → Bool // P e}, f e.val := by
      apply Finset.sum_congr rfl
      intro e he
      rw [exactlyOne_eq_indicator, if_pos e.property, one_mul]
    _ = ∑ i : Fin n, f (encode i) :=
      (Equiv.sum_comp encodingEquiv (fun e => f e.val)).symm

variable {A : Type*} [Fintype A]

/-- The collection of image choices, encoded row by row. -/
def encodeMaps (h : A → Fin n) : A × Fin n → Bool := fun x => encode (h x.1) x.2

/-- An assignment chooses exactly one image for each pattern vertex. -/
def Valid (e : A × Fin n → Bool) : Prop := ∀ a, ∃! i, e (a, i) = true

theorem encodeMaps_valid (h : A → Fin n) : Valid (encodeMaps h) :=
  fun a => encode_unique (h a)

/-- Simultaneous exactly-one assignments encode vertex maps bijectively. -/
noncomputable def mapsEncodingEquiv : (A → Fin n) ≃ {e : A × Fin n → Bool // Valid e} where
  toFun h := ⟨encodeMaps h, encodeMaps_valid h⟩
  invFun e a := Classical.choose (e.property a)
  left_inv h := by
    funext a
    have hc := (Classical.choose_spec (encodeMaps_valid h a)).1
    simpa [encodeMaps, encode] using hc
  right_inv e := by
    apply Subtype.ext
    funext x
    rcases x with ⟨a, j⟩
    have hrow := (encodingEquiv (n := n)).apply_symm_apply
      ⟨fun i => e.val (a, i), e.property a⟩
    exact congrFun (congrArg Subtype.val hrow) j

/-- Product of the vertex selectors. -/
def allSelectors (e : A × Fin n → Bool) : K :=
  ∏ a, exactlyOne (fun i => e (a, i))

theorem allSelectors_eq_indicator (e : A × Fin n → Bool) :
    allSelectors (K := K) e = if Valid e then 1 else 0 := by
  by_cases he : Valid e
  · rw [if_pos he]
    apply Finset.prod_eq_one
    intro a ha
    rw [exactlyOne_eq_indicator, if_pos (he a)]
  · rw [if_neg he]
    obtain ⟨a, ha⟩ := Classical.not_forall.mp he
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    rw [exactlyOne_eq_indicator, if_neg ha]

/-- Summing against all vertex selectors enumerates every vertex map exactly once. -/
theorem sum_allSelectors (f : (A × Fin n → Bool) → K) :
    (∑ e : A × Fin n → Bool, allSelectors e * f e) = ∑ h : A → Fin n, f (encodeMaps h) := by
  have hs := Fintype.sum_subtype_add_sum_subtype (Valid (A := A) (n := n))
    (fun e => allSelectors (K := K) e * f e)
  have hz : (∑ e : {e : A × Fin n → Bool // ¬Valid e},
      allSelectors (K := K) e.val * f e.val) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    rw [allSelectors_eq_indicator, if_neg e.property, zero_mul]
  rw [hz, add_zero] at hs
  rw [← hs]
  calc
    (∑ e : {e : A × Fin n → Bool // Valid e}, allSelectors (K := K) e.val * f e.val) =
        ∑ e : {e : A × Fin n → Bool // Valid e}, f e.val := by
      apply Finset.sum_congr rfl
      intro e he
      rw [allSelectors_eq_indicator, if_pos e.property, one_mul]
    _ = ∑ h : A → Fin n, f (encodeMaps h) :=
      (Equiv.sum_comp mapsEncodingEquiv (fun e => f e.val)).symm

end Lax461425Proofs.BooleanSelectors
