import Lax461425Proofs.PatternsLabelledSpanMul
import Lax461425Proofs.PatternsRestrictedMono
import Mathlib.Data.Fin.Tuple.Basic

/-!
---
title: The "all distinct" indicator δ (lem:restricted, construction)
type: definition
---
Let `ℓ, ℓ', r, r' : ℕ` and set `L := ℓ + ℓ'`, `R := r + r'`. For `v : Fin ℓ → Fin n`,
`w : Fin r → Fin n` and `y : Fin ℓ' → Fin n`, `z : Fin r' → Fin n`, write `vy := Fin.append v y`,
`wz := Fin.append w z` for the combined `(L,R)`-labellings.

We construct an element `δ` of `𝔗^{Δ,k}_{n,P}(L,R)` (for every `Δ, k, P` with `P.card ≤ k`) whose
value at `(vy, wz)` is `1` exactly when `vy` and `wz` are injective, i.e. (given `v, w` already
injective) exactly when `y` is injective with range disjoint from that of `v`, and `z` is
injective with range disjoint from that of `w` — i.e. `(y, z) ∈ Y(v, w)` in the notation of
`lem:restricted`. `δ` is a product, over all pairs of distinct label positions on the same side
with at least one "new" (one of the last `ℓ'` left or `r'` right positions), of `J_n - D^{i,j}_n`
where `D^{i,j}` identifies positions `i, j`: each factor evaluates to `1` unless the two
positions get the same value, so the product is `1` exactly when all these positions are
pairwise distinct.
-/

namespace Lax461425Proofs.PatternsRestrictedDelta

open Lax461425.HomomorphismPolynomials Lax461425Proofs.PatternsLabelledBasic
open Lax461425Proofs.PatternsLabelledOps Lax461425Proofs.PatternsLabelledSpanMul
open Lax461425Proofs.PatternsRestrictedMono
open scoped Classical

/-! ### A finite "product of 0/1 indicators" helper -/

/-- The product, over a finite set `s`, of a family that is `0` whenever a side-condition `Q i`
holds and `1` otherwise, is `1` if `Q` never holds on `s` and `0` if it holds somewhere on `s`. -/
theorem prod_ite_zero_one {ι R : Type*} [DecidableEq ι] [CommMonoidWithZero R] (s : Finset ι)
    (Q : ι → Prop) [DecidablePred Q] :
    (∏ i ∈ s, if Q i then (0 : R) else 1) = if (∀ i ∈ s, ¬ Q i) then 1 else 0 := by
  by_cases h : ∀ i ∈ s, ¬ Q i
  · rw [if_pos h]
    exact Finset.prod_eq_one fun i hi => if_neg (h i hi)
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i0, hi0, hQi0⟩ := h
    exact Finset.prod_eq_zero hi0 (if_pos hQi0)

/-- A function out of a linearly ordered type is injective iff it takes distinct values on every
pair of indices `i < j`. -/
theorem injective_iff_forall_lt_ne {ι α : Type*} [LinearOrder ι] (f : ι → α) :
    Function.Injective f ↔ ∀ i j : ι, i < j → f i ≠ f j := by
  constructor
  · intro hf i j hij hfij
    exact hij.ne (hf hfij)
  · intro h i j hfij
    rcases lt_trichotomy i j with hlt | heq | hlt
    · exact absurd hfij (h i j hlt)
    · exact heq
    · exact absurd hfij.symm (h j i hlt)

variable {L R : ℕ}

/-! ### Merging two label positions on the same side -/

/-- The underlying "merge `p` into `q`" function on `Fin L`: sends `q` to `p` and fixes
everything else. -/
def mergeAux (L : ℕ) (p q : Fin L) : Fin L → Fin L := fun i => if i = q then p else i

theorem mergeAux_ne {L : ℕ} {p q : Fin L} (hpq : p ≠ q) (i : Fin L) : mergeAux L p q i ≠ q := by
  unfold mergeAux
  split
  · exact hpq
  · assumption

@[simp] theorem mergeAux_self (L : ℕ) (p q : Fin L) : mergeAux L p q q = p := if_pos rfl

theorem mergeAux_of_ne {L : ℕ} (p q : Fin L) {i : Fin L} (hi : i ≠ q) : mergeAux L p q i = i :=
  if_neg hi

/-- The edgeless `(L,R)`-labelled graph identifying label positions `p, q : Fin L` (distinct) on
the `A`-side, with every other position on its own vertex: the `A`-side vertex set is `Fin L`
with `q` deleted, and `p` plays the role of the merged vertex. -/
def mergeA (L R : ℕ) (p q : Fin L) (hpq : p ≠ q) : LabelledPattern L R where
  F := { A := {x : Fin L // x ≠ q}, B := Fin R, mult := fun _ _ => 0 }
  a := fun i => ⟨mergeAux L p q i, mergeAux_ne hpq i⟩
  b := id

/-- The edgeless `(L,R)`-labelled graph identifying label positions `p, q : Fin R` (distinct) on
the `B`-side, with every other position on its own vertex. -/
def mergeB (L R : ℕ) (p q : Fin R) (hpq : p ≠ q) : LabelledPattern L R where
  F := { A := Fin L, B := {x : Fin R // x ≠ q}, mult := fun _ _ => 0 }
  a := id
  b := fun j => ⟨mergeAux R p q j, mergeAux_ne hpq j⟩

theorem mergeA_isEdgeless (L R : ℕ) (p q : Fin L) (hpq : p ≠ q) :
    isEdgeless (mergeA L R p q hpq).F := fun _ _ => rfl

theorem mergeB_isEdgeless (L R : ℕ) (p q : Fin R) (hpq : p ≠ q) :
    isEdgeless (mergeB L R p q hpq).F := fun _ _ => rfl

theorem mergeA_a_eq (L R : ℕ) (p q : Fin L) (hpq : p ≠ q) (i : Fin L) :
    (mergeA L R p q hpq).a i = (⟨mergeAux L p q i, mergeAux_ne hpq i⟩ :
      (mergeA L R p q hpq).F.A) := rfl

theorem mergeB_b_eq (L R : ℕ) (p q : Fin R) (hpq : p ≠ q) (j : Fin R) :
    (mergeB L R p q hpq).b j = (⟨mergeAux R p q j, mergeAux_ne hpq j⟩ :
      (mergeB L R p q hpq).F.B) := rfl

/-- **The value of `mergeA`'s homomorphism polynomial**: `1` if `v p = v q`, else `0`. -/
theorem labelledHom_mergeA (L R : ℕ) (p q : Fin L) (hpq : p ≠ q) (n : ℕ) (K : Type*)
    [CommSemiring K] (v : Fin L → Fin n) (w : Fin R → Fin n) :
    labelledHom K (mergeA L R p q hpq) n v w = if v p = v q then 1 else 0 := by
  set hA0 : {x : Fin L // x ≠ q} → Fin n := fun x => v x.1 with hhA0
  have key : ∀ i : Fin L, (hi : i ≠ q) →
      (mergeA L R p q hpq).a i = (⟨i, hi⟩ : {x : Fin L // x ≠ q}) := by
    intro i hi
    rw [mergeA_a_eq]
    exact Subtype.ext (mergeAux_of_ne p q hi)
  have keyq : (mergeA L R p q hpq).a q = (⟨p, hpq⟩ : {x : Fin L // x ≠ q}) := by
    rw [mergeA_a_eq]
    exact Subtype.ext (mergeAux_self L p q)
  have hcond : ∀ hA : {x : Fin L // x ≠ q} → Fin n,
      (∀ i, hA ((mergeA L R p q hpq).a i) = v i) ↔ (v p = v q ∧ hA = hA0) := by
    intro hA
    constructor
    · intro h
      have hp : hA ⟨p, hpq⟩ = v p := by rw [← key p hpq]; exact h p
      have hq : hA ⟨p, hpq⟩ = v q := by rw [← keyq]; exact h q
      refine ⟨hp ▸ hq, ?_⟩
      funext x
      obtain ⟨i, hi⟩ := x
      rw [hhA0]
      show hA ⟨i, hi⟩ = v i
      rw [← key i hi]
      exact h i
    · rintro ⟨hvpq, rfl⟩ i
      by_cases hiq : i = q
      · rw [hiq, keyq, hhA0]
        exact hvpq
      · rw [key i hiq, hhA0]
  show (∑ hA : {x : Fin L // x ≠ q} → Fin n, ∑ hB : Fin R → Fin n,
      if (∀ i, hA ((mergeA L R p q hpq).a i) = v i) ∧ (∀ j, hB (id j) = w j) then
        (∏ x : {x : Fin L // x ≠ q}, ∏ y, MvPolynomial.X (hA x, hB y) ^ (0 : ℕ) :
          MvPolynomial (Fin n × Fin n) K)
      else 0) = if v p = v q then 1 else 0
  simp only [pow_zero, Finset.prod_const_one]
  by_cases hvpq : v p = v q
  · rw [if_pos hvpq, Finset.sum_eq_single hA0]
    · rw [Finset.sum_eq_single w]
      · exact if_pos ⟨(hcond hA0).mpr ⟨hvpq, rfl⟩, by simp⟩
      · intro hB _ hne
        exact if_neg (fun h => hne (funext h.2))
      · intro h; exact absurd (Finset.mem_univ w) h
    · intro hA _ hne
      apply Finset.sum_eq_zero
      intro hB _
      exact if_neg (fun h => hne ((hcond hA).mp h.1).2)
    · intro h; exact absurd (Finset.mem_univ hA0) h
  · rw [if_neg hvpq]
    apply Finset.sum_eq_zero
    intro hA _
    apply Finset.sum_eq_zero
    intro hB _
    exact if_neg (fun h => hvpq ((hcond hA).mp h.1).1)

/-- **The value of `mergeB`'s homomorphism polynomial**: `1` if `w p = w q`, else `0`. -/
theorem labelledHom_mergeB (L R : ℕ) (p q : Fin R) (hpq : p ≠ q) (n : ℕ) (K : Type*)
    [CommSemiring K] (v : Fin L → Fin n) (w : Fin R → Fin n) :
    labelledHom K (mergeB L R p q hpq) n v w = if w p = w q then 1 else 0 := by
  set hB0 : {x : Fin R // x ≠ q} → Fin n := fun x => w x.1 with hhB0
  have key : ∀ j : Fin R, (hj : j ≠ q) →
      (mergeB L R p q hpq).b j = (⟨j, hj⟩ : {x : Fin R // x ≠ q}) := by
    intro j hj
    rw [mergeB_b_eq]
    exact Subtype.ext (mergeAux_of_ne p q hj)
  have keyq : (mergeB L R p q hpq).b q = (⟨p, hpq⟩ : {x : Fin R // x ≠ q}) := by
    rw [mergeB_b_eq]
    exact Subtype.ext (mergeAux_self R p q)
  have hcond : ∀ hB : {x : Fin R // x ≠ q} → Fin n,
      (∀ j, hB ((mergeB L R p q hpq).b j) = w j) ↔ (w p = w q ∧ hB = hB0) := by
    intro hB
    constructor
    · intro h
      have hp : hB ⟨p, hpq⟩ = w p := by rw [← key p hpq]; exact h p
      have hq : hB ⟨p, hpq⟩ = w q := by rw [← keyq]; exact h q
      refine ⟨hp ▸ hq, ?_⟩
      funext x
      obtain ⟨j, hj⟩ := x
      rw [hhB0]
      show hB ⟨j, hj⟩ = w j
      rw [← key j hj]
      exact h j
    · rintro ⟨hwpq, rfl⟩ j
      by_cases hjq : j = q
      · rw [hjq, keyq, hhB0]
        exact hwpq
      · rw [key j hjq, hhB0]
  show (∑ hA : Fin L → Fin n, ∑ hB : {x : Fin R // x ≠ q} → Fin n,
      if (∀ i, hA (id i) = v i) ∧ (∀ j, hB ((mergeB L R p q hpq).b j) = w j) then
        (∏ x : Fin L, ∏ y : {x : Fin R // x ≠ q}, MvPolynomial.X (hA x, hB y) ^ (0 : ℕ) :
          MvPolynomial (Fin n × Fin n) K)
      else 0) = if w p = w q then 1 else 0
  simp only [pow_zero, Finset.prod_const_one]
  by_cases hwpq : w p = w q
  · rw [if_pos hwpq, Finset.sum_eq_single v]
    · rw [Finset.sum_eq_single hB0]
      · exact if_pos ⟨by simp, (hcond hB0).mpr ⟨hwpq, rfl⟩⟩
      · intro hB _ hne
        exact if_neg (fun h => hne (((hcond hB).mp h.2).2))
      · intro h; exact absurd (Finset.mem_univ hB0) h
    · intro hA _ hne
      apply Finset.sum_eq_zero
      intro hB _
      exact if_neg (fun h => hne (funext h.1))
    · intro h; exact absurd (Finset.mem_univ v) h
  · rw [if_neg hwpq]
    apply Finset.sum_eq_zero
    intro hA _
    apply Finset.sum_eq_zero
    intro hB _
    exact if_neg (fun h => hwpq ((hcond hB).mp h.2).1)

end Lax461425Proofs.PatternsRestrictedDelta
