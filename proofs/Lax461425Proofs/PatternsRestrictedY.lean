import Lax461425Proofs.PatternsRestrictedDelta

/-!
---
title: The injective-extension set Y(v,w) and the all-distinct indicator δ
type: definition
---
For `v : Fin ℓ → Fin n`, `w : Fin r → Fin n`, `Y ℓ' r' n v w` is the `Finset` of pairs
`(y, z) : (Fin ℓ' → Fin n) × (Fin r' → Fin n)` such that `Fin.append v y` and `Fin.append w z`
are both injective: when `v, w` are themselves injective, this says exactly that `y` is injective
with range disjoint from that of `v`, and likewise for `z, w` (`Fin.append_injective_iff`).

`δ` is the pointwise product, over all pairs of distinct label positions on the same side with
at least one among the last `ℓ'` left or `r'` right positions, of `J_n - D^{i,j}_n`
(`PatternsRestrictedDelta.mergeA`/`mergeB` for `D^{i,j}`): we show `δ (Fin.append v y)
(Fin.append w z)` is the `0`/`1` indicator of `(y, z) ∈ Y ℓ' r' n v w`, given `v, w` injective.
-/

namespace Lax461425Proofs.PatternsRestrictedY

open Lax461425.HomomorphismPolynomials Lax461425Proofs.PatternsLabelledBasic
open Lax461425Proofs.PatternsLabelledOps Lax461425Proofs.PatternsLabelledSpanMul
open Lax461425Proofs.PatternsRestrictedMono Lax461425Proofs.PatternsRestrictedDelta
open scoped Classical

variable {ℓ ℓ' r r' : ℕ}

/-! ### The injective-extension set `Y(v, w)` -/

/-- `Y ℓ' r' n v w`: the pairs `(y, z)` such that `Fin.append v y` and `Fin.append w z` are both
injective. -/
def Y (ℓ' r' : ℕ) {ℓ r : ℕ} (n : ℕ) (v : Fin ℓ → Fin n) (w : Fin r → Fin n) :
    Finset ((Fin ℓ' → Fin n) × (Fin r' → Fin n)) :=
  Finset.univ.filter (fun yz =>
    Function.Injective (Fin.append v yz.1) ∧ Function.Injective (Fin.append w yz.2))

theorem mem_Y {n : ℕ} {v : Fin ℓ → Fin n} {w : Fin r → Fin n}
    {yz : (Fin ℓ' → Fin n) × (Fin r' → Fin n)} :
    yz ∈ Y ℓ' r' n v w ↔
      Function.Injective (Fin.append v yz.1) ∧ Function.Injective (Fin.append w yz.2) := by
  simp [Y]

/-! ### Pairwise-distinctness index sets -/

theorem castAdd_ne_natAdd (ℓ ℓ' : ℕ) (i : Fin ℓ) (j : Fin ℓ') :
    Fin.castAdd ℓ' i ≠ Fin.natAdd ℓ j := by
  intro h
  have hval := congrArg Fin.val h
  rw [Fin.val_castAdd, Fin.val_natAdd] at hval
  have := i.isLt
  omega

theorem natAdd_ne_natAdd_of_ne {ℓ ℓ' : ℕ} {i j : Fin ℓ'} (hij : i ≠ j) :
    Fin.natAdd ℓ i ≠ Fin.natAdd ℓ j := (Fin.natAdd_inj ℓ).not.mpr hij

/-- The unordered pairs `i < j` of `Fin m`. -/
def newPairs (m : ℕ) : Finset (Fin m × Fin m) := Finset.univ.filter (fun p => p.1 < p.2)

theorem mem_newPairs {m : ℕ} {p : Fin m × Fin m} : p ∈ newPairs m ↔ p.1 < p.2 := by
  simp [newPairs]

/-! ### A single `J_n - D^{i,j}_n` factor -/

/-- `J_n - D^{p,q}_n` on the `A`-side (left positions `p ≠ q` of `L`). -/
noncomputable def factorA (K : Type*) [Field K] (L R n : ℕ) (p q : Fin L) (hpq : p ≠ q)
    (v : Fin L → Fin n) (w : Fin R → Fin n) : MvPolynomial (Fin n × Fin n) K :=
  labelledHom K (J L R) n v w - labelledHom K (mergeA L R p q hpq) n v w

/-- `J_n - D^{p,q}_n` on the `B`-side (right positions `p ≠ q` of `R`). -/
noncomputable def factorB (K : Type*) [Field K] (L R n : ℕ) (p q : Fin R) (hpq : p ≠ q)
    (v : Fin L → Fin n) (w : Fin R → Fin n) : MvPolynomial (Fin n × Fin n) K :=
  labelledHom K (J L R) n v w - labelledHom K (mergeB L R p q hpq) n v w

theorem factorA_eval (K : Type*) [Field K] (L R n : ℕ) (p q : Fin L) (hpq : p ≠ q)
    (v : Fin L → Fin n) (w : Fin R → Fin n) :
    factorA K L R n p q hpq v w = if v p = v q then (0 : MvPolynomial (Fin n × Fin n) K) else 1 := by
  rw [factorA, labelledHom_J, labelledHom_mergeA]
  by_cases h : v p = v q <;> simp [h]

theorem factorB_eval (K : Type*) [Field K] (L R n : ℕ) (p q : Fin R) (hpq : p ≠ q)
    (v : Fin L → Fin n) (w : Fin R → Fin n) :
    factorB K L R n p q hpq v w = if w p = w q then (0 : MvPolynomial (Fin n × Fin n) K) else 1 := by
  rw [factorB, labelledHom_J, labelledHom_mergeB]
  by_cases h : w p = w q <;> simp [h]

/-! ### The all-distinct indicator `δ` -/

/-- **`δ`**: the pointwise product, over all pairs of distinct label positions on the same side
with at least one among the last `ℓ'` left or `r'` right positions, of `J_n - D^{i,j}_n`. -/
noncomputable def δ (K : Type*) [Field K] (ℓ ℓ' r r' : ℕ) (n : ℕ) :
    (Fin (ℓ + ℓ') → Fin n) → (Fin (r + r') → Fin n) → MvPolynomial (Fin n × Fin n) K :=
  fun v w =>
    ((∏ p : Fin ℓ × Fin ℓ', factorA K (ℓ + ℓ') (r + r') n (Fin.castAdd ℓ' p.1) (Fin.natAdd ℓ p.2)
        (castAdd_ne_natAdd ℓ ℓ' p.1 p.2) v w) *
      (∏ p ∈ (newPairs ℓ').attach, factorA K (ℓ + ℓ') (r + r') n
        (Fin.natAdd ℓ p.1.1) (Fin.natAdd ℓ p.1.2)
        (natAdd_ne_natAdd_of_ne (ne_of_lt (mem_newPairs.mp p.2))) v w)) *
    ((∏ p : Fin r × Fin r', factorB K (ℓ + ℓ') (r + r') n (Fin.castAdd r' p.1) (Fin.natAdd r p.2)
        (castAdd_ne_natAdd r r' p.1 p.2) v w) *
      (∏ p ∈ (newPairs r').attach, factorB K (ℓ + ℓ') (r + r') n
        (Fin.natAdd r p.1.1) (Fin.natAdd r p.1.2)
        (natAdd_ne_natAdd_of_ne (ne_of_lt (mem_newPairs.mp p.2))) v w))

/-! ### A couple of generic combinators -/

theorem ite_mul_ite_one_zero {S : Type*} [MulZeroOneClass S] {P Q : Prop} [Decidable P]
    [Decidable Q] : (if P then (1 : S) else 0) * (if Q then (1 : S) else 0) =
      if P ∧ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- The left-side pair of factors (cross + new-new) collapses to the indicator of injectivity
of the extended left labelling. -/
theorem δ_left_eval (K : Type*) [Field K] (n : ℕ) (v : Fin ℓ → Fin n) (y : Fin ℓ' → Fin n)
    (w : Fin (r + r') → Fin n) (hv : Function.Injective v) :
    (∏ p : Fin ℓ × Fin ℓ', factorA K (ℓ + ℓ') (r + r') n (Fin.castAdd ℓ' p.1) (Fin.natAdd ℓ p.2)
        (castAdd_ne_natAdd ℓ ℓ' p.1 p.2) (Fin.append v y) w) *
      (∏ p ∈ (newPairs ℓ').attach, factorA K (ℓ + ℓ') (r + r') n
        (Fin.natAdd ℓ p.1.1) (Fin.natAdd ℓ p.1.2)
        (natAdd_ne_natAdd_of_ne (ne_of_lt (mem_newPairs.mp p.2))) (Fin.append v y) w) =
      if Function.Injective (Fin.append v y) then (1 : MvPolynomial (Fin n × Fin n) K) else 0 := by
  have h1 : (∏ p : Fin ℓ × Fin ℓ', factorA K (ℓ + ℓ') (r + r') n (Fin.castAdd ℓ' p.1)
        (Fin.natAdd ℓ p.2) (castAdd_ne_natAdd ℓ ℓ' p.1 p.2) (Fin.append v y) w) =
      if (∀ i : Fin ℓ, ∀ j : Fin ℓ', v i ≠ y j) then (1 : MvPolynomial (Fin n × Fin n) K) else 0 := by
    have heq : ∀ p : Fin ℓ × Fin ℓ', factorA K (ℓ + ℓ') (r + r') n (Fin.castAdd ℓ' p.1)
        (Fin.natAdd ℓ p.2) (castAdd_ne_natAdd ℓ ℓ' p.1 p.2) (Fin.append v y) w =
        if v p.1 = y p.2 then (0 : MvPolynomial (Fin n × Fin n) K) else 1 := by
      intro p
      rw [factorA_eval, Fin.append_left, Fin.append_right]
    rw [Finset.prod_congr rfl (fun p _ => heq p)]
    rw [show (∏ p : Fin ℓ × Fin ℓ', if v p.1 = y p.2 then (0 : MvPolynomial (Fin n × Fin n) K)
        else 1) = ∏ p ∈ (Finset.univ : Finset (Fin ℓ × Fin ℓ')),
          if v p.1 = y p.2 then (0 : MvPolynomial (Fin n × Fin n) K) else 1 from rfl]
    rw [prod_ite_zero_one]
    have hiff : (∀ i ∈ (Finset.univ : Finset (Fin ℓ × Fin ℓ')), ¬ v i.1 = y i.2) ↔
        (∀ i : Fin ℓ, ∀ j : Fin ℓ', v i ≠ y j) :=
      ⟨fun h i j => h ⟨i, j⟩ (Finset.mem_univ _), fun h p _ => h p.1 p.2⟩
    simp only [hiff]
  have h2 : (∏ p ∈ (newPairs ℓ').attach, factorA K (ℓ + ℓ') (r + r') n
        (Fin.natAdd ℓ p.1.1) (Fin.natAdd ℓ p.1.2)
        (natAdd_ne_natAdd_of_ne (ne_of_lt (mem_newPairs.mp p.2))) (Fin.append v y) w) =
      if Function.Injective y then (1 : MvPolynomial (Fin n × Fin n) K) else 0 := by
    have heq : ∀ p : (newPairs ℓ'), factorA K (ℓ + ℓ') (r + r') n
        (Fin.natAdd ℓ p.1.1) (Fin.natAdd ℓ p.1.2)
        (natAdd_ne_natAdd_of_ne (ne_of_lt (mem_newPairs.mp p.2))) (Fin.append v y) w =
        if y p.1.1 = y p.1.2 then (0 : MvPolynomial (Fin n × Fin n) K) else 1 := by
      intro p
      rw [factorA_eval, Fin.append_right, Fin.append_right]
    rw [Finset.prod_congr rfl (fun p _ => heq p)]
    rw [Finset.prod_attach (newPairs ℓ')
      (fun p => if y p.1 = y p.2 then (0 : MvPolynomial (Fin n × Fin n) K) else 1)]
    rw [prod_ite_zero_one]
    have hiff : (∀ p ∈ newPairs ℓ', ¬ y p.1 = y p.2) ↔ Function.Injective y := by
      rw [injective_iff_forall_lt_ne]
      exact ⟨fun h i j hij => h (i, j) (mem_newPairs.mpr hij), fun h p hp => h p.1 p.2
        (mem_newPairs.mp hp)⟩
    simp only [hiff]
  rw [h1, h2, ite_mul_ite_one_zero]
  have hiff : ((∀ i : Fin ℓ, ∀ j : Fin ℓ', v i ≠ y j) ∧ Function.Injective y) ↔
      Function.Injective (Fin.append v y) := by
    rw [Fin.append_injective_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hv, h2, h1⟩
    · rintro ⟨-, h2, h1⟩
      exact ⟨h1, h2⟩
  simp only [hiff]

/-- The right-side pair of factors (cross + new-new) collapses to the indicator of injectivity
of the extended right labelling. -/
theorem δ_right_eval (K : Type*) [Field K] (n : ℕ) (w : Fin r → Fin n) (z : Fin r' → Fin n)
    (v : Fin (ℓ + ℓ') → Fin n) (hw : Function.Injective w) :
    (∏ p : Fin r × Fin r', factorB K (ℓ + ℓ') (r + r') n (Fin.castAdd r' p.1) (Fin.natAdd r p.2)
        (castAdd_ne_natAdd r r' p.1 p.2) v (Fin.append w z)) *
      (∏ p ∈ (newPairs r').attach, factorB K (ℓ + ℓ') (r + r') n
        (Fin.natAdd r p.1.1) (Fin.natAdd r p.1.2)
        (natAdd_ne_natAdd_of_ne (ne_of_lt (mem_newPairs.mp p.2))) v (Fin.append w z)) =
      if Function.Injective (Fin.append w z) then (1 : MvPolynomial (Fin n × Fin n) K) else 0 := by
  have h1 : (∏ p : Fin r × Fin r', factorB K (ℓ + ℓ') (r + r') n (Fin.castAdd r' p.1)
        (Fin.natAdd r p.2) (castAdd_ne_natAdd r r' p.1 p.2) v (Fin.append w z)) =
      if (∀ i : Fin r, ∀ j : Fin r', w i ≠ z j) then (1 : MvPolynomial (Fin n × Fin n) K) else 0 := by
    have heq : ∀ p : Fin r × Fin r', factorB K (ℓ + ℓ') (r + r') n (Fin.castAdd r' p.1)
        (Fin.natAdd r p.2) (castAdd_ne_natAdd r r' p.1 p.2) v (Fin.append w z) =
        if w p.1 = z p.2 then (0 : MvPolynomial (Fin n × Fin n) K) else 1 := by
      intro p
      rw [factorB_eval, Fin.append_left, Fin.append_right]
    rw [Finset.prod_congr rfl (fun p _ => heq p)]
    rw [show (∏ p : Fin r × Fin r', if w p.1 = z p.2 then (0 : MvPolynomial (Fin n × Fin n) K)
        else 1) = ∏ p ∈ (Finset.univ : Finset (Fin r × Fin r')),
          if w p.1 = z p.2 then (0 : MvPolynomial (Fin n × Fin n) K) else 1 from rfl]
    rw [prod_ite_zero_one]
    have hiff : (∀ i ∈ (Finset.univ : Finset (Fin r × Fin r')), ¬ w i.1 = z i.2) ↔
        (∀ i : Fin r, ∀ j : Fin r', w i ≠ z j) :=
      ⟨fun h i j => h ⟨i, j⟩ (Finset.mem_univ _), fun h p _ => h p.1 p.2⟩
    simp only [hiff]
  have h2 : (∏ p ∈ (newPairs r').attach, factorB K (ℓ + ℓ') (r + r') n
        (Fin.natAdd r p.1.1) (Fin.natAdd r p.1.2)
        (natAdd_ne_natAdd_of_ne (ne_of_lt (mem_newPairs.mp p.2))) v (Fin.append w z)) =
      if Function.Injective z then (1 : MvPolynomial (Fin n × Fin n) K) else 0 := by
    have heq : ∀ p : (newPairs r'), factorB K (ℓ + ℓ') (r + r') n
        (Fin.natAdd r p.1.1) (Fin.natAdd r p.1.2)
        (natAdd_ne_natAdd_of_ne (ne_of_lt (mem_newPairs.mp p.2))) v (Fin.append w z) =
        if z p.1.1 = z p.1.2 then (0 : MvPolynomial (Fin n × Fin n) K) else 1 := by
      intro p
      rw [factorB_eval, Fin.append_right, Fin.append_right]
    rw [Finset.prod_congr rfl (fun p _ => heq p)]
    rw [Finset.prod_attach (newPairs r')
      (fun p => if z p.1 = z p.2 then (0 : MvPolynomial (Fin n × Fin n) K) else 1)]
    rw [prod_ite_zero_one]
    have hiff : (∀ p ∈ newPairs r', ¬ z p.1 = z p.2) ↔ Function.Injective z := by
      rw [injective_iff_forall_lt_ne]
      exact ⟨fun h i j hij => h (i, j) (mem_newPairs.mpr hij), fun h p hp => h p.1 p.2
        (mem_newPairs.mp hp)⟩
    simp only [hiff]
  rw [h1, h2, ite_mul_ite_one_zero]
  have hiff : ((∀ i : Fin r, ∀ j : Fin r', w i ≠ z j) ∧ Function.Injective z) ↔
      Function.Injective (Fin.append w z) := by
    rw [Fin.append_injective_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hw, h2, h1⟩
    · rintro ⟨-, h2, h1⟩
      exact ⟨h1, h2⟩
  simp only [hiff]

/-- **`δ`'s evaluation**: given `v, w` injective, `δ` at `(Fin.append v y, Fin.append w z)` is
the `0`/`1` indicator of `(y, z) ∈ Y ℓ' r' n v w`. -/
theorem δ_eval (K : Type*) [Field K] (n : ℕ) (v : Fin ℓ → Fin n) (w : Fin r → Fin n)
    (hv : Function.Injective v) (hw : Function.Injective w) (y : Fin ℓ' → Fin n)
    (z : Fin r' → Fin n) :
    δ K ℓ ℓ' r r' n (Fin.append v y) (Fin.append w z) =
      if (y, z) ∈ Y ℓ' r' n v w then (1 : MvPolynomial (Fin n × Fin n) K) else 0 := by
  rw [δ, δ_left_eval K n v y (Fin.append w z) hv, δ_right_eval K n w z (Fin.append v y) hw,
    ite_mul_ite_one_zero]
  have hiff : (Function.Injective (Fin.append v y) ∧ Function.Injective (Fin.append w z)) ↔
      (y, z) ∈ Y ℓ' r' n v w := by rw [mem_Y]
  simp only [hiff]

end Lax461425Proofs.PatternsRestrictedY
