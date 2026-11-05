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

open Lax461425.SymmetricFamilies (MatrixPolynomial)

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
    (v : Fin L → Fin n) (w : Fin R → Fin n) : MatrixPolynomial n K :=
  labelledHom K (J L R) n v w - labelledHom K (mergeA L R p q hpq) n v w

/-- `J_n - D^{p,q}_n` on the `B`-side (right positions `p ≠ q` of `R`). -/
noncomputable def factorB (K : Type*) [Field K] (L R n : ℕ) (p q : Fin R) (hpq : p ≠ q)
    (v : Fin L → Fin n) (w : Fin R → Fin n) : MatrixPolynomial n K :=
  labelledHom K (J L R) n v w - labelledHom K (mergeB L R p q hpq) n v w

theorem factorA_eval (K : Type*) [Field K] (L R n : ℕ) (p q : Fin L) (hpq : p ≠ q)
    (v : Fin L → Fin n) (w : Fin R → Fin n) :
    factorA K L R n p q hpq v w = if v p = v q then (0 : MatrixPolynomial n K) else 1 := by
  rw [factorA, labelledHom_J, labelledHom_mergeA]
  by_cases h : v p = v q <;> simp [h]

theorem factorB_eval (K : Type*) [Field K] (L R n : ℕ) (p q : Fin R) (hpq : p ≠ q)
    (v : Fin L → Fin n) (w : Fin R → Fin n) :
    factorB K L R n p q hpq v w = if w p = w q then (0 : MatrixPolynomial n K) else 1 := by
  rw [factorB, labelledHom_J, labelledHom_mergeB]
  by_cases h : w p = w q <;> simp [h]

/-! ### The all-distinct indicator `δ` -/

/-- **`δ`**: the pointwise product, over all pairs of distinct label positions on the same side
with at least one among the last `ℓ'` left or `r'` right positions, of `J_n - D^{i,j}_n`. -/
noncomputable def δ (K : Type*) [Field K] (ℓ ℓ' r r' : ℕ) (n : ℕ) :
    (Fin (ℓ + ℓ') → Fin n) → (Fin (r + r') → Fin n) → MatrixPolynomial n K :=
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

/-- Generic side-independent core: a family `f` of factors, equal to the `0`/`1` indicator of
`g p ≠ g q` for `g = Fin.append u y`, has (cross + new-new) product equal to the indicator of
injectivity of `g`. Used for both the left and the right side. -/
theorem prod_pairs_eval {S : Type*} [CommRing S] {m m' n : ℕ} (u : Fin m → Fin n)
    (y : Fin m' → Fin n) (hu : Function.Injective u)
    (f : ∀ p q : Fin (m + m'), p ≠ q → S)
    (hf : ∀ p q hpq, f p q hpq = if Fin.append u y p = Fin.append u y q then 0 else 1) :
    (∏ p : Fin m × Fin m', f (Fin.castAdd m' p.1) (Fin.natAdd m p.2)
        (castAdd_ne_natAdd m m' p.1 p.2)) *
      (∏ p ∈ (newPairs m').attach, f (Fin.natAdd m p.1.1) (Fin.natAdd m p.1.2)
        (natAdd_ne_natAdd_of_ne (ne_of_lt (mem_newPairs.mp p.2)))) =
      if Function.Injective (Fin.append u y) then (1 : S) else 0 := by
  have h1 : (∏ p : Fin m × Fin m', f (Fin.castAdd m' p.1) (Fin.natAdd m p.2)
        (castAdd_ne_natAdd m m' p.1 p.2)) =
      if (∀ i : Fin m, ∀ j : Fin m', u i ≠ y j) then (1 : S) else 0 := by
    have heq : ∀ p : Fin m × Fin m', f (Fin.castAdd m' p.1) (Fin.natAdd m p.2)
        (castAdd_ne_natAdd m m' p.1 p.2) = if u p.1 = y p.2 then (0 : S) else 1 := by
      intro p
      rw [hf, Fin.append_left, Fin.append_right]
    rw [Finset.prod_congr rfl (fun p _ => heq p)]
    rw [prod_ite_zero_one]
    have hiff : (∀ i ∈ (Finset.univ : Finset (Fin m × Fin m')), ¬ u i.1 = y i.2) ↔
        (∀ i : Fin m, ∀ j : Fin m', u i ≠ y j) :=
      ⟨fun h i j => h ⟨i, j⟩ (Finset.mem_univ _), fun h p _ => h p.1 p.2⟩
    simp only [hiff]
  have h2 : (∏ p ∈ (newPairs m').attach, f (Fin.natAdd m p.1.1) (Fin.natAdd m p.1.2)
        (natAdd_ne_natAdd_of_ne (ne_of_lt (mem_newPairs.mp p.2)))) =
      if Function.Injective y then (1 : S) else 0 := by
    have heq : ∀ p : (newPairs m'), f (Fin.natAdd m p.1.1) (Fin.natAdd m p.1.2)
        (natAdd_ne_natAdd_of_ne (ne_of_lt (mem_newPairs.mp p.2))) =
        if y p.1.1 = y p.1.2 then (0 : S) else 1 := by
      intro p
      rw [hf, Fin.append_right, Fin.append_right]
    rw [Finset.prod_congr rfl (fun p _ => heq p)]
    rw [Finset.prod_attach (newPairs m')
      (fun p => if y p.1 = y p.2 then (0 : S) else 1)]
    rw [prod_ite_zero_one]
    have hiff : (∀ p ∈ newPairs m', ¬ y p.1 = y p.2) ↔ Function.Injective y := by
      rw [injective_iff_forall_lt_ne]
      exact ⟨fun h i j hij => h (i, j) (mem_newPairs.mpr hij), fun h p hp => h p.1 p.2
        (mem_newPairs.mp hp)⟩
    simp only [hiff]
  rw [h1, h2, ite_mul_ite_one_zero]
  have hiff : ((∀ i : Fin m, ∀ j : Fin m', u i ≠ y j) ∧ Function.Injective y) ↔
      Function.Injective (Fin.append u y) := by
    rw [Fin.append_injective_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hu, h2, h1⟩
    · rintro ⟨-, h2, h1⟩
      exact ⟨h1, h2⟩
  simp only [hiff]

/-- The left-side pair of factors (cross + new-new) collapses to the indicator of injectivity
of the extended left labelling. -/
theorem δ_left_eval (K : Type*) [Field K] (n : ℕ) (v : Fin ℓ → Fin n) (y : Fin ℓ' → Fin n)
    (w : Fin (r + r') → Fin n) (hv : Function.Injective v) :
    (∏ p : Fin ℓ × Fin ℓ', factorA K (ℓ + ℓ') (r + r') n (Fin.castAdd ℓ' p.1) (Fin.natAdd ℓ p.2)
        (castAdd_ne_natAdd ℓ ℓ' p.1 p.2) (Fin.append v y) w) *
      (∏ p ∈ (newPairs ℓ').attach, factorA K (ℓ + ℓ') (r + r') n
        (Fin.natAdd ℓ p.1.1) (Fin.natAdd ℓ p.1.2)
        (natAdd_ne_natAdd_of_ne (ne_of_lt (mem_newPairs.mp p.2))) (Fin.append v y) w) =
      if Function.Injective (Fin.append v y) then (1 : MatrixPolynomial n K) else 0 :=
  prod_pairs_eval v y hv
    (fun p q hpq => factorA K (ℓ + ℓ') (r + r') n p q hpq (Fin.append v y) w)
    (fun _ _ _ => factorA_eval ..)

/-- The right-side pair of factors (cross + new-new) collapses to the indicator of injectivity
of the extended right labelling. -/
theorem δ_right_eval (K : Type*) [Field K] (n : ℕ) (w : Fin r → Fin n) (z : Fin r' → Fin n)
    (v : Fin (ℓ + ℓ') → Fin n) (hw : Function.Injective w) :
    (∏ p : Fin r × Fin r', factorB K (ℓ + ℓ') (r + r') n (Fin.castAdd r' p.1) (Fin.natAdd r p.2)
        (castAdd_ne_natAdd r r' p.1 p.2) v (Fin.append w z)) *
      (∏ p ∈ (newPairs r').attach, factorB K (ℓ + ℓ') (r + r') n
        (Fin.natAdd r p.1.1) (Fin.natAdd r p.1.2)
        (natAdd_ne_natAdd_of_ne (ne_of_lt (mem_newPairs.mp p.2))) v (Fin.append w z)) =
      if Function.Injective (Fin.append w z) then (1 : MatrixPolynomial n K) else 0 :=
  prod_pairs_eval w z hw
    (fun p q hpq => factorB K (ℓ + ℓ') (r + r') n p q hpq v (Fin.append w z))
    (fun _ _ _ => factorB_eval ..)

/-- **`δ`'s evaluation**: given `v, w` injective, `δ` at `(Fin.append v y, Fin.append w z)` is
the `0`/`1` indicator of `(y, z) ∈ Y ℓ' r' n v w`. -/
theorem δ_eval (K : Type*) [Field K] (n : ℕ) (v : Fin ℓ → Fin n) (w : Fin r → Fin n)
    (hv : Function.Injective v) (hw : Function.Injective w) (y : Fin ℓ' → Fin n)
    (z : Fin r' → Fin n) :
    δ K ℓ ℓ' r r' n (Fin.append v y) (Fin.append w z) =
      if (y, z) ∈ Y ℓ' r' n v w then (1 : MatrixPolynomial n K) else 0 := by
  rw [δ, δ_left_eval K n v y (Fin.append w z) hv, δ_right_eval K n w z (Fin.append v y) hw,
    ite_mul_ite_one_zero]
  have hiff : (Function.Injective (Fin.append v y) ∧ Function.Injective (Fin.append w z)) ↔
      (y, z) ∈ Y ℓ' r' n v w := by rw [mem_Y]
  simp only [hiff]

/-! ### `δ` lies in the span, for every `Δ`, `k`, `P` with `P.card ≤ k` -/

/-- A pointwise product over an arbitrary finite index set of elements of `span𝔗P K Δ k n P`
(all for the same `Δ, k, P`) again lies in `span𝔗P K Δ k n P`. -/
theorem span𝔗P_prod_mem {ℓ r : ℕ} {K : Type*} [Field K] {Δ k n : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)}
    (hP : P.card ≤ k) {ι : Type*} (s : Finset ι)
    (f : ι → (Fin ℓ → Fin n) → (Fin r → Fin n) → MatrixPolynomial n K)
    (hf : ∀ i ∈ s, f i ∈ span𝔗P K Δ k n P) :
    (fun v w => ∏ i ∈ s, f i v w) ∈ span𝔗P K Δ k n P := by
  classical
  induction s using Finset.induction with
  | empty => simpa using one_mem_span𝔗P K Δ k n P
  | insert a s ha ih =>
      have heq : (fun v w => ∏ i ∈ insert a s, f i v w) =
          fun v w => f a v w * ∏ i ∈ s, f i v w := by
        funext v w; rw [Finset.prod_insert ha]
      rw [heq]
      exact span𝔗P_mul_mem hP (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- `J - H` lies in the span for any edgeless `H` (the shared core of `factorA`/`factorB`). -/
theorem J_sub_mem_span (K : Type*) [Field K] (Δ k n L R : ℕ) (H : LabelledPattern L R)
    (hH : isEdgeless H.F) (P : Finset (Fin L ⊕ Fin R)) :
    (fun v w => labelledHom K (J L R) n v w - labelledHom K H n v w) ∈ span𝔗P K Δ k n P :=
  Submodule.sub_mem _
    (Submodule.subset_span ⟨J L R, inClassP_of_edgeless' (J_isEdgeless L R) Δ k P, rfl⟩)
    (Submodule.subset_span ⟨H, inClassP_of_edgeless' hH Δ k P, rfl⟩)

theorem factorA_mem_span (K : Type*) [Field K] (Δ k n L R : ℕ) (p q : Fin L) (hpq : p ≠ q)
    (P : Finset (Fin L ⊕ Fin R)) : factorA K L R n p q hpq ∈ span𝔗P K Δ k n P :=
  J_sub_mem_span K Δ k n L R _ (mergeA_isEdgeless L R p q hpq) P

theorem factorB_mem_span (K : Type*) [Field K] (Δ k n L R : ℕ) (p q : Fin R) (hpq : p ≠ q)
    (P : Finset (Fin L ⊕ Fin R)) : factorB K L R n p q hpq ∈ span𝔗P K Δ k n P :=
  J_sub_mem_span K Δ k n L R _ (mergeB_isEdgeless L R p q hpq) P

/-- **`δ` lies in `𝔗^{Δ,k}_{n,P}(ℓ+ℓ',r+r')`**, for *every* `Δ`, and every `k, P` with
`P.card ≤ k`: each factor is edgeless (so lies in the span for any `Δ, k, P` at all by item 1 of
`lem:labelled-ops`), and the span is closed under pointwise products (`span𝔗P_mul_mem`). -/
theorem δ_mem_span (K : Type*) [Field K] (Δ k n : ℕ) (P : Finset (Fin (ℓ + ℓ') ⊕ Fin (r + r')))
    (hP : P.card ≤ k) : δ K ℓ ℓ' r r' n ∈ span𝔗P K Δ k n P := by
  unfold δ
  refine span𝔗P_mul_mem hP (span𝔗P_mul_mem hP ?_ ?_) (span𝔗P_mul_mem hP ?_ ?_)
  · exact span𝔗P_prod_mem hP _ _ (fun p _ => factorA_mem_span K Δ k n _ _ _ _ _ P)
  · exact span𝔗P_prod_mem hP _ _ (fun p _ => factorA_mem_span K Δ k n _ _ _ _ _ P)
  · exact span𝔗P_prod_mem hP _ _ (fun p _ => factorB_mem_span K Δ k n _ _ _ _ _ P)
  · exact span𝔗P_prod_mem hP _ _ (fun p _ => factorB_mem_span K Δ k n _ _ _ _ _ P)

end Lax461425Proofs.PatternsRestrictedY
