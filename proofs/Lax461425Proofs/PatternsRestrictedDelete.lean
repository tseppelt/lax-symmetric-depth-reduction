import Lax461425Proofs.PatternsRestrictedY
import Mathlib.Data.Fintype.BigOperators

/-!
---
title: Deleting labels by summing over their values (lem:restricted, "delete labels")
type: lemma
---
The structural operation `PatternsLabelledOps.restrict` deletes label *positions* from a graph
`G`, keeping the underlying pattern unchanged. At the level of homomorphism polynomials this
corresponds exactly to *summing* over the deleted positions' label values: the vertex images at
the deleted positions become unconstrained free summation variables. We make this precise
(`labelledHom_restrict_eq_sum`), then lift it from a single generator to the whole span
(`span𝔗P_restrict_sum`), via `Submodule.span_induction`, exactly parallel to how
`span𝔗P_mul_mem` lifted `inClassP_glue`.
-/

open Lax461425.SymmetricFamilies (MatrixPolynomial)

namespace Lax461425Proofs.PatternsRestrictedDelete

open Lax461425.HomomorphismPolynomials Lax461425Proofs.PatternsLabelledBasic
open Lax461425Proofs.PatternsLabelledOps Lax461425Proofs.PatternsRestrictedMono
open scoped Classical

variable {ℓ ℓ' r r' : ℕ}

/-- Splitting a universally quantified statement over `Fin (m + m')` into its `castAdd`/`natAdd`
parts. -/
theorem forall_addCases_iff {m m' : ℕ} (P : Fin (m + m') → Prop) :
    (∀ p, P p) ↔ (∀ i : Fin m, P (Fin.castAdd m' i)) ∧ (∀ j : Fin m', P (Fin.natAdd m j)) := by
  constructor
  · intro h; exact ⟨fun i => h _, fun j => h _⟩
  · rintro ⟨h1, h2⟩ p
    induction p using Fin.addCases with
    | left i => exact h1 i
    | right j => exact h2 j

/-- A generic "4-index sum exchange": summing in the order `a, b, c, d` agrees with summing in
the order `c, d, a, b`. Used to move the two "new label" summation variables past the two
`labelledHom`-defining summations (over vertex images), so they can be collapsed independently of
the "old label" summations. -/
theorem sum4_comm {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (f : α → β → γ → δ → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  have h1 : (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ p : α × β, ∑ q : γ × δ, f p.1 p.2 q.1 q.2 := by
    rw [← Fintype.sum_prod_type']
    congr 1
    ext p
    rw [← Fintype.sum_prod_type']
  have h2 : (∑ c, ∑ d, ∑ a, ∑ b, f a b c d) = ∑ q : γ × δ, ∑ p : α × β, f p.1 p.2 q.1 q.2 := by
    rw [← Fintype.sum_prod_type']
    congr 1
    ext q
    rw [← Fintype.sum_prod_type']
  rw [h1, h2, Finset.sum_comm]

variable (G : LabelledPattern (ℓ + ℓ') (r + r'))

/-- **Deleting labels by summing**: the homomorphism polynomial of `restrict`-ing `G` down to
the first `ℓ, r` label positions equals the sum, over all values of the deleted `ℓ', r'`
positions, of `G`'s own homomorphism polynomial at the extended labelling. -/
theorem labelledHom_restrict_eq_sum (n : ℕ) (K : Type*) [CommSemiring K] (v : Fin ℓ → Fin n)
    (w : Fin r → Fin n) :
    labelledHom K (restrict G (Fin.castAddEmb ℓ') (Fin.castAddEmb r')) n v w =
      ∑ y : Fin ℓ' → Fin n, ∑ z : Fin r' → Fin n,
        labelledHom K G n (Fin.append v y) (Fin.append w z) := by
  set y0 : (G.F.A → Fin n) → Fin ℓ' → Fin n := fun hA j => hA (G.a (Fin.natAdd ℓ j)) with hy0
  set z0 : (G.F.B → Fin n) → Fin r' → Fin n := fun hB j => hB (G.b (Fin.natAdd r j)) with hz0
  set Φ : (G.F.A → Fin n) → (G.F.B → Fin n) → MatrixPolynomial n K :=
    fun hA hB => ∏ x, ∏ y, MvPolynomial.X (hA x, hB y) ^ G.F.mult x y with hΦ
  have hcollapse : ∀ hA hB,
      (∑ y : Fin ℓ' → Fin n, ∑ z : Fin r' → Fin n,
        if (∀ p : Fin (ℓ + ℓ'), hA (G.a p) = Fin.append v y p) ∧
            (∀ q : Fin (r + r'), hB (G.b q) = Fin.append w z q) then Φ hA hB
          else (0 : MatrixPolynomial n K)) =
        if (∀ i : Fin ℓ, hA (G.a (Fin.castAdd ℓ' i)) = v i) ∧
            (∀ j : Fin r, hB (G.b (Fin.castAdd r' j)) = w j) then Φ hA hB else 0 := by
    intro hA hB
    have hcond : ∀ y z, ((∀ p, hA (G.a p) = Fin.append v y p) ∧
        (∀ q, hB (G.b q) = Fin.append w z q)) ↔
        (((∀ i : Fin ℓ, hA (G.a (Fin.castAdd ℓ' i)) = v i) ∧ y0 hA = y) ∧
          ((∀ j : Fin r, hB (G.b (Fin.castAdd r' j)) = w j) ∧ z0 hB = z)) := by
      intro y z
      rw [forall_addCases_iff, forall_addCases_iff]
      simp only [Fin.append_left, Fin.append_right, hy0, hz0, funext_iff]
    simp only [hcond]
    by_cases hA0 : ∀ i : Fin ℓ, hA (G.a (Fin.castAdd ℓ' i)) = v i
    · by_cases hB0 : ∀ j : Fin r, hB (G.b (Fin.castAdd r' j)) = w j
      · rw [if_pos ⟨hA0, hB0⟩]
        rw [Finset.sum_eq_single (y0 hA)]
        · rw [Finset.sum_eq_single (z0 hB)]
          · rw [if_pos ⟨⟨hA0, rfl⟩, ⟨hB0, rfl⟩⟩]
          · intro z _ hne; exact if_neg (fun h => hne h.2.2.symm)
          · intro h; exact absurd (Finset.mem_univ (z0 hB)) h
        · intro y _ hne
          apply Finset.sum_eq_zero
          intro z _
          exact if_neg (fun h => hne h.1.2.symm)
        · intro h; exact absurd (Finset.mem_univ (y0 hA)) h
      · rw [if_neg (fun h : _ ∧ _ => hB0 h.2)]
        apply Finset.sum_eq_zero; intro y _
        apply Finset.sum_eq_zero; intro z _
        exact if_neg (fun h => hB0 h.2.1)
    · rw [if_neg (fun h : _ ∧ _ => hA0 h.1)]
      apply Finset.sum_eq_zero; intro y _
      apply Finset.sum_eq_zero; intro z _
      exact if_neg (fun h => hA0 h.1.1)
  show labelledHom K (restrict G (Fin.castAddEmb ℓ') (Fin.castAddEmb r')) n v w =
      ∑ y : Fin ℓ' → Fin n, ∑ z : Fin r' → Fin n,
        ∑ hA : G.F.A → Fin n, ∑ hB : G.F.B → Fin n,
          if (∀ p, hA (G.a p) = Fin.append v y p) ∧ (∀ q, hB (G.b q) = Fin.append w z q) then
            Φ hA hB else 0
  rw [sum4_comm]
  rw [Finset.sum_congr rfl (fun hA (_ : hA ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun hB (_ : hB ∈ Finset.univ) => hcollapse hA hB))]
  show labelledHom K (restrict G (Fin.castAddEmb ℓ') (Fin.castAddEmb r')) n v w =
      ∑ hA : G.F.A → Fin n, ∑ hB : G.F.B → Fin n,
        if (∀ i : Fin ℓ, hA (G.a (Fin.castAdd ℓ' i)) = v i) ∧
            (∀ j : Fin r, hB (G.b (Fin.castAdd r' j)) = w j) then Φ hA hB else 0
  rfl

/-- For `P = Finset.univ`, the image over the coerced subtype `↥P` agrees with the image over
the whole type: needed since `InClassP`'s support condition quantifies over `↥P`, not over `α`
directly. -/
theorem image_univ_subtype_eq {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) :
    Finset.univ.image (fun p : (Finset.univ : Finset α) => f p.1) = Finset.univ.image f := by
  ext b
  simp

/-- `InClassP Δ k Finset.univ G` is the same as `InClass Δ k G` (restricting to *all* positions
is vacuous), matching the remark in `PatternsLabelledBasic`. -/
theorem inClassP_univ_of_inClass {ℓ r Δ k : ℕ} {G : LabelledPattern ℓ r} (h : InClass Δ k G) :
    InClassP Δ k (Finset.univ : Finset (Fin ℓ ⊕ Fin r)) G :=
  ⟨h, (image_univ_subtype_eq G.labelVertex) ▸ G.labelSupport_subset_image⟩

/-! ### Lifting "delete labels by summing" from a generator to the whole span -/

/-- **`Σ^≠`**: summing a `(ℓ+ℓ',r+r')`-labelled function over *all* values of the last `ℓ', r'`
label positions, producing an `(ℓ,r)`-labelled function. (When multiplied by `δ` first, as in
`lem:restricted`'s proof, the non-`Y(v,w)` terms vanish and this becomes the genuinely
*restricted* sum over `Y(v,w)`; see `PatternsRestrictedSum`.) -/
noncomputable def sumExt (K : Type*) [Field K] (n : ℕ)
    (ψ : (Fin (ℓ + ℓ') → Fin n) → (Fin (r + r') → Fin n) → MatrixPolynomial n K) :
    (Fin ℓ → Fin n) → (Fin r → Fin n) → MatrixPolynomial n K :=
  fun v w => ∑ y : Fin ℓ' → Fin n, ∑ z : Fin r' → Fin n, ψ (Fin.append v y) (Fin.append w z)

/-- **Deleting labels at the span level**: if `ψ ∈ 𝔗^{Δ,k}_{n,P}(ℓ+ℓ',r+r')` for *any* `P`, then
`Σ^≠ ψ ∈ 𝔗^{Δ+1,k}_n(ℓ,r)` (the *unrestricted* class, i.e. with `P` taken to be the full set of
`(ℓ,r)`-positions — always a vacuous restriction, per `LabelledPattern.labelSupport_subset_image`).
Lifted from `labelledHom_restrict_eq_sum` on generators via `Submodule.span_induction`. -/
theorem span𝔗P_restrict_sum (K : Type*) [Field K] (Δ k n : ℕ)
    (P : Finset (Fin (ℓ + ℓ') ⊕ Fin (r + r')))
    (ψ : (Fin (ℓ + ℓ') → Fin n) → (Fin (r + r') → Fin n) → MatrixPolynomial n K)
    (hψ : ψ ∈ span𝔗P K Δ k n P) :
    sumExt K n ψ ∈ span𝔗P K (Δ + 1) k n (Finset.univ : Finset (Fin ℓ ⊕ Fin r)) := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨G, hG, rfl⟩ := hx
      have heq : sumExt K n (labelledHom K G n) =
          labelledHom K (restrict G (Fin.castAddEmb ℓ') (Fin.castAddEmb r')) n := by
        funext v w
        exact (labelledHom_restrict_eq_sum G n K v w).symm
      rw [heq]
      exact Submodule.subset_span ⟨restrict G (Fin.castAddEmb ℓ') (Fin.castAddEmb r'),
        inClassP_univ_of_inClass (inClass_restrict hG.1 _ _), rfl⟩
  | zero =>
      have heq : sumExt K n (0 : (Fin (ℓ + ℓ') → Fin n) → (Fin (r + r') → Fin n) →
          MatrixPolynomial n K) = 0 := by
        funext v w
        show (∑ y : Fin ℓ' → Fin n, ∑ z : Fin r' → Fin n,
          (0 : (Fin (ℓ + ℓ') → Fin n) → (Fin (r + r') → Fin n) →
            MatrixPolynomial n K) (Fin.append v y) (Fin.append w z)) = 0
        simp
      rw [heq]
      exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      have heq : sumExt K n (x + y) = sumExt K n x + sumExt K n y := by
        funext v w
        show (∑ y' : Fin ℓ' → Fin n, ∑ z' : Fin r' → Fin n,
            (x + y) (Fin.append v y') (Fin.append w z')) =
          (∑ y' : Fin ℓ' → Fin n, ∑ z' : Fin r' → Fin n, x (Fin.append v y') (Fin.append w z')) +
            ∑ y' : Fin ℓ' → Fin n, ∑ z' : Fin r' → Fin n, y (Fin.append v y') (Fin.append w z')
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro y' _
        rw [← Finset.sum_add_distrib]
      rw [heq]
      exact Submodule.add_mem _ ihx ihy
  | smul c x _ ih =>
      have heq : sumExt K n (c • x) = c • sumExt K n x := by
        funext v w
        show (∑ y' : Fin ℓ' → Fin n, ∑ z' : Fin r' → Fin n,
            (c • x) (Fin.append v y') (Fin.append w z')) =
          c • ∑ y' : Fin ℓ' → Fin n, ∑ z' : Fin r' → Fin n, x (Fin.append v y') (Fin.append w z')
        simp only [Pi.smul_apply, Finset.smul_sum]
      rw [heq]
      exact Submodule.smul_mem _ c ih

end Lax461425Proofs.PatternsRestrictedDelete
