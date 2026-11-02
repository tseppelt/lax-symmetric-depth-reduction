import Lax461425Proofs.PatternsRestrictedY
import Mathlib.Data.Fintype.CardEmbedding

/-!
---
title: |Y(v,w)| depends only on n, ℓ, ℓ', r, r' (lem:restricted, ψ_Π preliminary)
type: lemma
---
A preliminary fact needed to define `ψ_Π` as a *single* function, uniformly over all injective
`v, w`: the cardinality of `Y ℓ' r' n v w` does not depend on the particular injective `v, w`
chosen, only on `n, ℓ, ℓ', r, r'`. We give the closed form
`cardY n ℓ ℓ' r r' = (n - ℓ).descFactorial ℓ' * (n - r).descFactorial r'`
and show `(Y ℓ' r' n v w).card = cardY n ℓ ℓ' r r'` for every injective `v, w`
(`card_Y_eq`); independence across different choices of injective `v, w` is then an immediate
corollary (`card_Y_eq_card_Y`).

The proof: given `v` injective, `Y ℓ' r' n v w` splits (by `Fin.append_injective_iff`) as a
product of a "left" and a "right" condition, each counting injective functions into `Fin n`
whose range avoids the (fixed-cardinality) range of `v` resp. `w`. Such functions are in
bijection with embeddings into the complement of that range (`avoidEquiv`), whose cardinality is
computed by `Fintype.card_embedding_eq` together with `Fintype.card_compl_set` and
`Set.card_range_of_injective`.
-/

namespace Lax461425Proofs.PatternsRestrictedCard

open Lax461425Proofs.PatternsRestrictedY
open scoped Classical

variable {ℓ ℓ' r r' : ℕ}

/-! ### Counting injective functions avoiding a fixed range -/

/-- The subtype of functions `Fin ℓ' → Fin n` that are injective and whose range avoids that of
`v`, in bijection with embeddings `Fin ℓ' ↪ {x // x ∉ Set.range v}`. -/
noncomputable def avoidEquiv {n : ℕ} (v : Fin ℓ → Fin n) :
    {y : Fin ℓ' → Fin n // Function.Injective y ∧ ∀ i j, v i ≠ y j} ≃
      (Fin ℓ' ↪ {x : Fin n // x ∉ Set.range v}) where
  toFun y := ⟨fun j => ⟨y.1 j, by
      intro hmem
      obtain ⟨i, hi⟩ := hmem
      exact y.2.2 i j hi⟩,
    fun j1 j2 h => y.2.1 (congrArg Subtype.val h)⟩
  invFun f := ⟨fun j => (f j).1,
    fun j1 j2 h => f.injective (Subtype.ext h),
    fun i j hij => (f j).2 (by
      have hmem : v i ∈ Set.range v := Set.mem_range_self i
      rwa [hij] at hmem)⟩
  left_inv y := rfl
  right_inv f := Function.Embedding.ext (fun j => rfl)

/-- The cardinality of injective functions `Fin ℓ' → Fin n` avoiding the range of an injective
`v : Fin ℓ → Fin n` is `(n - ℓ).descFactorial ℓ'`, independent of the particular `v` beyond its
domain size `ℓ`. -/
theorem card_avoid_eq {n : ℕ} (v : Fin ℓ → Fin n) (hv : Function.Injective v) :
    Fintype.card {y : Fin ℓ' → Fin n // Function.Injective y ∧ ∀ i j, v i ≠ y j} =
      (n - ℓ).descFactorial ℓ' := by
  rw [Fintype.card_congr (avoidEquiv v), Fintype.card_embedding_eq, Fintype.card_fin]
  have hcompl : Fintype.card {x : Fin n // x ∉ Set.range v} =
      Fintype.card (Fin n) - Fintype.card (Set.range v) :=
    Fintype.card_compl_set (Set.range v)
  rw [hcompl, Fintype.card_fin, Set.card_range_of_injective hv, Fintype.card_fin]

/-! ### The product decomposition of `Y ℓ' r' n v w` -/

/-- Given `v, w` injective, `Y ℓ' r' n v w` is the Finset product of the "avoid `v`" and "avoid
`w`" Finsets. -/
theorem Y_eq_product {n : ℕ} (v : Fin ℓ → Fin n) (w : Fin r → Fin n) (hv : Function.Injective v)
    (hw : Function.Injective w) :
    Y ℓ' r' n v w =
      (Finset.univ.filter
          (fun y : Fin ℓ' → Fin n => Function.Injective y ∧ ∀ i j, v i ≠ y j)) ×ˢ
        (Finset.univ.filter
          (fun z : Fin r' → Fin n => Function.Injective z ∧ ∀ i j, w i ≠ z j)) := by
  ext ⟨y, z⟩
  simp only [mem_Y, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.append_injective_iff, hv, hw, true_and]

/-- **`|Y(v,w)|` depends only on `n, ℓ, ℓ', r, r'`**: the closed form. -/
noncomputable def cardY (n ℓ ℓ' r r' : ℕ) : ℕ :=
  (n - ℓ).descFactorial ℓ' * (n - r).descFactorial r'

/-- **The cardinality formula for `Y(v,w)`**, for any injective `v, w`. -/
theorem card_Y_eq {n : ℕ} (v : Fin ℓ → Fin n) (w : Fin r → Fin n) (hv : Function.Injective v)
    (hw : Function.Injective w) :
    (Y ℓ' r' n v w).card = cardY n ℓ ℓ' r r' := by
  rw [Y_eq_product v w hv hw, Finset.card_product, cardY]
  have h1 : (Finset.univ.filter
      (fun y : Fin ℓ' → Fin n => Function.Injective y ∧ ∀ i j, v i ≠ y j)).card =
      (n - ℓ).descFactorial ℓ' := by
    rw [← card_avoid_eq v hv]
    exact (Fintype.card_of_subtype _ (fun y => by simp)).symm
  have h2 : (Finset.univ.filter
      (fun z : Fin r' → Fin n => Function.Injective z ∧ ∀ i j, w i ≠ z j)).card =
      (n - r).descFactorial r' := by
    rw [← card_avoid_eq w hw]
    exact (Fintype.card_of_subtype _ (fun z => by simp)).symm
  rw [h1, h2]

end Lax461425Proofs.PatternsRestrictedCard
