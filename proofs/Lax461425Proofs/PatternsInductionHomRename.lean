import Mathlib.Algebra.MvPolynomial.Rename
import Lax461425.MatrixSymmetry
import Lax461425Proofs.PatternsLabelledBasic

/-!
A general **equivariance fact about `labelledHom`**: relabelling the images of a labelled
graph's homomorphism polynomial along `γ : Γ n` (postcomposing the label images `v, w` with
`γ.1, γ.2`) is the same as renaming the variables of the polynomial along `actVar γ`. This is
the key algebraic fact (not previously available anywhere in this development) underlying the
paper's claim `p_{h_y} = φ_h(vec{sup}(h)[N ↦ y])` in `lem:induction`'s internal-gate case: once
`h_y = γ_y • h` for some `γ_y` mapping the real support-complement tuple to `y`, this lemma lets
`p_{h_y} = rename (actVar γ_y) p_h` (from `PatternsInductionEquivariant`) be rewritten, via the
induction hypothesis `p_h = φ_h(leftEnum h, rightEnum h)`, as a direct evaluation of (a sum of
copies of) `φ_h` at the relabelled tuple, with no reference to `h_y` as a gate at all.
-/

namespace Lax461425Proofs.PatternsInductionHomRename

open Lax461425.MatrixSymmetry
open Lax461425Proofs.PatternsLabelledBasic

variable {n : ℕ}

/-- Postcomposition with a permutation `γ1` is a bijection of `A → Fin n` with itself. -/
def postComp (γ1 : Equiv.Perm (Fin n)) (A : Type*) : (A → Fin n) ≃ (A → Fin n) where
  toFun f := γ1 ∘ f
  invFun f := γ1.symm ∘ f
  left_inv f := by funext a; simp
  right_inv f := by funext a; simp

theorem postComp_apply {γ1 : Equiv.Perm (Fin n)} {A : Type*} (f : A → Fin n) :
    postComp γ1 A f = γ1 ∘ f := rfl

/-- **`labelledHom` is equivariant under `Γ n`, via `MvPolynomial.rename`.** -/
theorem labelledHom_rename {ℓ r : ℕ} (K : Type*) [CommSemiring K] (G : LabelledPattern ℓ r)
    (γ : Γ n) (v : Fin ℓ → Fin n) (w : Fin r → Fin n) :
    MvPolynomial.rename (actVar γ) (labelledHom K G n v w) =
      labelledHom K G n (γ.1 ∘ v) (γ.2 ∘ w) := by
  set eA := postComp γ.1 G.F.A with heA
  set eB := postComp γ.2 G.F.B with heB
  unfold labelledHom
  rw [map_sum]
  refine Fintype.sum_equiv eA _ _ (fun hA => ?_)
  rw [map_sum]
  refine Fintype.sum_equiv eB _ _ (fun hB => ?_)
  have hcondeq : ((∀ i, hA (G.a i) = v i) ∧ (∀ j, hB (G.b j) = w j)) ↔
      ((∀ i, (eA hA) (G.a i) = (γ.1 ∘ v) i) ∧ (∀ j, (eB hB) (G.b j) = (γ.2 ∘ w) j)) := by
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun j => ?_⟩
      · rw [postComp_apply]; show γ.1 (hA (G.a i)) = γ.1 (v i); rw [h1 i]
      · rw [postComp_apply]; show γ.2 (hB (G.b j)) = γ.2 (w j); rw [h2 j]
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => γ.1.injective ?_, fun j => γ.2.injective ?_⟩
      · have := h1 i; rwa [postComp_apply] at this
      · have := h2 j; rwa [postComp_apply] at this
  rw [apply_ite (MvPolynomial.rename (actVar γ)), map_zero]
  by_cases hc : (∀ i, hA (G.a i) = v i) ∧ ∀ j, hB (G.b j) = w j
  · have hc' := hcondeq.mp hc
    rw [if_pos hc, if_pos hc', map_prod]
    refine Finset.prod_congr rfl (fun x _ => ?_)
    rw [map_prod]
    refine Finset.prod_congr rfl (fun y _ => ?_)
    rw [map_pow, MvPolynomial.rename_X]
    congr 1
  · have hc' : ¬ ((∀ i, (eA hA) (G.a i) = (γ.1 ∘ v) i) ∧ ∀ j, (eB hB) (G.b j) = (γ.2 ∘ w) j) :=
      fun h => hc (hcondeq.mpr h)
    rw [if_neg hc, if_neg hc']

end Lax461425Proofs.PatternsInductionHomRename
