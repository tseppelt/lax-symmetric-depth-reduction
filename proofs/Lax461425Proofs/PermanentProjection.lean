import Lax461425Proofs.PermanentBasic
import Lax461425Proofs.PermanentBouquet
import Lax461425Proofs.PermanentPresentation
import Lax461425Proofs.PermanentMembership
import Lax461425Proofs.BooleanWitnesses

/-!
Equivariance of the bouquet matrix, followed by averaging over the finite variable group.
The source order is unrestricted, as in Definition 7.6.
-/

namespace Lax461425Proofs.PermanentProjection

open Lax461425.Permanent PermanentBouquet
open scoped BigOperators Classical

variable {B H R : Type*} [Fintype B] [DecidableEq B] [Group H] [CommSemiring R]

/-- Left multiplication permutes separate copies of the same monomial cycle. -/
def vertexPerm {d : B → ℕ} (δ : H) :
    Equiv.Perm (Vertex (B × H) (fun b => d b.1)) :=
  Equiv.optionCongr (Equiv.sigmaCongr
    (Equiv.prodCongr (Equiv.refl B) (Equiv.mulLeft δ)) (fun _ => Equiv.refl _))

lemma advance_vertexPerm {d : B → ℕ} (δ : H) (b : B) (γ : H)
    (j : Fin (d b + 1)) :
    vertexPerm δ (advance (d := fun b => d b.1) (b, γ) j) =
      advance (b, δ * γ) j := by
  unfold advance
  split_ifs <;> rfl

/-- Group multiplication preserves the coefficient edge, variable edges, and loops. -/
theorem matrix_equivariant {S : Type*} [CommSemiring S] {d : B → ℕ}
    (δ : H) (φ : R →+* S)
    (c : B × H → R) (a : ∀ b : B × H, Fin (d b.1 + 1) → R)
    (c' : B × H → S) (a' : ∀ b : B × H, Fin (d b.1 + 1) → S)
    (hc : ∀ b γ, c' (b, δ * γ) = φ (c (b, γ)))
    (ha : ∀ b γ j, a' (b, δ * γ) j = φ (a (b, γ) j))
    (u v : Vertex (B × H) (fun b => d b.1)) :
    matrix c' a' (vertexPerm δ u) (vertexPerm δ v) = φ (matrix c a u v) := by
  cases v with
  | none =>
    cases u with
    | none => simp [matrix, vertexPerm]
    | some u =>
      rcases u with ⟨⟨b, γ⟩, j⟩
      change (if j = 0 then c' (b, δ * γ) else 0) = φ (if j = 0 then c (b, γ) else 0)
      split_ifs <;> simp_all
  | some v =>
    rcases v with ⟨⟨b, γ⟩, j⟩
    change (if vertexPerm δ u = some ⟨(b, δ * γ), j⟩ then 1
      else if vertexPerm δ u = advance (b, δ * γ) j then a' (b, δ * γ) j else 0) = _
    rw [← advance_vertexPerm δ b γ j]
    have hself : some ⟨(b, δ * γ), j⟩ = vertexPerm δ (some ⟨(b, γ), j⟩) := rfl
    rw [hself]
    simp only [Equiv.apply_eq_iff_eq]
    by_cases h₁ : u = some ⟨(b, γ), j⟩
    · simp [h₁, matrix]
    · by_cases h₂ : u = advance (b, γ) j
      · rw [h₂] at h₁ ⊢
        simpa only [matrix, if_neg h₁, if_pos rfl, ↓reduceIte] using ha b γ j
      · simp [h₁, h₂, matrix]

lemma matrix_affine {V K : Type*} [CommSemiring K] {d : B → ℕ}
    (c : B → MvPolynomial V K) (a : ∀ b, Fin (d b + 1) → MvPolynomial V K)
    (hc : ∀ b, IsAffine (c b)) (ha : ∀ b j, IsAffine (a b j))
    (u v : Vertex B d) : IsAffine (matrix c a u v) := by
  cases v with
  | none =>
    cases u with
    | none => simpa [matrix] using (Permanent.isAffine_C (V := V) (0 : K))
    | some u =>
      rcases u with ⟨b, j⟩
      simp only [matrix]
      split_ifs
      · exact hc b
      · simpa using (Permanent.isAffine_C (V := V) (0 : K))
  | some v =>
    rcases v with ⟨b, j⟩
    simp only [matrix]
    split_ifs
    · simpa using (Permanent.isAffine_C (V := V) (1 : K))
    · exact ha b j
    · simpa using (Permanent.isAffine_C (V := V) (0 : K))

set_option backward.isDefEq.respectTransparency false in
/-- Every invariant polynomial for a finite variable group is a symmetric projection of
some permanent. This asserts equivariance only, with no bound on the source order. -/
theorem invariant_projection {V G : Type} {K : Type*} [Group G] [Fintype G] [Field K] [CharZero K]
    (ρ : G →* Equiv.Perm V) (p : MvPolynomial V K)
    (hinv : ∀ γ, MvPolynomial.rename (ρ γ) p = p) : IsSymmetricProjection ρ p := by
  obtain ⟨B, hB, hdB, d, c, z, hp⟩ := PermanentPresentation.exists_presentation p
  letI := hB
  letI := hdB
  let D : B × G → ℕ := fun b => d b.1
  let c' : B × G → MvPolynomial V K :=
    fun b => MvPolynomial.C (c b.1 * (Fintype.card G : K)⁻¹)
  let a' (b : B × G) : Fin (d b.1 + 1) → MvPolynomial V K :=
    Fin.lastCases 1 (fun j => MvPolynomial.X (ρ b.2 (z b.1 j)))
  have hword (b : B) (γ : G) : (∏ j, a' (b, γ) j) =
      ∏ j, MvPolynomial.X (ρ γ (z b j)) := by
    rw [Fin.prod_univ_castSucc]
    simp [a']
  let M := matrix (d := D) c' a'
  refine ⟨Vertex (B × G) D, inferInstance, inferInstance, inferInstance, M, ?_, ?_, ?_⟩
  · symm
    have hsum (γ : G) :
        (∑ b : B, c' (b, γ) * ∏ j, a' (b, γ) j) =
          MvPolynomial.C ((Fintype.card G : K)⁻¹) * MvPolynomial.rename (ρ γ) p := by
      simp_rw [hword]
      rw [hp]
      simp only [map_sum, map_mul, MvPolynomial.rename_C, map_prod, MvPolynomial.rename_X,
        c', MvPolynomial.C_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    have hG : (Fintype.card G : K) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
    have hcancel : (Fintype.card G : MvPolynomial V K) *
        MvPolynomial.C ((Fintype.card G : K)⁻¹) = 1 := by
      simpa only [map_mul, map_one, map_natCast] using
        congrArg (MvPolynomial.C (σ := V)) (mul_inv_cancel₀ hG)
    change Matrix.permanent (matrix (d := D) c' a') = p
    rw [permanent_matrix, Fintype.sum_prod_type, Finset.sum_comm]
    change (∑ γ : G, ∑ b : B, c' (b, γ) * ∏ j, a' (b, γ) j) = p
    simp_rw [hsum, hinv]
    rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, Finset.card_univ, hcancel, one_mul]
  · apply matrix_affine
    · intro b
      exact Permanent.isAffine_C _
    · rintro ⟨b, γ⟩ j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa [a', D] using (Permanent.isAffine_C (V := V) (1 : K))
      · simpa [a', D] using (Permanent.isAffine_X (K := K) (ρ γ (z b j)))
  · intro δ
    refine ⟨vertexPerm (d := d) δ, vertexPerm (d := d) δ, ?_⟩
    apply matrix_equivariant δ (MvPolynomial.rename (ρ δ)).toRingHom c' a' c' a'
    · intro b γ
      simp [c']
    · intro b γ j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [a', map_mul]

/--
---
conclusion: Lax461425.PermanentCompleteness.hardness
---
The hardness direction of Theorem 7.7, with unrestricted source order as in Definition 7.6.
-/
theorem hardness {K : Type u_1} [Field K] [CharZero K] :
    ∀ f : Lax461425.SymmetricFamilies.MatrixFamily K,
      Lax461425.SymmetricVNP.InSymVNP f → ∀ n,
        IsSymmetricProjection (Lax461425.SymmetricVNP.matrixAction n) (f n) := by
  intro f hf n
  exact invariant_projection (Lax461425.SymmetricVNP.matrixAction n) (f n)
    (Lax461425.BooleanSumSymmetry.matrixInvariant_of_mem f hf n)

/-- Theorem 7.7: membership and hardness together give completeness. -/
theorem completeness (K : Type*) [Field K] [CharZero K] :
    Lax461425.SymmetricVNP.InSymVNP (permanent K) ∧
      ∀ f : Lax461425.SymmetricFamilies.MatrixFamily K,
        Lax461425.SymmetricVNP.InSymVNP f → ∀ n,
          IsSymmetricProjection (Lax461425.SymmetricVNP.matrixAction n) (f n) :=
  ⟨Lax461425.PermanentCompleteness.membership, hardness⟩

end Lax461425Proofs.PermanentProjection
