import Lax461425.PatternPadding
import Lax461425.HomomorphismSpanning
import Lax461425Proofs.PatternsInductionReindex
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic

/-!
Prove the paper's isolated-vertex identity internally, absorb its nonzero scalar, and
reindex all patterns onto `Fin n ⊎ Fin n`. The counting argument follows Tim's existing
isolated-vertex proof. No cited external assumption is used.
-/

namespace Lax461425Proofs.Section7Padding

open Lax461425.PatternPadding Lax461425.HomomorphismPolynomials
open Lax461425.SymmetricFamilies
open scoped Classical BigOperators

set_option backward.isDefEq.respectTransparency false in
/-- The paper's `obs:no-isolated-vertices`, iterated on both parts. As in Tim's
`hom_eq_pow_mul_hom_Fiso`, split the independent assignments to isolated vertices
and factor out their number. This is an internal helper, not a concept declaration. -/
theorem hom_padPattern {K : Type*} [CommSemiring K] (F : Pattern) (n : ℕ) :
    hom K (padPattern F n) n =
      MvPolynomial.C ((n : K) ^ ((n - Fintype.card F.A) + (n - Fintype.card F.B))) * hom K F n := by
  unfold hom
  change (∑ hA : F.A ⊕ Fin (n - Fintype.card F.A) → Fin n,
    ∑ hB : F.B ⊕ Fin (n - Fintype.card F.B) → Fin n,
      ∏ a : F.A ⊕ Fin (n - Fintype.card F.A),
        ∏ b : F.B ⊕ Fin (n - Fintype.card F.B),
          MvPolynomial.X (hA a, hB b) ^ (padPattern F n).mult a b) = _
  rw [PatternsInductionReindex.sum_sumArrow]
  simp_rw [PatternsInductionReindex.sum_sumArrow]
  simp only [Fintype.prod_sum_type, padPattern, Sum.elim_inl, Sum.elim_inr,
    pow_zero, Finset.prod_const_one, mul_one, one_mul]
  let w := fun (a : F.A → Fin n) (b : F.B → Fin n) =>
    ∏ x : F.A, ∏ y : F.B,
      (MvPolynomial.X (a x, b y) : MvPolynomial (Fin n × Fin n) K) ^ F.mult x y
  have hconst : ∀ (a : F.A → Fin n) (b : F.B → Fin n),
      (∑ _a : Fin (n - Fintype.card F.A) → Fin n,
        ∑ _b : Fin (n - Fintype.card F.B) → Fin n, w a b) =
      MvPolynomial.C ((n : K) ^ ((n - Fintype.card F.A) + (n - Fintype.card F.B))) * w a b := by
    intro a b
    simp [Fintype.card_fun, nsmul_eq_mul, map_pow, map_natCast, pow_add, mul_assoc]
  change (∑ a : F.A → Fin n, ∑ _a : Fin (n - Fintype.card F.A) → Fin n,
    ∑ b : F.B → Fin n, ∑ _b : Fin (n - Fintype.card F.B) → Fin n, w a b) = _
  calc
    _ = ∑ a : F.A → Fin n, ∑ b : F.B → Fin n,
        ∑ _a : Fin (n - Fintype.card F.A) → Fin n,
          ∑ _b : Fin (n - Fintype.card F.B) → Fin n, w a b :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := by simp only [hconst, Finset.mul_sum]; rfl

lemma card_pad_left (F : Pattern) (n : ℕ) (h : Fintype.card F.A ≤ n) :
    Fintype.card (padPattern F n).A = n := by
  change Fintype.card (F.A ⊕ Fin (n - Fintype.card F.A)) = n
  rw [Fintype.card_sum, Fintype.card_fin]
  omega

lemma card_pad_right (F : Pattern) (n : ℕ) (h : Fintype.card F.B ≤ n) :
    Fintype.card (padPattern F n).B = n := by
  change Fintype.card (F.B ⊕ Fin (n - Fintype.card F.B)) = n
  rw [Fintype.card_sum, Fintype.card_fin]
  omega

set_option backward.isDefEq.respectTransparency false in
/-- Isomorphic reindexing of the two pattern parts preserves the homomorphism polynomial. -/
theorem hom_square_reindex {K : Type*} [CommSemiring K] (F : Pattern) (n : ℕ)
    (a : F.A ≃ Fin n) (b : F.B ≃ Fin n) :
    hom K (squarePattern n (fun i j => F.mult (a.symm i) (b.symm j))) n = hom K F n := by
  unfold hom
  let ea := Equiv.arrowCongr a (Equiv.refl (Fin n))
  let eb := Equiv.arrowCongr b (Equiv.refl (Fin n))
  change (∑ hA : Fin n → Fin n, ∑ hB : Fin n → Fin n, ∏ i : Fin n, ∏ j : Fin n,
    MvPolynomial.X (hA i, hB j) ^ F.mult (a.symm i) (b.symm j)) = _
  apply Fintype.sum_equiv ea.symm
  intro hA
  apply Fintype.sum_equiv eb.symm
  intro hB
  apply Fintype.prod_equiv a.symm
  intro i
  apply Fintype.prod_equiv b.symm
  intro j
  simp [ea, eb]

/-- Every padded pattern has a presentation on the same fixed square bipartition. -/
theorem exists_square_hom {K : Type*} [CommSemiring K] (F : Pattern) (n : ℕ)
    (hA : Fintype.card F.A = n) (hB : Fintype.card F.B = n) :
    ∃ m : Fin n → Fin n → ℕ, hom K (squarePattern n m) n = hom K F n := by
  let a : F.A ≃ Fin n := Fintype.equivFinOfCardEq hA
  let b : F.B ≃ Fin n := Fintype.equivFinOfCardEq hB
  exact ⟨fun i j => F.mult (a.symm i) (b.symm j), hom_square_reindex F n a b⟩

/-- Padding converts the earlier spanning theorem to generators on exactly `n` vertices
per side. The nonzero isolated-vertex factor is absorbed into coefficients. -/
theorem invariant_mem_span_square {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (hn : 1 ≤ n) (p : MvPolynomial (Fin n × Fin n) K) (hp : MatrixInvariant p) :
    p ∈ Submodule.span K {q | ∃ m : Fin n → Fin n → ℕ,
      hom K (squarePattern n m) n = q} := by
  have hspan := Lax461425.HomomorphismSpanning.invariant_mem_span_hom hn p hp
  refine (Submodule.span_le.mpr ?_) hspan
  rintro q ⟨F, hA, hB, rfl⟩
  change hom K F n ∈ Submodule.span K {q | ∃ m : Fin n → Fin n → ℕ,
    hom K (squarePattern n m) n = q}
  obtain ⟨m, hm⟩ := exists_square_hom (K := K) (padPattern F n) n
    (card_pad_left F n hA) (card_pad_right F n hB)
  have hmem : hom K (squarePattern n m) n ∈
      Submodule.span K {q | ∃ m : Fin n → Fin n → ℕ,
        hom K (squarePattern n m) n = q} := Submodule.subset_span ⟨m, rfl⟩
  let s : K := (n : K) ^ ((n - Fintype.card F.A) + (n - Fintype.card F.B))
  have hs : s ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : n ≠ 0))
  have hpad : hom K (squarePattern n m) n = MvPolynomial.C s * hom K F n :=
    hm.trans (hom_padPattern F n)
  have hscaled := Submodule.smul_mem
    (Submodule.span K {q | ∃ m : Fin n → Fin n → ℕ,
      hom K (squarePattern n m) n = q}) s⁻¹ hmem
  have hnormalize : s⁻¹ • hom K (squarePattern n m) n = hom K F n := by
    rw [MvPolynomial.smul_eq_C_mul, hpad, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ hs, map_one, one_mul]
  rw [hnormalize] at hscaled
  exact hscaled

/-- A matrix-invariant polynomial is a finite linear combination of homomorphism
polynomials on one common square bipartition. -/
theorem finite_square_combination {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (hn : 1 ≤ n) (p : MvPolynomial (Fin n × Fin n) K) (hp : MatrixInvariant p) :
    ∃ (r : ℕ) (c : Fin r → K) (m : Fin r → Fin n → Fin n → ℕ),
      p = ∑ i, MvPolynomial.C (c i) * hom K (squarePattern n (m i)) n := by
  obtain ⟨r, c, g, hg⟩ := Submodule.mem_span_set'.1 (invariant_mem_span_square hn p hp)
  choose m hm using fun i => (g i).property
  refine ⟨r, c, m, ?_⟩
  rw [← hg]
  apply Finset.sum_congr rfl
  intro i _
  rw [MvPolynomial.smul_eq_C_mul, hm]

end Lax461425Proofs.Section7Padding
