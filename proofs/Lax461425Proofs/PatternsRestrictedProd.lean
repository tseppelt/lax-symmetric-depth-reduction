import Lax461425Proofs.PatternsRestrictedSum
import Lax461425Proofs.PatternsRestrictedCard
import Lax461425Proofs.PatternsNewton
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Algebra.Rat

/-!
---
title: The restricted product ψ_Π (lem:restricted, Π-part)
type: theorem
---
Assembling `PatternsRestrictedCard` (`|Y(v,w)|` depends only on `n, ℓ, ℓ', r, r'`),
`PatternsRestrictedSum`'s machinery (`δ`, `sumExt`, their span membership and evaluation), and
`PatternsNewton` (Newton's identity expressing a product of elements via their power sums) to
build `ψ_Π`.

For `m ≥ 0`, `Q_m := c⁻¹ • Σ^≠(δ ⊙ φ^{⊙m})` lies in `𝔗^{Δ+1,k}_n(ℓ,r)` (exactly as `ψ_Σ` lies in
that span, with `φ` replaced by `φ^{⊙m}`, itself still in `𝔗^{Δ,k}_{n,P}(ℓ+ℓ',r+r')` since the
span is closed under pointwise powers). At injective `v, w`, given a partition of `Y(v,w)` into
classes of size `c` on which `φ` is constant (value `φ_B` on class `B`), `Q_m(v,w)` collapses to
`Σ_B φ_B^m`, i.e. the `m`-th power sum of the family `(φ_B)_{B ∈ 𝒬}`.

Fixing `N := |Y(v,w)|/c` (well defined independent of `v, w` by `PatternsRestrictedCard.card_Y_eq`)
and `ψ_Π := (N!)⁻¹ • Σ_π μ(π) ⊙_{B ∈ π} Q_{|B|}` (summed over partitions `π` of `Fin N`),
`PatternsNewton.newton` applied to the `N` values `(φ_B)_{B ∈ 𝒬}` (reindexed via a bijection
`Fin N ≃ 𝒬.parts`, using `|𝒬.parts| = N`) gives `ψ_Π(v,w) = ∏_{B ∈ 𝒬} φ_B`. Membership of `ψ_Π`
in the span additionally uses that `ℓ + r ≤ k` (so that *pointwise products* of up to `N`
`Δ+1`-level terms stay inside `𝔗^{Δ+1,k}_n(ℓ,r)`, via `span𝔗P_mul_mem` on the `Finset.univ`
support), matching the paper's own use of this hypothesis for `ψ_Π` (not needed for `ψ_Σ`).
-/

open Lax461425.SymmetricFamilies (MatrixPolynomial)

namespace Lax461425Proofs.PatternsRestrictedProd

open Lax461425.HomomorphismPolynomials Lax461425Proofs.PatternsLabelledBasic
open Lax461425Proofs.PatternsLabelledOps Lax461425Proofs.PatternsLabelledSpanMul
open Lax461425Proofs.PatternsRestrictedMono Lax461425Proofs.PatternsRestrictedDelta
open Lax461425Proofs.PatternsRestrictedY Lax461425Proofs.PatternsRestrictedDelete
open Lax461425Proofs.PatternsRestrictedSum Lax461425Proofs.PatternsRestrictedCard
open scoped Classical

variable {ℓ ℓ' r r' : ℕ}

/-! ### `φ^{⊙m}` stays in the span -/

/-- The span `𝔗^{Δ,k}_{n,P}(ℓ,r)` is closed under pointwise powers. -/
theorem span𝔗P_pow_mem {K : Type*} [Field K] {Δ k n ℓ r : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)}
    (hP : P.card ≤ k) {φ : (Fin ℓ → Fin n) → (Fin r → Fin n) → MatrixPolynomial n K}
    (hφ : φ ∈ span𝔗P K Δ k n P) (m : ℕ) :
    (fun v w => φ v w ^ m) ∈ span𝔗P K Δ k n P := by
  induction m with
  | zero => simpa using one_mem_span𝔗P K Δ k n P
  | succ m ih =>
      have heq : (fun v w => φ v w ^ (m + 1)) = fun v w => φ v w * φ v w ^ m := by
        funext v w; ring
      rw [heq]
      exact span𝔗P_mul_mem hP hφ ih

/-! ### `Q_m`: the restricted sum of `φ^{⊙m}` over `Y(v,w)`, divided by `c` -/

/-- **`Q_m`**: `c⁻¹ • Σ^≠(δ ⊙ φ^{⊙m})`, mirroring the construction inside `exists_ψSum` with `φ`
replaced by `φ^{⊙m}`. -/
noncomputable def Q (K : Type*) [Field K] (ℓ ℓ' r r' n c : ℕ)
    (φ : (Fin (ℓ + ℓ') → Fin n) → (Fin (r + r') → Fin n) → MatrixPolynomial n K)
    (m : ℕ) : (Fin ℓ → Fin n) → (Fin r → Fin n) → MatrixPolynomial n K :=
  (c : K)⁻¹ • sumExt K n (fun v' w' => δ K ℓ ℓ' r r' n v' w' * φ v' w' ^ m)

/-- **`Q_m` lies in the (unrestricted) `Δ+1` span**, for every `m`. -/
theorem Q_mem_span (K : Type*) [Field K] (Δ k n ℓ ℓ' r r' c : ℕ)
    (P : Finset (Fin (ℓ + ℓ') ⊕ Fin (r + r'))) (hP : P.card ≤ k)
    (φ : (Fin (ℓ + ℓ') → Fin n) → (Fin (r + r') → Fin n) → MatrixPolynomial n K)
    (hφ : φ ∈ span𝔗P K Δ k n P) (m : ℕ) :
    Q K ℓ ℓ' r r' n c φ m ∈ span𝔗P K (Δ + 1) k n (Finset.univ : Finset (Fin ℓ ⊕ Fin r)) := by
  unfold Q
  exact Submodule.smul_mem _ _
    (span𝔗P_restrict_sum K Δ k n P _
      (span𝔗P_mul_mem hP (δ_mem_span K Δ k n P hP) (span𝔗P_pow_mem hP hφ m)))

/-- **`Q_m`'s evaluation** at injective `v, w`: the `m`-th power sum of `φ` over `Y(v,w)`,
divided by `c`. -/
theorem Q_eval (K : Type*) [Field K] (ℓ ℓ' r r' n c : ℕ)
    (φ : (Fin (ℓ + ℓ') → Fin n) → (Fin (r + r') → Fin n) → MatrixPolynomial n K)
    (v : Fin ℓ → Fin n) (w : Fin r → Fin n) (hv : Function.Injective v)
    (hw : Function.Injective w) (m : ℕ) :
    Q K ℓ ℓ' r r' n c φ m v w =
      (c : K)⁻¹ • ∑ yz ∈ Y ℓ' r' n v w, (φ (Fin.append v yz.1) (Fin.append w yz.2)) ^ m := by
  unfold Q
  show (c : K)⁻¹ • sumExt K n (fun v' w' => δ K ℓ ℓ' r r' n v' w' * φ v' w' ^ m) v w = _
  rw [sumExt_delta_mul_eq_sum_Y K n v w hv hw (fun v' w' => φ v' w' ^ m)]

/-- **`Q_m`'s evaluation against a size-`c` partition**: `Q_m(v,w)` is the `m`-th power sum
`Σ_{B ∈ 𝒬} φ_B^m` of the constant values `φ_B` of `φ` on the classes of a partition `𝒬` of
`Y(v,w)` into classes of size `c`. -/
theorem Q_eval_partition (K : Type*) [Field K] [CharZero K] (ℓ ℓ' r r' n c : ℕ) (hc : c ≠ 0)
    (φ : (Fin (ℓ + ℓ') → Fin n) → (Fin (r + r') → Fin n) → MatrixPolynomial n K)
    (v : Fin ℓ → Fin n) (w : Fin r → Fin n) (hv : Function.Injective v)
    (hw : Function.Injective w) (m : ℕ) (𝒬 : Finpartition (Y ℓ' r' n v w))
    (hsize : ∀ B ∈ 𝒬.parts, B.card = c)
    (φB : Finset ((Fin ℓ' → Fin n) × (Fin r' → Fin n)) → MatrixPolynomial n K)
    (hφB : ∀ B ∈ 𝒬.parts, ∀ x ∈ B, φ (Fin.append v x.1) (Fin.append w x.2) = φB B) :
    Q K ℓ ℓ' r r' n c φ m v w = ∑ B ∈ 𝒬.parts, (φB B) ^ m := by
  rw [Q_eval K ℓ ℓ' r r' n c φ v w hv hw m,
    Finpartition.sum_parts 𝒬 (fun x => (φ (Fin.append v x.1) (Fin.append w x.2)) ^ m)]
  have hterm : ∀ B ∈ 𝒬.parts,
      ∑ x ∈ B, (φ (Fin.append v x.1) (Fin.append w x.2)) ^ m = (c : K) • (φB B) ^ m := by
    intro B hB
    rw [Finset.sum_congr rfl (fun x hx => by rw [hφB B hB x hx])]
    rw [Finset.sum_const, hsize B hB, ← Nat.cast_smul_eq_nsmul K]
  rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hc), one_smul]

/-! ### Bridging `R`-valued `μ(π)` back to a `K`-scalar -/

/-- `μ(π)`, computed inside `MatrixPolynomial n K`, is `C` applied to `μ(π)` computed
inside `K` itself: both are built from the same integer data (`-1`'s and factorials) via a ring
homomorphism (`MvPolynomial.C`). -/
theorem muC_eq {K : Type*} [Field K] [CharZero K] {n N : ℕ}
    [Algebra ℚ (MatrixPolynomial n K)] (π : Finpartition (Finset.univ : Finset (Fin N))) :
    MvPolynomial.C (PatternsNewton.mu (R := K) π) =
      PatternsNewton.mu (R := MatrixPolynomial n K) π := by
  unfold PatternsNewton.mu
  rw [map_prod]
  refine Finset.prod_congr rfl (fun B _ => ?_)
  rw [map_mul, map_pow, map_neg, map_one, map_natCast]

/-! ### `ψ_Π` -/

/-- **`ψ_Π` (`lem:restricted`'s Π-part)**: for `φ ∈ 𝔗^{Δ,k}_{n,P}(ℓ+ℓ',r+r')` with `P.card ≤ k`
and `ℓ + r ≤ k`, there is `ψ_Π ∈ 𝔗^{Δ+1,k}_n(ℓ,r)` with the following property. For all injective
`v, w` and every partition `𝒬` of `Y(v,w)` into classes of size exactly `c` (`c ≠ 0`) on which
`φ` is constant (witnessed by `φB`, assigning each part its common value of `φ`), `ψ_Π(v,w) =
∏_{B ∈ 𝒬} φ_B`. -/
theorem exists_ψProd (K : Type*) [Field K] [CharZero K] (Δ k n : ℕ)
    (P : Finset (Fin (ℓ + ℓ') ⊕ Fin (r + r'))) (hP : P.card ≤ k) (hlr : ℓ + r ≤ k) (c : ℕ)
    (hc : c ≠ 0)
    (φ : (Fin (ℓ + ℓ') → Fin n) → (Fin (r + r') → Fin n) → MatrixPolynomial n K)
    (hφ : φ ∈ span𝔗P K Δ k n P) :
    ∃ ψProd : (Fin ℓ → Fin n) → (Fin r → Fin n) → MatrixPolynomial n K,
      ψProd ∈ span𝔗P K (Δ + 1) k n (Finset.univ : Finset (Fin ℓ ⊕ Fin r)) ∧
      ∀ (v : Fin ℓ → Fin n) (w : Fin r → Fin n), Function.Injective v → Function.Injective w →
      ∀ (𝒬 : Finpartition (Y ℓ' r' n v w)), (∀ B ∈ 𝒬.parts, B.card = c) →
      ∀ (φB : Finset ((Fin ℓ' → Fin n) × (Fin r' → Fin n)) → MatrixPolynomial n K),
        (∀ B ∈ 𝒬.parts, ∀ x ∈ B, φ (Fin.append v x.1) (Fin.append w x.2) = φB B) →
        ψProd v w = ∏ B ∈ 𝒬.parts, φB B := by
  have hAlg : Algebra ℚ (MatrixPolynomial n K) :=
    RingHom.toAlgebra ((MvPolynomial.C).comp (algebraMap ℚ K))
  have hPunivlr : (Finset.univ : Finset (Fin ℓ ⊕ Fin r)).card ≤ k := by
    rw [Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    exact hlr
  set N : ℕ := cardY n ℓ ℓ' r r' / c with hN
  refine ⟨fun v w => (N.factorial : K)⁻¹ •
    ∑ π : Finpartition (Finset.univ : Finset (Fin N)),
      PatternsNewton.mu (R := MatrixPolynomial n K) π *
        ∏ B ∈ π.parts, Q K ℓ ℓ' r r' n c φ B.card v w, ?_, ?_⟩
  · -- Membership.
    apply Submodule.smul_mem
    have hsum_eq : (fun v w => ∑ π : Finpartition (Finset.univ : Finset (Fin N)),
          PatternsNewton.mu (R := MatrixPolynomial n K) π *
            ∏ B ∈ π.parts, Q K ℓ ℓ' r r' n c φ B.card v w) =
        ∑ π : Finpartition (Finset.univ : Finset (Fin N)),
          (fun v w => PatternsNewton.mu (R := MatrixPolynomial n K) π *
            ∏ B ∈ π.parts, Q K ℓ ℓ' r r' n c φ B.card v w) := by
      funext v w
      simp only [Finset.sum_apply]
    rw [hsum_eq]
    apply Submodule.sum_mem
    intro π _
    have heq2 : (fun v w => PatternsNewton.mu (R := MatrixPolynomial n K) π *
          ∏ B ∈ π.parts, Q K ℓ ℓ' r r' n c φ B.card v w) =
        (PatternsNewton.mu (R := K) π) •
          (fun v w => ∏ B ∈ π.parts, Q K ℓ ℓ' r r' n c φ B.card v w) := by
      funext v w
      show PatternsNewton.mu (R := MatrixPolynomial n K) π *
          ∏ B ∈ π.parts, Q K ℓ ℓ' r r' n c φ B.card v w =
        (PatternsNewton.mu (R := K) π) • (∏ B ∈ π.parts, Q K ℓ ℓ' r r' n c φ B.card v w)
      rw [Algebra.smul_def, MvPolynomial.algebraMap_eq, muC_eq]
    rw [heq2]
    exact Submodule.smul_mem _ _
      (span𝔗P_prod_mem hPunivlr π.parts (fun B => Q K ℓ ℓ' r r' n c φ B.card)
        (fun B _ => Q_mem_span K Δ k n ℓ ℓ' r r' c P hP φ hφ B.card))
  · -- Evaluation.
    intro v w hv hw 𝒬 hsize φB hφB
    show (N.factorial : K)⁻¹ •
      ∑ π : Finpartition (Finset.univ : Finset (Fin N)),
        PatternsNewton.mu (R := MatrixPolynomial n K) π *
          ∏ B ∈ π.parts, Q K ℓ ℓ' r r' n c φ B.card v w = ∏ B ∈ 𝒬.parts, φB B
    have hsumcard : ∑ B ∈ 𝒬.parts, B.card = (Y ℓ' r' n v w).card := Finpartition.sum_card_parts 𝒬
    have hsumcard' : ∑ B ∈ 𝒬.parts, B.card = 𝒬.parts.card * c := by
      rw [Finset.sum_congr rfl hsize, Finset.sum_const, smul_eq_mul]
    have hYcard : (Y ℓ' r' n v w).card = cardY n ℓ ℓ' r r' := card_Y_eq v w hv hw
    have hc0 : 0 < c := Nat.pos_of_ne_zero hc
    have hNparts : 𝒬.parts.card = N := by
      have heqc : 𝒬.parts.card * c = cardY n ℓ ℓ' r r' := by rw [← hsumcard', hsumcard, hYcard]
      rw [hN, ← heqc, Nat.mul_comm, Nat.mul_div_cancel_left _ hc0]
    have hcardcoe : Fintype.card (↥𝒬.parts) = N := by rw [Fintype.card_coe, hNparts]
    set e : Fin N ≃ ↥𝒬.parts := (Fintype.equivFinOfCardEq hcardcoe).symm with he
    set y : Fin N → MatrixPolynomial n K := fun i => φB (e i).1 with hy
    have hsum_coe : ∀ (g : Finset ((Fin ℓ' → Fin n) × (Fin r' → Fin n)) →
        MatrixPolynomial n K), ∑ x : ↥𝒬.parts, g x.1 = ∑ B ∈ 𝒬.parts, g B := by
      intro g
      show ∑ x ∈ (Finset.univ : Finset ↥𝒬.parts), g x.1 = ∑ B ∈ 𝒬.parts, g B
      rw [Finset.univ_eq_attach, Finset.sum_attach]
    have hprod_coe : ∀ (g : Finset ((Fin ℓ' → Fin n) × (Fin r' → Fin n)) →
        MatrixPolynomial n K), ∏ x : ↥𝒬.parts, g x.1 = ∏ B ∈ 𝒬.parts, g B := by
      intro g
      show ∏ x ∈ (Finset.univ : Finset ↥𝒬.parts), g x.1 = ∏ B ∈ 𝒬.parts, g B
      rw [Finset.univ_eq_attach, Finset.prod_attach]
    have hprodY : ∏ i, y i = ∏ B ∈ 𝒬.parts, φB B := by
      show ∏ i : Fin N, φB (e i).1 = ∏ B ∈ 𝒬.parts, φB B
      rw [Equiv.prod_comp e (fun x : ↥𝒬.parts => φB x.1)]
      exact hprod_coe φB
    have hpowerSum : ∀ m, PatternsNewton.powerSum y m = ∑ B ∈ 𝒬.parts, (φB B) ^ m := by
      intro m
      show ∑ i : Fin N, y i ^ m = ∑ B ∈ 𝒬.parts, (φB B) ^ m
      have hswap : (fun i : Fin N => y i ^ m) =
          fun i : Fin N => (fun x : ↥𝒬.parts => (φB x.1) ^ m) (e i) := rfl
      rw [hswap, Equiv.sum_comp e (fun x : ↥𝒬.parts => (φB x.1) ^ m)]
      exact hsum_coe (fun B => (φB B) ^ m)
    have hQ : ∀ m : ℕ, Q K ℓ ℓ' r r' n c φ m v w = PatternsNewton.powerSum y m := by
      intro m
      rw [Q_eval_partition K ℓ ℓ' r r' n c hc φ v w hv hw m 𝒬 hsize φB hφB, hpowerSum]
    have hstep : (N.factorial : MatrixPolynomial n K) * ∏ B ∈ 𝒬.parts, φB B =
        ∑ π : Finpartition (Finset.univ : Finset (Fin N)),
          PatternsNewton.mu (R := MatrixPolynomial n K) π *
            ∏ B ∈ π.parts, Q K ℓ ℓ' r r' n c φ B.card v w := by
      rw [← hprodY, PatternsNewton.newton y]
      refine Finset.sum_congr rfl (fun π _ => ?_)
      refine congrArg (fun z => PatternsNewton.mu (R := MatrixPolynomial n K) π * z) ?_
      exact Finset.prod_congr rfl (fun B _ => (hQ B.card).symm)
    have hcast : (N.factorial : K) • (1 : MatrixPolynomial n K) =
        (N.factorial : MatrixPolynomial n K) := by
      rw [Algebra.smul_def, mul_one, MvPolynomial.algebraMap_eq, map_natCast]
    have hfacne : (N.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
    calc (N.factorial : K)⁻¹ •
        ∑ π : Finpartition (Finset.univ : Finset (Fin N)),
          PatternsNewton.mu (R := MatrixPolynomial n K) π *
            ∏ B ∈ π.parts, Q K ℓ ℓ' r r' n c φ B.card v w
        = (N.factorial : K)⁻¹ •
            ((N.factorial : MatrixPolynomial n K) * ∏ B ∈ 𝒬.parts, φB B) := by
          rw [← hstep]
      _ = (N.factorial : K)⁻¹ •
            (((N.factorial : K) • (1 : MatrixPolynomial n K)) * ∏ B ∈ 𝒬.parts, φB B) := by
          rw [hcast]
      _ = (N.factorial : K)⁻¹ • ((N.factorial : K) • (1 * ∏ B ∈ 𝒬.parts, φB B)) := by
          rw [smul_mul_assoc]
      _ = ((N.factorial : K)⁻¹ * (N.factorial : K)) • (1 * ∏ B ∈ 𝒬.parts, φB B) := by
          rw [smul_smul]
      _ = ∏ B ∈ 𝒬.parts, φB B := by
          rw [inv_mul_cancel₀ hfacne, one_smul, one_mul]

end Lax461425Proofs.PatternsRestrictedProd
