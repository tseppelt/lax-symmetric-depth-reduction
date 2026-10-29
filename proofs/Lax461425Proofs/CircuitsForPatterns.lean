import Lax461425Proofs.ConverseIsolated

/-!
Final assembly of `thm:converse`'s remaining goal: discharging the concept axiom
`Lax461425.CircuitsForPatterns.exists_circuit`.

Given a pattern `F` with `fw_Δ(F) ≤ k - 1`, we split on whether `F` has isolated vertices
(`isoJ F = 0` or not):

* if not, `F` itself has no isolated vertices, and we package the existing converse-side
  construction (`circuit`/`reduced`) directly, applied to a `NormDecomp` of `F`;
* if so, we apply the same construction to `Fiso F` (the sub-pattern on the non-isolated
  vertices of `F`, which provably has none itself), obtaining a reduced matrix-symmetric
  circuit `R0` computing `hom K (Fiso F) n`, and wrap it (`wcircuit`, from
  `ConverseIsolated.lean`) with two pendant gates absorbing the extra factor `n ^ isoJ F`
  coming from the free choice of image of each isolated vertex. All structural properties
  (`Computes`, `IsReduced`, `IsMatrixSymmetric`, `supportSize`, `supportDepth`, `orbitSize`,
  `depth`, `size`) of the wrapper are already established in `ConverseIsolated.lean`; here we
  only need to supply the numeric bookkeeping relating `F`'s and `(Fiso F)`'s size bound.
-/

namespace Lax461425Proofs

open Classical Lax461425.Circuits Lax461425.HomomorphismPolynomials Lax461425.Forestwidth
open Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.RigidConstruction Lax461425Proofs.RigidRep Lax461425Proofs.RigidEquiv
open Lax461425Proofs.RigidComputes Lax461425Proofs.RigidDepth Lax461425Proofs.RigidSize
open Lax461425Proofs.RigidReduced Lax461425Proofs.RigidSymmetric
open MvPolynomial

section NumericBound

/-- **The numeric size bound used for the isolated-vertex branch.** If `S0 ≤ 5 * n ^ k * M0`
and `M = M0 + j` with `j ≥ 1`, `k ≥ 2`, `n ≥ 1`, then `S0 + 2 + j + n ≤ 5 * n ^ k * M`. -/
theorem wrapper_size_bound (n k M0 j S0 : ℕ) (hk : 2 ≤ k) (hn0 : 0 < n) (hj : 1 ≤ j)
    (hS0 : S0 ≤ 5 * n ^ k * M0) :
    S0 + 2 + j + n ≤ 5 * n ^ k * (M0 + j) := by
  have hn2' : n * n ≤ n ^ k := by
    calc n * n = n ^ 2 := (sq n).symm
      _ ≤ n ^ k := Nat.pow_le_pow_right hn0 hk
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn0
  have hge1' : 1 ≤ n ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k hn0.ne')
  have hge1 : 1 ≤ 5 * n ^ k := by omega
  have h5 : n + 3 ≤ 5 * n ^ k := by omega
  have hmain : 2 + j + n ≤ 5 * n ^ k * j := by
    have hjeq : j = 1 + (j - 1) := by omega
    have e1 : 5 * n ^ k * j = 5 * n ^ k * 1 + 5 * n ^ k * (j - 1) := by
      conv_lhs => rw [hjeq, Nat.mul_add]
    have e2 : 1 * (j - 1) ≤ 5 * n ^ k * (j - 1) :=
      Nat.mul_le_mul hge1 (le_refl (j - 1))
    rw [mul_one] at e1
    omega
  calc S0 + 2 + j + n ≤ 5 * n ^ k * M0 + (2 + j + n) := by omega
    _ ≤ 5 * n ^ k * M0 + 5 * n ^ k * j := by omega
    _ = 5 * n ^ k * (M0 + j) := by ring

end NumericBound

section IsolatedBranch

variable {K : Type*} [Field K] [CharZero K] {Δ k n : ℕ}

theorem noIsolatedVertices_of_isoJ_eq_zero {F : Pattern} (hj0 : isoJ F = 0) :
    NoIsolatedVertices F := by
  have hboth : Fintype.card (IsoA F) = 0 ∧ Fintype.card (IsoB F) = 0 := by
    unfold isoJ at hj0; omega
  have hIsoAEmpty : IsEmpty (IsoA F) := Fintype.card_eq_zero_iff.mp hboth.1
  have hIsoBEmpty : IsEmpty (IsoB F) := Fintype.card_eq_zero_iff.mp hboth.2
  have hAall : ∀ a : F.A, ∃ b, F.mult a b ≠ 0 := by
    intro a; by_contra hcon; exact hIsoAEmpty.false ⟨a, hcon⟩
  have hBall : ∀ b : F.B, ∃ a, F.mult a b ≠ 0 := by
    intro b; by_contra hcon; exact hIsoBEmpty.false ⟨b, hcon⟩
  intro v
  cases v with
  | inl a => obtain ⟨b, hb⟩ := hAall a; exact ⟨a, b, hb, Or.inl rfl⟩
  | inr b => obtain ⟨a, ha⟩ := hBall b; exact ⟨a, b, ha, Or.inr rfl⟩

/-- **The characterisation theorem, isolated-vertex-free branch.** -/
theorem exists_circuit_of_noIsolated (hΔ : 1 ≤ Δ) (hk : 2 ≤ k) (hn : 2 * k + 1 ≤ n) (F : Pattern)
    (hE : ∃ a b, F.mult a b ≠ 0) (D : DepthDecomposition F Δ k) (hNI : NoIsolatedVertices F) :
    ∃ C : Circuit (Fin n × Fin n) K,
      C.Computes (hom K F n) ∧ C.IsReduced ∧ IsMatrixSymmetric C ∧
        supportSize C ≤ k ∧ supportDepth C ≤ Δ ∧ orbitSize C ≤ n ^ k ∧
        C.depth ≤ 2 * Δ + 1 ∧
        C.size ≤ 5 * n ^ k * (Fintype.card F.A + Fintype.card F.B + ∑ a, ∑ b, F.mult a b) := by
  have hn0 : 0 < n := by omega
  set N := normDecompOfDepthDecomposition D with hNdef
  set C0 := circuit N n K hn0 hE with hC0def
  refine ⟨reduced C0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact computes_transfer C0 (circuit_computes_hom N n hE hn0 hNI)
  · exact isReduced_reduced C0
  · exact isMatrixSymmetric_reduced C0 (isMatrixSymmetric_circuit N n hn0 hE)
  · exact supportSize_reduced_le' N n hn0 hE hk
  · exact supportDepth_reduced_le' N n hn0 hE hk (by omega)
  · exact orbitSize_reduced_le N n hn0 hE hk
  · exact le_trans (depth_reduced_le C0) (circuit_depth_le N n K hn0 hE)
  · exact le_trans (size_reduced_le C0) (circuit_size_le N n K hn0 hk hE)

end IsolatedBranch

section WrapperBranch

variable {K : Type*} [Field K] [CharZero K] {Δ k n : ℕ}

/-- **The characterisation theorem, isolated-vertex branch.** -/
theorem exists_circuit_of_isolated (hΔ : 1 ≤ Δ) (hk : 2 ≤ k) (hn : 2 * k + 1 ≤ n) (F : Pattern)
    (hE : ∃ a b, F.mult a b ≠ 0) (D : DepthDecomposition F Δ k) (hj0 : 0 < isoJ F) :
    ∃ C : Circuit (Fin n × Fin n) K,
      C.Computes (hom K F n) ∧ C.IsReduced ∧ IsMatrixSymmetric C ∧
        supportSize C ≤ k ∧ supportDepth C ≤ Δ ∧ orbitSize C ≤ n ^ k ∧
        C.depth ≤ 2 * Δ + 1 ∧
        C.size ≤ 5 * n ^ k * (Fintype.card F.A + Fintype.card F.B + ∑ a, ∑ b, F.mult a b) := by
  have hn0 : 0 < n := by omega
  have hn2k : 2 * k < n := by omega
  have hNI' : NoIsolatedVertices (Fiso F) := noIsolatedVertices_Fiso F
  have hE' : ∃ a b, (Fiso F).mult a b ≠ 0 := exists_edge_Fiso F hE
  set D' := isoDepthDecomposition D with hD'def
  set N' := normDecompOfDepthDecomposition D' with hN'def
  set C0' := circuit N' n K hn0 hE' with hC0'def
  set R0 := reduced C0' with hR0def
  have hout : R0.label R0.out = .mul := by
    show C0'.label (rep C0' C0'.out) = .mul
    rw [← equiv_label_eq C0' (rep_equiv C0' C0'.out)]
    rfl
  have hredR0 : R0.IsReduced := isReduced_reduced C0'
  have hsym0 : IsMatrixSymmetric C0' := isMatrixSymmetric_circuit N' n hn0 hE'
  have hsymR0 : IsMatrixSymmetric R0 := isMatrixSymmetric_reduced C0' hsym0
  have hrig0 : IsRigid R0 := Lax461425Proofs.ReducedRigid.isRigid hsymR0 hredR0
  have hextγ' : ∀ γ : Γ n, Extends C0' (actGateEquiv N' n γ) (actVar γ) :=
    fun γ => ⟨actGate_label N' n γ, actGate_wire N' n γ⟩
  let τ : Γ n → R0.Gate ≃ R0.Gate := fun γ =>
    toC'Equiv C0' (show Extends C0' (actGateEquiv N' n γ) (⇑(Equiv.prodCongr γ.1 γ.2)) from
      hextγ' γ)
  have hτ : ∀ γ, Extends R0 (τ γ) (actVar γ) := fun γ => extends_toC'Equiv (hextγ' γ)
  have hnoconst : ∀ x : R0.Gate, ∀ c : K, R0.label x ≠ .const c := by
    intro x c hcon
    have hceq : C0'.label x.1 = .const c := hcon
    cases hx1 : x.1 with
    | R t γ => rw [hx1] at hceq; cases hceq
    | S t δ => rw [hx1] at hceq; cases hceq
    | inp i j => rw [hx1] at hceq; cases hceq
  have hredD : (wcircuit R0 (isoJ F) hout hj0 hn0).IsReduced :=
    wcircuit_isReduced R0 (isoJ F) hout hj0 hn0 hredR0 hnoconst
  have hsymD : IsMatrixSymmetric (wcircuit R0 (isoJ F) hout hj0 hn0) :=
    wcircuit_isMatrixSymmetric R0 (isoJ F) hout hj0 hn0 τ hτ
  have hrigD : IsRigid (wcircuit R0 (isoJ F) hout hj0 hn0) :=
    Lax461425Proofs.ReducedRigid.isRigid hsymD hredD
  have hss0 : supportSize R0 ≤ k := supportSize_reduced_le' N' n hn0 hE' hk
  have hΔ0 : ∀ {m : ℕ} (p' : Fin (m + 1) → R0.Gate), R0.IsPath p' → supportChanges R0 p' ≤ Δ :=
    fun p' hp' => supportChanges_le_Δ N' n hn0 hE' hk hn2k hrig0 p' hp'
  have hcomputes : (wcircuit R0 (isoJ F) hout hj0 hn0).Computes (hom K F n) := by
    show (wcircuit R0 (isoJ F) hout hj0 hn0).Computes (hom K F n)
    rw [hom_eq_pow_mul_hom_Fiso F n, mul_comm]
    exact wcircuit_computes R0 (isoJ F) hout hj0 hn0
      (computes_transfer C0' (circuit_computes_hom N' n hE' hn0 hNI'))
  have hdepth : (wcircuit R0 (isoJ F) hout hj0 hn0).depth ≤ 2 * Δ + 1 := by
    have h1 : (wcircuit R0 (isoJ F) hout hj0 hn0).depth ≤ max R0.depth 2 :=
      wcircuit_depth_le R0 (isoJ F) hout hj0 hn0
    have h2 : R0.depth ≤ 2 * Δ + 1 :=
      le_trans (depth_reduced_le C0') (circuit_depth_le N' n K hn0 hE')
    have h3 : (2 : ℕ) ≤ 2 * Δ + 1 := by omega
    exact le_trans h1 (max_le h2 h3)
  have hsize : (wcircuit R0 (isoJ F) hout hj0 hn0).size ≤
      5 * n ^ k * (Fintype.card F.A + Fintype.card F.B + ∑ a, ∑ b, F.mult a b) := by
    apply wcircuit_size_le R0 (isoJ F) hout hj0 hn0
    have hR0size : R0.size ≤ 5 * n ^ k *
        (Fintype.card (Fiso F).A + Fintype.card (Fiso F).B + ∑ a, ∑ b, (Fiso F).mult a b) :=
      le_trans (size_reduced_le C0') (circuit_size_le N' n K hn0 hk hE')
    have hbound := wrapper_size_bound n k
      (Fintype.card (Fiso F).A + Fintype.card (Fiso F).B + ∑ a, ∑ b, (Fiso F).mult a b)
      (isoJ F) R0.size hk hn0 hj0 hR0size
    have hA : Fintype.card F.A = Fintype.card (NonIsoA F) + Fintype.card (IsoA F) := by
      rw [← Fintype.card_sum]
      exact Fintype.card_congr (Equiv.sumCompl (fun a : F.A => ∃ b, F.mult a b ≠ 0)).symm
    have hB : Fintype.card F.B = Fintype.card (NonIsoB F) + Fintype.card (IsoB F) := by
      rw [← Fintype.card_sum]
      exact Fintype.card_congr (Equiv.sumCompl (fun b : F.B => ∃ a, F.mult a b ≠ 0)).symm
    have hE2 : (∑ a : F.A, ∑ b : F.B, F.mult a b) =
        ∑ a0 : NonIsoA F, ∑ b0 : NonIsoB F, F.mult a0.1 b0.1 := by
      have step1 : (∑ a : F.A, ∑ b : F.B, F.mult a b) =
          ∑ a0 : NonIsoA F, ∑ b : F.B, F.mult a0.1 b := by
        have heq : (∑ a ∈ Finset.univ.filter (fun a : F.A => ∃ b, F.mult a b ≠ 0),
              ∑ b : F.B, F.mult a b) = ∑ a0 : NonIsoA F, ∑ b : F.B, F.mult a0.1 b :=
          Finset.sum_subtype (Finset.univ.filter (fun a : F.A => ∃ b, F.mult a b ≠ 0)) (by simp)
            (fun a => ∑ b : F.B, F.mult a b)
        rw [← heq]
        refine (Finset.sum_subset (Finset.filter_subset _ _) (fun a _ ha => ?_)).symm
        have ha' : ¬ ∃ b, F.mult a b ≠ 0 := by simpa using ha
        apply Finset.sum_eq_zero
        intro b _
        by_contra hc
        exact ha' ⟨b, hc⟩
      rw [step1]
      refine Finset.sum_congr rfl (fun a0 _ => ?_)
      have heq : (∑ b ∈ Finset.univ.filter (fun b : F.B => ∃ a, F.mult a b ≠ 0), F.mult a0.1 b) =
          ∑ b0 : NonIsoB F, F.mult a0.1 b0.1 :=
        Finset.sum_subtype (Finset.univ.filter (fun b : F.B => ∃ a, F.mult a b ≠ 0)) (by simp)
          (fun b => F.mult a0.1 b)
      rw [← heq]
      refine (Finset.sum_subset (Finset.filter_subset _ _) (fun b _ hb => ?_)).symm
      have hb' : ¬ ∃ a, F.mult a b ≠ 0 := by simpa using hb
      by_contra hc
      exact hb' ⟨a0.1, hc⟩
    have hMeq : (Fintype.card (Fiso F).A + Fintype.card (Fiso F).B +
          ∑ a : (Fiso F).A, ∑ b : (Fiso F).B, (Fiso F).mult a b) + isoJ F =
        Fintype.card F.A + Fintype.card F.B + ∑ a : F.A, ∑ b : F.B, F.mult a b := by
      show (Fintype.card (NonIsoA F) + Fintype.card (NonIsoB F) +
          ∑ a0 : NonIsoA F, ∑ b0 : NonIsoB F, F.mult a0.1 b0.1) + isoJ F =
        Fintype.card F.A + Fintype.card F.B + ∑ a : F.A, ∑ b : F.B, F.mult a b
      unfold isoJ
      omega
    rw [hMeq] at hbound
    exact hbound
  exact ⟨wcircuit R0 (isoJ F) hout hj0 hn0, hcomputes, hredD, hsymD,
    wcircuit_supportSize_le R0 (isoJ F) hout hj0 hn0 τ hτ hrig0 hrigD hss0,
    wcircuit_supportDepth_le R0 (isoJ F) hout hj0 hn0 τ hτ hrig0 hrigD hss0 hn2k hΔ0,
    wcircuit_orbitSize_le R0 (isoJ F) hout hj0 hn0 τ hτ hrig0 hrigD hss0,
    hdepth, hsize⟩

end WrapperBranch

/--
---
conclusion: Lax461425.CircuitsForPatterns.exists_circuit
---
After unfolding `ForestwidthLE Δ (k - 1) F` (the arithmetic `(k - 1) + 1 = k`, using `k ≥ 2`,
is immediate) into a `DepthDecomposition F Δ k`, we split on whether `F` has isolated vertices
(`isoJ F = 0` or not) and invoke `exists_circuit_of_noIsolated` or `exists_circuit_of_isolated`
respectively.
-/
theorem exists_circuit {K : Type*} [Field K] [CharZero K] {Δ k n : ℕ} (hΔ : 1 ≤ Δ) (hk : 2 ≤ k)
    (hn : 2 * k + 1 ≤ n) (F : Pattern) (hE : ∃ a b, F.mult a b ≠ 0)
    (hF : ForestwidthLE Δ (k - 1) F) :
    ∃ C : Circuit (Fin n × Fin n) K,
      C.Computes (hom K F n) ∧ C.IsReduced ∧ IsMatrixSymmetric C ∧
        supportSize C ≤ k ∧
        supportDepth C ≤ Δ ∧
        orbitSize C ≤ n ^ k ∧
        C.depth ≤ 2 * Δ + 1 ∧
        C.size ≤ 5 * n ^ k * (Fintype.card F.A + Fintype.card F.B + ∑ a, ∑ b, F.mult a b) := by
  have hkk : k - 1 + 1 = k := by omega
  obtain ⟨D0⟩ := hF
  have D : DepthDecomposition F Δ k := hkk ▸ D0
  by_cases hj0 : isoJ F = 0
  · exact exists_circuit_of_noIsolated hΔ hk hn F hE D (noIsolatedVertices_of_isoJ_eq_zero hj0)
  · exact exists_circuit_of_isolated hΔ hk hn F hE D (Nat.pos_of_ne_zero hj0)

end Lax461425Proofs
