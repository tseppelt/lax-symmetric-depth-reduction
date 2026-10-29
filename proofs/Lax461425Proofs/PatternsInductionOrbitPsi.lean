import Lax461425Proofs.PatternsInductionOrbitFinal

/-!
**The orbit-level `ψ^O_Σ`/`ψ^O_Π`, final assembly.** Applies `exists_ψSum`/`exists_ψProd` to
`ψ_h` with the partition `Qpart`, giving witnesses at depth `sc h + 1` whose value at `g`'s
canonical enumeration is the sum/product of `qfun` over `Ofinset hrig hn g h` — i.e. (via
`computesAt_qfun`) the sum/product, over the orbit of `h`, of the polynomials actually computed
by its members.
-/

namespace Lax461425Proofs.PatternsInductionOrbitPsi

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open Lax461425Proofs.PatternsSupportDepth Lax461425Proofs.PatternsInductionSetup
open Lax461425Proofs.PatternsInductionNidx Lax461425Proofs.PatternsInductionTransitive
open Lax461425Proofs.PatternsRestrictedY Lax461425Proofs.PatternsInductionOrbitMap
open Lax461425Proofs.PatternsInductionReindex Lax461425Proofs.PatternsLabelledOps
open Lax461425Proofs.PatternsInductionHomRename Lax461425Proofs.PatternsInductionEquivariant
open Lax461425Proofs.RigidComputes Lax461425Proofs.PatternsInductionPsiH
open Lax461425Proofs.PatternsRestrictedSum Lax461425Proofs.PatternsRestrictedProd
open Lax461425Proofs.PatternsRestrictedMono Lax461425Proofs.PatternsInductionOrbitSum
open Lax461425Proofs.PatternsInductionOrbitWitness Lax461425Proofs.PatternsInductionOrbitFinal
open scoped Classical

set_option maxHeartbeats 4000000

variable {K : Type*} [Field K] [CharZero K] {n : ℕ} {C : Circuit (Fin n × Fin n) K}
variable (hrig : IsRigid C) (hn : 2 * supportSize C < n) {g h : C.Gate} {k : ℕ}
variable (φh : (Fin (leftCard hrig hn h) → Fin n) → (Fin (rightCard hrig hn h) → Fin n) →
  MvPolynomial (Fin n × Fin n) K)
variable (hφh_mem : φh ∈ span𝔗P K (sc C h) k n
  (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h))))
variable (hφh_eval : C.ComputesAt h (φh (leftEnum hrig hn h) (rightEnum hrig hn h)))

/-- **`φB`**: the constant-on-blocks function fed to `exists_ψSum`/`exists_ψProd`, built from
`ψ_h` evaluated at each block's chosen representative. -/
noncomputable def φBlock : Finset (Pairs hrig hn (g := g) (h := h)) → MvPolynomial (Fin n × Fin n) K :=
  fun B =>
    if hB : B ∈ (Qpart hrig hn (g := g) (h := h)).parts then
      ψh hrig hn φh (Fin.append (leftEnum hrig hn g) (exists_rep_of_mem_Qpart hrig hn hB).choose.1)
        (Fin.append (rightEnum hrig hn g) (exists_rep_of_mem_Qpart hrig hn hB).choose.2)
    else 0

omit [CharZero K] in
theorem φBlock_eq {B : Finset (Pairs hrig hn (g := g) (h := h))}
    (hB : B ∈ (Qpart hrig hn (g := g) (h := h)).parts) :
    φBlock hrig hn φh B = ψh hrig hn φh
      (Fin.append (leftEnum hrig hn g) (exists_rep_of_mem_Qpart hrig hn hB).choose.1)
      (Fin.append (rightEnum hrig hn g) (exists_rep_of_mem_Qpart hrig hn hB).choose.2) := by
  rw [φBlock, dif_pos hB]

omit [CharZero K] in
theorem φBlock_const
    (hφh_mem : φh ∈ span𝔗P K (sc C h) k n
      (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h))))
    (hφh_eval : C.ComputesAt h (φh (leftEnum hrig hn h) (rightEnum hrig hn h))) :
    ∀ B (_hB : B ∈ (Qpart hrig hn (g := g) (h := h)).parts), ∀ x ∈ B,
      ψh hrig hn φh (Fin.append (leftEnum hrig hn g) x.1) (Fin.append (rightEnum hrig hn g) x.2) =
        φBlock hrig hn φh B := by
  intro B hB x hx
  rw [φBlock_eq hrig hn φh hB]
  generalize hdef : (exists_rep_of_mem_Qpart hrig hn hB).choose = rep
  have hspec := (exists_rep_of_mem_Qpart hrig hn hB).choose_spec
  rw [hdef] at hspec
  rw [hspec.2] at hx
  obtain ⟨hxY, hxeq⟩ := Finset.mem_filter.mp hx
  exact ψh_eq_of_hYtot_eq hrig hn φh hφh_mem hφh_eval hxY hspec.1 hxeq.symm

/-- **The orbit-level `ψ^O_Σ`.** -/
theorem exists_ψOrbitSum
    (hφh_mem : φh ∈ span𝔗P K (sc C h) k n
      (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h))))
    (hφh_eval : C.ComputesAt h (φh (leftEnum hrig hn h) (rightEnum hrig hn h)))
    (hsize : supportSize C ≤ k) :
    ∃ ψOSum : (Fin (leftCard hrig hn g) → Fin n) → (Fin (rightCard hrig hn g) → Fin n) →
      MvPolynomial (Fin n × Fin n) K,
      ψOSum ∈ span𝔗P K (sc C h + 1) k n
        (Finset.univ : Finset (Fin (leftCard hrig hn g) ⊕ Fin (rightCard hrig hn g))) ∧
      ψOSum (leftEnum hrig hn g) (rightEnum hrig hn g) =
        ∑ h' ∈ Ofinset hrig hn (g := g) (h := h), qfun hrig hn (g := g) φh h' := by
  obtain ⟨ψSumFull, hmem, heval⟩ := exists_ψSum K (sc C h) k n _
    (ψh_P_card_le hrig hn hsize) (cBlock hrig hn) (cBlock_ne_zero hrig hn) (ψh hrig hn φh)
    (ψh_mem hrig hn φh hφh_mem)
  refine ⟨ψSumFull, hmem, ?_⟩
  have heval2 := heval (leftEnum hrig hn g) (rightEnum hrig hn g) (leftEnum_injective hrig hn g)
    (rightEnum_injective hrig hn g) (Qpart hrig hn) (fun B hB => card_eq_cBlock hrig hn hB)
    (φBlock hrig hn φh) (φBlock_const hrig hn φh hφh_mem hφh_eval)
  rw [heval2]
  exact sum_parts_eq_sum_Ofinset hrig hn φh hφh_mem hφh_eval (φBlock hrig hn φh)
    (fun B hB => (φBlock_eq hrig hn φh hB))

/-- **The orbit-level `ψ^O_Π`.** -/
theorem exists_ψOrbitProd
    (hφh_mem : φh ∈ span𝔗P K (sc C h) k n
      (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h))))
    (hφh_eval : C.ComputesAt h (φh (leftEnum hrig hn h) (rightEnum hrig hn h)))
    (hsize : supportSize C ≤ k)
    (hlr : leftCard hrig hn g + rightCard hrig hn g ≤ k) :
    ∃ ψOProd : (Fin (leftCard hrig hn g) → Fin n) → (Fin (rightCard hrig hn g) → Fin n) →
      MvPolynomial (Fin n × Fin n) K,
      ψOProd ∈ span𝔗P K (sc C h + 1) k n
        (Finset.univ : Finset (Fin (leftCard hrig hn g) ⊕ Fin (rightCard hrig hn g))) ∧
      ψOProd (leftEnum hrig hn g) (rightEnum hrig hn g) =
        ∏ h' ∈ Ofinset hrig hn (g := g) (h := h), qfun hrig hn (g := g) φh h' := by
  obtain ⟨ψProdFull, hmem, heval⟩ := exists_ψProd K (sc C h) k n _
    (ψh_P_card_le hrig hn hsize) hlr (cBlock hrig hn) (cBlock_ne_zero hrig hn) (ψh hrig hn φh)
    (ψh_mem hrig hn φh hφh_mem)
  refine ⟨ψProdFull, hmem, ?_⟩
  have heval2 := heval (leftEnum hrig hn g) (rightEnum hrig hn g) (leftEnum_injective hrig hn g)
    (rightEnum_injective hrig hn g) (Qpart hrig hn) (fun B hB => card_eq_cBlock hrig hn hB)
    (φBlock hrig hn φh) (φBlock_const hrig hn φh hφh_mem hφh_eval)
  rw [heval2]
  exact prod_parts_eq_prod_Ofinset hrig hn φh hφh_mem hφh_eval (φBlock hrig hn φh)
    (fun B hB => (φBlock_eq hrig hn φh hB))

end Lax461425Proofs.PatternsInductionOrbitPsi
