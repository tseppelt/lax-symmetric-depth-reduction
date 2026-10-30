import Lax461425Proofs.DepthHierarchyRichBasic
import Lax461425Proofs.DepthHierarchyRichOddo
import Lax461425Proofs.DepthHierarchyTree
import Lax461425Proofs.DepthHierarchyArith
import Lax461425.SupportTheorem
import Lax461425.BoundedDepthCharacterisation

/-!
First assertion of the depth hierarchy theorem: assembly from the support theorem, the
characterisation of bounded-depth circuits, the non-uniform closure theorem and richness.
-/

namespace Lax461425Proofs.DepthHierarchy

open Lax461425 Lax461425.Forestwidth Lax461425.NonUniformClosure Lax461425.Oddomorphisms
  Lax461425.HomomorphismPolynomials Lax68.GraphMinors Lax871432.GraphClasses
  Lax871432.ClosureProperties Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports

/-- The class of graphs that are not `(Δ,k)`-rich. -/
def nonRich (k Δ : ℕ) : GraphClass where
  Mem F := ¬ IsRich F k Δ
  mem_congr := fun ⟨e⟩ => not_congr (isRich_iso e)

/-- A matrix-symmetric reduced circuit of support depth `≤ Δ` computing `hom_{T_{Δ,n},n}` has
orbit size `≥ C(n, k+1)`. -/
theorem choose_le_orbitSize {K : Type*} [Field K] [CharZero K] {Δ n k : ℕ} (hΔ : 1 ≤ Δ)
    (hn : 20 ≤ n) (hk : 2 ≤ k) (hkn : 4 * (k + 1) ≤ n)
    (hγ : 2 ^ (k + 3) * (k + 1) ^ (Δ - 1) ≤ n)
    (C : Circuit (Fin n × Fin n) K) (hC : C.Computes (hom K (DepthHierarchy.fullTree Δ n) n))
    (hred : C.IsReduced) (hsym : IsMatrixSymmetric C) (hdepth : supportDepth C ≤ Δ) :
    n.choose (k + 1) ≤ orbitSize C := by
  by_contra hlt
  push_neg at hlt
  have hsup : supportSize C ≤ k := by
    have := SupportTheorem.supportSize_le (K := K) hn (κ := k + 1) (by omega) C hred hsym hlt
    simpa using this
  have hmem := (BoundedDepthCharacterisation.characterisation (K := K) (Δ := Δ) (k := k)
    (n := n) hΔ hk (by omega) (hom K (DepthHierarchy.fullTree Δ n) n)).1
    ⟨C, hC, hred, hsym, hsup, hdepth⟩
  have hsub : Submodule.span K {q | ∃ F : Pattern, ForestwidthLE Δ (k - 1) F ∧
      hom K F n = q} ≤ homSpan K (nonRich k Δ) n := by
    apply Submodule.span_mono
    rintro q ⟨F, hF, rfl⟩
    exact ⟨F, fun hr => not_forestwidthLE_of_isRich (by omega) hΔ hr hF, rfl⟩
  obtain ⟨Δ', rfl⟩ : ∃ Δ', Δ = Δ' + 1 := ⟨Δ - 1, by omega⟩
  refine hom_not_mem_homSpan (K := K) (nonRich k (Δ' + 1)) ?_ ?_ ?_
    (treeG (Δ' + 1) (k + 1)) (treeG_connected _ _) ?_ (DepthHierarchy.fullTree (Δ' + 1) n)
    (treeG_isMinor (by omega)) (N := n) (le_trans (cfiSize_treeG_le hΔ (by omega)) hγ)
    (hsub hmem)
  · exact not_isRich_bot (by omega)
  · intro V W _ _ F K' hK hF hr
    exact hF (isRich_of_isMinor hK hr)
  · intro V W _ _ F G φ hφ hF hG
    exact hF (isRich_of_weakOddomorphism φ hφ hG)
  · exact fun h => h ⟨Set.univ, by simpa using treeG_richSet Δ' k⟩

lemma one_le_orbitSize {K : Type*} {n : ℕ} (C : Circuit (Fin n × Fin n) K)
    (hsym : IsMatrixSymmetric C) : 1 ≤ orbitSize C := by
  obtain ⟨σ, hσ⟩ := hsym 1
  have hne : (orbit C C.out).Nonempty := ⟨σ C.out, 1, σ, hσ, rfl⟩
  have h1 : 1 ≤ (orbit C C.out).ncard := Set.ncard_pos (Set.toFinite _) |>.2 hne
  exact h1.trans (Finset.le_sup (f := fun g => (orbit C g).ncard) (Finset.mem_univ C.out))

/--
---
conclusion: Lax461425.DepthHierarchy.orbitSize_ge
---
By `choose_le_orbitSize` and the numerical estimate `arith`.
-/
theorem orbitSize_ge {K : Type*} [Field K] [CharZero K] {Δ n : ℕ} (hΔ : 1 ≤ Δ) (hn : 20 ≤ n)
    (C : Circuit (Fin n × Fin n) K)
    (hC : C.Computes (hom K (DepthHierarchy.fullTree Δ n) n))
    (hred : C.IsReduced) (hsym : IsMatrixSymmetric C) (hdepth : supportDepth C ≤ Δ) :
    (n : ℝ) ^ (Real.logb 2 n - Δ * Real.logb 2 (Real.logb 2 n) - 3) ≤ orbitSize C :=
  arith hΔ hn (one_le_orbitSize C hsym) fun k hk hkn hγ => choose_le_orbitSize hΔ hn hk hkn hγ C hC hred hsym hdepth

end Lax461425Proofs.DepthHierarchy
