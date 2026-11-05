import Lax461425.TreewidthForestwidth
import Lax461425.SymmetricFamilies
import Mathlib.LinearAlgebra.Span.Basic

/-!
Auxiliary facts for the characterisation of symmetric VP: monotonicity of `Δ`-forestwidth and
treewidth, a trivial decomposition for small patterns, the empty pattern, and invariance of
homomorphism polynomials under row and column permutations.
-/

namespace Lax461425Proofs.SymVPWidths

open Lax461425.HomomorphismPolynomials Lax461425.Forestwidth Lax461425.PatternWidths
open Lax461425.SymmetricFamilies Lax461425.MatrixSymmetry

/-- Enlarging the depth or the width bound preserves `Δ`-forestwidth bounds. -/
theorem forestwidthLE_mono {Δ Δ' w w' : ℕ} {F : Pattern} (hΔ : Δ ≤ Δ') (hw : w ≤ w')
    (h : ForestwidthLE Δ w F) : ForestwidthLE Δ' w' F := by
  obtain ⟨D⟩ := h
  refine ⟨{ D with
    depth_le := fun t => ?_
    card_bag_le := fun t => (D.card_bag_le t).trans (by omega) }⟩
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hΔ
  rw [show Δ + e = e + Δ from Nat.add_comm _ _, Function.iterate_add_apply, D.depth_le t]
  exact Function.iterate_fixed D.parent_root e

/-- Treewidth bounds are monotone. -/
theorem treewidthLE_mono {w w' : ℕ} {F : Pattern} (hw : w ≤ w') (h : TreewidthLE w F) :
    TreewidthLE w' F := by
  obtain ⟨Δ, -, hF⟩ := Lax461425.TreewidthForestwidth.exists_forestwidthLE_of_treewidthLE h
  exact Lax461425.TreewidthForestwidth.treewidthLE_of_forestwidthLE
    (forestwidthLE_mono le_rfl hw hF)

/-- The decomposition with an empty root and a single child containing all vertices. -/
def fullDecomposition (F : Pattern) :
    DepthDecomposition F 1 (Fintype.card F.A + Fintype.card F.B) where
  Node := Bool
  root := false
  parent := fun _ => false
  parent_root := rfl
  depth_le := fun _ => rfl
  bag := fun t => if t then Finset.univ else ∅
  bag_root := rfl
  card_bag_le := fun t => by
    cases t <;> simp [Finset.card_univ, Fintype.card_sum]
  exists_mem_bag := fun v => ⟨true, by simp⟩
  exists_edge_mem_bag := fun a b _ => ⟨true, by simp⟩
  connected := fun v t t' h _ h' _ => by
    cases t <;> cases t' <;> simp_all

/-- A pattern with at most `n` vertices on each side has treewidth at most `2n`. -/
theorem treewidthLE_two_mul {F : Pattern} {n : ℕ}
    (hA : Fintype.card F.A ≤ n) (hB : Fintype.card F.B ≤ n) : TreewidthLE (2 * n) F :=
  Lax461425.TreewidthForestwidth.treewidthLE_of_forestwidthLE (Δ := 1)
    ⟨(fullDecomposition F).card_bag_le |> fun h =>
      { fullDecomposition F with card_bag_le := fun t => (h t).trans (by omega) }⟩

/-- The pattern without vertices. -/
def emptyPattern : Pattern where
  A := Empty
  B := Empty
  mult := fun a _ => a.elim

theorem treewidthLE_emptyPattern (w : ℕ) : TreewidthLE w emptyPattern :=
  treewidthLE_mono (Nat.zero_le w)
    (treewidthLE_two_mul (n := 0) (Fintype.card_eq_zero (α := Empty)).le
      (Fintype.card_eq_zero (α := Empty)).le)

theorem hom_emptyPattern (K : Type*) [CommSemiring K] (n : ℕ) :
    hom K emptyPattern n = 1 := by
  show (∑ hA : Empty → Fin n, ∑ hB : Empty → Fin n, _) = 1
  rw [Fintype.sum_unique, Fintype.sum_unique]
  have : IsEmpty emptyPattern.A := inferInstanceAs (IsEmpty Empty)
  exact Fintype.prod_empty _

/-- Homomorphism polynomials are invariant under row and column permutations. -/
theorem hom_matrixInvariant (K : Type*) [CommSemiring K] (F : Pattern) (n : ℕ) :
    MatrixInvariant (hom K F n) := by
  intro γ
  simp only [hom, map_sum, map_prod, map_pow, MvPolynomial.rename_X]
  refine Fintype.sum_equiv (Equiv.piCongrRight fun _ : F.A => γ.1) _ _ fun hA => ?_
  exact Fintype.sum_equiv (Equiv.piCongrRight fun _ : F.B => γ.2) _ _ fun hB => rfl

/-- Linear combinations of matrix-invariant polynomials are matrix-invariant. -/
theorem matrixInvariant_of_mem_span {K : Type*} [CommSemiring K] {n : ℕ}
    {S : Set (MatrixPolynomial n K)} (hS : ∀ q ∈ S, MatrixInvariant q)
    {p : MatrixPolynomial n K} (hp : p ∈ Submodule.span K S) : MatrixInvariant p := by
  intro γ
  induction hp using Submodule.span_induction with
  | mem x hx => exact hS x hx γ
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [MvPolynomial.rename, map_smul, ← MvPolynomial.rename, hx]

/-- Every polynomial in the empty matrix is a multiple of a homomorphism polynomial of the
empty pattern. -/
theorem mem_span_zero {K : Type*} [CommSemiring K] (w : ℕ) (p : MatrixPolynomial 0 K) :
    p ∈ Submodule.span K {q | ∃ F : Pattern, TreewidthLE w F ∧ hom K F 0 = q} := by
  have hmem : hom K emptyPattern 0 ∈
      Submodule.span K {q | ∃ F : Pattern, TreewidthLE w F ∧ hom K F 0 = q} :=
    Submodule.subset_span ⟨_, treewidthLE_emptyPattern w, rfl⟩
  have h := Submodule.smul_mem _ (p.coeff 0) hmem
  rw [hom_emptyPattern, MvPolynomial.smul_eq_C_mul, mul_one, ← p.eq_C_of_isEmpty] at h
  exact h

end Lax461425Proofs.SymVPWidths
