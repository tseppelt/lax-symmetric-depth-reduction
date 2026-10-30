import Lax461425Proofs.DepthHierarchyRichDefs
import Lax461425.NonUniformClosure
import Lax461425.Forestwidth
import Lax461425.Oddomorphisms

/-!
Statements (all `sorry`) of the lemmas in the proof of the first assertion of the depth hierarchy
theorem. Each is proved in its own module `DepthHierarchy*.lean` under the same namespace with the
same name and statement.
-/

namespace Lax461425Proofs.DepthHierarchy

open Lax461425 Lax461425.Forestwidth Lax461425.NonUniformClosure Lax461425.Oddomorphisms
  Lax461425.HomomorphismPolynomials Lax68.GraphMinors

/-- Richness is invariant under isomorphism. -/
theorem isRich_iso {V W : Type} {F : SimpleGraph V} {G : SimpleGraph W} (e : F ≃g G) {k Δ : ℕ} :
    IsRich F k Δ ↔ IsRich G k Δ := by
  sorry

/-- Richness passes from a minor to the graph (for `k ≥ 1`... any `k`). -/
theorem isRich_of_isMinor {V W : Type} {G : SimpleGraph W} {F : SimpleGraph V}
    (h : IsMinor G F) {k Δ : ℕ} (hG : IsRich G k Δ) : IsRich F k Δ := by
  sorry

/-- A pattern whose underlying graph is `(Δ,k)`-rich has `Δ`-forestwidth `≥ k`. -/
theorem not_forestwidthLE_of_isRich {P : Pattern} {k Δ : ℕ} (hk : 1 ≤ k) (hΔ : 1 ≤ Δ)
    (h : IsRich (underlying P) k Δ) : ¬ ForestwidthLE Δ (k - 1) P := by
  sorry

/-- Oddomorphisms (even weak) reflect richness. -/
theorem isRich_of_weakOddomorphism {V W : Type} [Finite V] [Finite W] {F : SimpleGraph V}
    {G : SimpleGraph W} (φ : F →g G) (hφ : IsWeakOddomorphism φ) {k Δ : ℕ}
    (hG : IsRich G k Δ) : IsRich F k Δ := by
  sorry

/-- A rich graph (with `k ≥ 1`) has at least two vertices... so `K₁` is not rich. -/
theorem not_isRich_bot {k Δ : ℕ} (hk : 1 ≤ k) : ¬ IsRich (⊥ : SimpleGraph (Fin 1)) k Δ := by
  sorry

theorem treeG_connected (Δ m : ℕ) : (treeG Δ m).Connected := by
  sorry

theorem treeG_richSet (Δ k : ℕ) : RichSet (treeG (Δ + 1) (k + 1)) k Δ Set.univ := by
  sorry

theorem treeG_isMinor {Δ k n : ℕ} (h : k + 1 ≤ n) :
    IsMinor (treeG Δ (k + 1)) (underlying (DepthHierarchy.fullTree Δ n)) := by
  sorry

theorem cfiSize_treeG_le {Δ k : ℕ} (hΔ : 1 ≤ Δ) (hk : 1 ≤ k) :
    cfiSize (treeG Δ (k + 1)) ≤ 2 ^ (k + 3) * (k + 1) ^ (Δ - 1) := by
  sorry

/-- The final numerical estimate: if an orbit size `O` is at least `C(n, k+1)` for every `k ≥ 2`
with `4(k+1) ≤ n` and `2^(k+3) (k+1)^(Δ-1) ≤ n`, then `O ≥ n^(log₂ n - Δ log₂ log₂ n - 3)`. -/
theorem arith {Δ n O : ℕ} (hΔ : 1 ≤ Δ) (hn : 20 ≤ n)
    (h : ∀ k, 2 ≤ k → 4 * (k + 1) ≤ n → 2 ^ (k + 3) * (k + 1) ^ (Δ - 1) ≤ n →
      n.choose (k + 1) ≤ O) :
    (n : ℝ) ^ (Real.logb 2 n - Δ * Real.logb 2 (Real.logb 2 n) - 3) ≤ O := by
  sorry

end Lax461425Proofs.DepthHierarchy
