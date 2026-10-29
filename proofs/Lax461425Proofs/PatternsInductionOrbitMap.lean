import Lax461425Proofs.PatternsInductionNidx
import Lax461425Proofs.PatternsInductionTransitive
import Lax461425Proofs.PatternsRestrictedY

/-!
The **`h_y` construction** for `lem:induction`'s internal-gate case: given a gate `g`, a child
`h` of `g`, and a pair `(y, z) ∈ Y_u` (the paper's `Y(vec{sup}(g))`, i.e.
`PatternsRestrictedY.Y` at the sizes of `N`'s two sides), we build the sibling gate `h_y`
obtained by transporting `h` along *any* `γ ∈ fixingSubgroup (Γ n) (supOf hrig hn g)` sending
the real `N`-tuple to `(y, z)` (which exists by `PatternsInductionTransitive`'s transitivity
lemma). The construction does not depend on the choice of `γ` (`σOf_eq_of_both_valid`), since
two valid choices differ by an element of `fixingSubgroup (Γ n) (sup g ∪ N) ≤ gateStabilizer
hrig h` (as `sup h ⊆ sup g ∪ N` always, and `fixingSubgroup` is antitone in its `Set` argument).

This file supplies `hYtot`, a *total* function on all pairs `(y, z)` (not just those in `Y_u`,
for convenience: an arbitrary default value is returned outside `Y_u`), together with its
defining property `hYtot_eq_of_valid`: for any valid `γ`, `hYtot (y, z) = σOf hrig γ h`.
-/

namespace Lax461425Proofs.PatternsInductionOrbitMap

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open Lax461425Proofs.PatternsSupportDepth Lax461425Proofs.PatternsInductionSetup
open Lax461425Proofs.PatternsInductionNidx Lax461425Proofs.PatternsInductionTransitive
open Lax461425Proofs.PatternsRestrictedY
open scoped Classical

variable {K : Type*} [Field K] {n : ℕ} {C : Circuit (Fin n × Fin n) K}
variable (hrig : IsRigid C) (hn : 2 * supportSize C < n) {g h : C.Gate}

/-! ### Existence of a valid `γ` -/

omit [Field K] in
/-- **Existence of a valid `γ`.** For `(y, z) ∈ Y_u`, there is `γ ∈ fixingSubgroup (Γ n) (sup g)`
sending the real `N`-tuple `(yReal, yReal)` to `(y, z)`. -/
theorem exists_γ_of_mem_Y
    {y : Fin (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h)) → Fin n}
    {z : Fin (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) → Fin n}
    (hmem : (y, z) ∈ Y _ _ n (leftEnum hrig hn g) (rightEnum hrig hn g)) :
    ∃ γ : Γ n, γ ∈ fixingSubgroup (Γ n) (supOf hrig hn g) ∧
      γ.1 ∘ (yReal (leftEnum hrig hn g) (leftEnum hrig hn h)) = y ∧
      γ.2 ∘ (yReal (rightEnum hrig hn g) (rightEnum hrig hn h)) = z := by
  obtain ⟨hinjY, hinjZ⟩ := mem_Y.mp hmem
  obtain ⟨-, hyinj, hycross⟩ := Fin.append_injective_iff.mp hinjY
  obtain ⟨-, hzinj, hzcross⟩ := Fin.append_injective_iff.mp hinjZ
  have hyRealinj : Function.Injective (yReal (leftEnum hrig hn g) (leftEnum hrig hn h)) :=
    yReal_injective (leftEnum_injective hrig hn h)
  have hzRealinj : Function.Injective (yReal (rightEnum hrig hn g) (rightEnum hrig hn h)) :=
    yReal_injective (rightEnum_injective hrig hn h)
  have hyRealdisj : ∀ k, yReal (leftEnum hrig hn g) (leftEnum hrig hn h) k
      ∉ leftPart (supOf hrig hn g) := by
    intro k hk
    rw [← range_leftEnum] at hk
    exact yReal_disjoint_v k hk
  have hzRealdisj : ∀ k, yReal (rightEnum hrig hn g) (rightEnum hrig hn h) k
      ∉ rightPart (supOf hrig hn g) := by
    intro k hk
    rw [← range_rightEnum] at hk
    exact yReal_disjoint_v k hk
  have hydisj : ∀ k, y k ∉ leftPart (supOf hrig hn g) := by
    intro k hk
    rw [← range_leftEnum] at hk
    obtain ⟨i, hi⟩ := hk
    exact hycross i k hi
  have hzdisj : ∀ k, z k ∉ rightPart (supOf hrig hn g) := by
    intro k hk
    rw [← range_rightEnum] at hk
    obtain ⟨j, hj⟩ := hk
    exact hzcross j k hj
  obtain ⟨γ, hγmem, hγy, hγz⟩ := exists_fixing_Γ_of_notMem hyRealinj hyinj hzRealinj hzinj
    hyRealdisj hydisj hzRealdisj hzdisj
  exact ⟨γ, hγmem, funext hγy, funext hγz⟩

/-! ### Well-definedness: any two valid `γ`'s give the same `σOf hrig γ h` -/

/-- The pointwise stabiliser of a superset is a subgroup of that of a subset. -/
theorem fixingSubgroup_mono {S T : Set (Fin n ⊕ Fin n)} (hST : S ⊆ T) :
    fixingSubgroup (Γ n) T ≤ fixingSubgroup (Γ n) S := by
  intro γ hγ
  rw [mem_fixingSubgroup_iff] at hγ ⊢
  intro x hx
  exact hγ x (hST hx)

omit [Field K] in
theorem sup_subset_sup_union_N :
    supOf hrig hn h ⊆ supOf hrig hn g ∪
      (Sum.inl '' Set.range (yReal (leftEnum hrig hn g) (leftEnum hrig hn h)) ∪
        Sum.inr '' Set.range (yReal (rightEnum hrig hn g) (rightEnum hrig hn h))) := by
  intro x hx
  cases x with
  | inl i =>
      have hi : i ∈ leftPart (supOf hrig hn h) := hx
      rw [← range_leftEnum] at hi
      by_cases hmem : i ∈ Set.range (leftEnum hrig hn g)
      · exact Or.inl (show Sum.inl i ∈ supOf hrig hn g from by rw [range_leftEnum] at hmem; exact hmem)
      · have : i ∈ Set.range (yReal (leftEnum hrig hn g) (leftEnum hrig hn h)) := by
          rw [range_yReal]; exact ⟨hi, hmem⟩
        exact Or.inr (Or.inl ⟨i, this, rfl⟩)
  | inr j =>
      have hj : j ∈ rightPart (supOf hrig hn h) := hx
      rw [← range_rightEnum] at hj
      by_cases hmem : j ∈ Set.range (rightEnum hrig hn g)
      · exact Or.inl (show Sum.inr j ∈ supOf hrig hn g from by rw [range_rightEnum] at hmem; exact hmem)
      · have : j ∈ Set.range (yReal (rightEnum hrig hn g) (rightEnum hrig hn h)) := by
          rw [range_yReal]; exact ⟨hj, hmem⟩
        exact Or.inr (Or.inr ⟨j, this, rfl⟩)

end Lax461425Proofs.PatternsInductionOrbitMap
