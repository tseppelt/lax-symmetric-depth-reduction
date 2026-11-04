import Lax461425Proofs.SymmetricPathDecomposition

/-!
The combinatorial core of the path-decomposition ABP: assignments to adjacent bags
agreeing on their intersection are equivalent to a single assignment of all vertices.
This includes isolated vertices and does not discard bags that introduce several vertices.
-/

namespace Lax461425Proofs.SymmetricPathAssignments

open Lax461425.SymmetricABPs Lax461425.HomomorphismPolynomials

variable {F : Pattern} {k : ℕ} (D : PaddedPathDecomposition F k) (n : ℕ)

abbrev BagAssignment (i : Fin (D.length + 1)) := {v // v ∈ D.bag i} → Fin n

/-- Agreement on consecutive bag intersections. -/
def Compatible (a : ∀ i, BagAssignment D n i) : Prop :=
  ∀ (i : Fin D.length) (v : F.A ⊕ F.B) (hi : v ∈ D.bag i.castSucc)
    (hj : v ∈ D.bag i.succ), a i.castSucc ⟨v, hi⟩ = a i.succ ⟨v, hj⟩

abbrev CompatibleAssignments := {a : ∀ i, BagAssignment D n i // Compatible D n a}

/-- Consecutive compatibility implies agreement anywhere in a vertex's interval. -/
theorem compatible_eq {a : ∀ i, BagAssignment D n i} (ha : Compatible D n a)
    (v : F.A ⊕ F.B) {i j : Fin (D.length + 1)}
    (hi : v ∈ D.bag i) (hj : v ∈ D.bag j) : a i ⟨v, hi⟩ = a j ⟨v, hj⟩ := by
  suffices h : ∀ (r s : ℕ) (hr : r ≤ D.length) (hs : s ≤ D.length),
      r ≤ s → ∀ (hvr : v ∈ D.bag ⟨r, by omega⟩)
        (hvs : v ∈ D.bag ⟨s, by omega⟩),
      a ⟨r, by omega⟩ ⟨v, hvr⟩ = a ⟨s, by omega⟩ ⟨v, hvs⟩ by
    rcases le_total i.val j.val with hij | hji
    · exact h i.val j.val (by omega) (by omega) hij hi hj
    · exact (h j.val i.val (by omega) (by omega) hji hj hi).symm
  intro r s
  induction s with
  | zero =>
    intro hr hs hrs hvr hvs
    have : r = 0 := by omega
    subst r
    rfl
  | succ s ih =>
    intro hr hs hrs hvr hvs
    by_cases hEq : r = s + 1
    · subst r
      rfl
    · have hrs' : r ≤ s := by omega
      have hv : v ∈ D.bag ⟨s, by omega⟩ :=
        D.interval v ⟨r, by omega⟩ ⟨s, by omega⟩ ⟨s + 1, by omega⟩
          hrs' (by change s ≤ s + 1; omega) hvr hvs
      exact (ih hr (by omega) hrs' hvr hv).trans (ha ⟨s, by omega⟩ v hv hvs)

/-- Restrict a global vertex assignment to every bag. -/
def restrict (h : F.A ⊕ F.B → Fin n) : CompatibleAssignments D n :=
  ⟨fun _ v => h v.val, fun _ _ _ _ => rfl⟩

theorem restrict_injective : Function.Injective (restrict D n) := by
  intro h g hhg
  funext v
  obtain ⟨i, hi⟩ := D.covers_vertex v
  exact congrArg (fun a : CompatibleAssignments D n => a.1 i ⟨v, hi⟩) hhg

/-- Extend compatible bag assignments to all vertices by selecting any containing bag. -/
noncomputable def extend (a : CompatibleAssignments D n) : F.A ⊕ F.B → Fin n :=
  fun v => a.1 (Classical.choose (D.covers_vertex v))
    ⟨v, Classical.choose_spec (D.covers_vertex v)⟩

theorem extend_apply (a : CompatibleAssignments D n) (i : Fin (D.length + 1))
    (v : F.A ⊕ F.B) (hi : v ∈ D.bag i) : extend D n a v = a.1 i ⟨v, hi⟩ :=
  compatible_eq D n a.2 v (Classical.choose_spec (D.covers_vertex v)) hi

theorem restrict_extend (a : CompatibleAssignments D n) : restrict D n (extend D n a) = a := by
  apply Subtype.ext
  funext i v
  exact extend_apply D n a i v.val v.property

/-- The path-state choices of a decomposition are exactly global vertex maps. -/
noncomputable def assignmentEquiv : (F.A ⊕ F.B → Fin n) ≃ CompatibleAssignments D n where
  toFun := restrict D n
  invFun := extend D n
  left_inv h := restrict_injective D n (restrict_extend D n (restrict D n h))
  right_inv := restrict_extend D n

/-- The state count of each bag is controlled by the pathwidth. -/
theorem card_bagAssignment_le (hn : 1 ≤ n) (i : Fin (D.length + 1)) :
    Fintype.card (BagAssignment D n i) ≤ n ^ (k + 1) := by
  classical
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  exact Nat.pow_le_pow_right hn (D.card_bag_le i)

end Lax461425Proofs.SymmetricPathAssignments
