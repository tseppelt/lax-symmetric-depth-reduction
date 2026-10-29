import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Find

/-!
Generic facts about a "rooted tree" given by a parent function with a uniform depth bound:
if `parent root = root` and `parent^[Δ] t = root` for every `t`, then every node has a
well-defined `level` (its distance to the root), with `level root = 0` and
`level t = level (parent t) + 1` for `t ≠ root`, and `level t ≤ Δ` for every `t`.

This is used twice: for the tree underlying a given `DepthDecomposition`, and for the
contracted tree built from it.
-/

namespace Lax461425Proofs

open Classical

variable {Node : Type*} {Δ : ℕ} {parent : Node → Node} {root : Node}

/-- The set of iteration counts that reach the root from `t`, used to define `level`. -/
private theorem exists_iterate_eq_root (hdepth : ∀ t, parent^[Δ] t = root) (t : Node) :
    ∃ j, parent^[j] t = root :=
  ⟨Δ, hdepth t⟩

/-- The distance from `t` to the root along `parent`: the least `j` with `parent^[j] t = root`.
-/
noncomputable def level (hdepth : ∀ t, parent^[Δ] t = root) (t : Node) : ℕ :=
  Nat.find (exists_iterate_eq_root hdepth t)

variable (hdepth : ∀ t, parent^[Δ] t = root)

theorem iterate_level (t : Node) : parent^[level hdepth t] t = root :=
  Nat.find_spec (exists_iterate_eq_root hdepth t)

theorem level_le (t : Node) : level hdepth t ≤ Δ :=
  Nat.find_le (hdepth t)

theorem level_eq_zero_iff (hroot : parent root = root) (t : Node) :
    level hdepth t = 0 ↔ t = root := by
  constructor
  · intro h
    have := iterate_level hdepth t
    rwa [h, Function.iterate_zero_apply] at this
  · rintro rfl
    exact Nat.le_zero.mp (Nat.find_le (by simp))

theorem level_eq_zero_of_eq_root (hroot : parent root = root) : level hdepth root = 0 :=
  (level_eq_zero_iff hdepth hroot root).mpr rfl

/-- For `t ≠ root`, the level of `t` is one more than the level of its parent. -/
theorem level_succ (hroot : parent root = root) {t : Node} (ht : t ≠ root) :
    level hdepth t = level hdepth (parent t) + 1 := by
  have hle : level hdepth t ≤ level hdepth (parent t) + 1 := by
    apply Nat.find_le
    rw [Function.iterate_succ_apply]
    exact iterate_level hdepth (parent t)
  have hpos : 0 < level hdepth t := by
    rcases Nat.eq_zero_or_pos (level hdepth t) with h0 | hpos
    · exact absurd ((level_eq_zero_iff hdepth hroot t).mp h0) ht
    · exact hpos
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  have hj' : parent^[j] (parent t) = root := by
    have heq := iterate_level hdepth t
    rw [hj, Function.iterate_succ_apply] at heq
    exact heq
  have hge : level hdepth (parent t) ≤ j := Nat.find_le hj'
  omega

/-- The level strictly decreases when passing from a non-root node to its parent. -/
theorem level_parent_lt (hroot : parent root = root) {t : Node} (ht : t ≠ root) :
    level hdepth (parent t) < level hdepth t := by
  rw [level_succ hdepth hroot ht]; omega

/-- If a measure `μ` strictly decreases under `f` away from a fixed point `x0` (and vanishes
at `x0`), then `f^[n] x = x0` as soon as `n ≥ μ x`. Used to transfer depth bounds along
contracted trees, whose "level" measure is only known to decrease, not to be computed by a
literal distance-to-root formula. -/
theorem iterate_eq_of_measure_decreasing {X : Type*} (f : X → X) (x0 : X) (μ : X → ℕ)
    (hx0 : f x0 = x0) (hμ0 : μ x0 = 0) (hdec : ∀ x, x ≠ x0 → μ (f x) < μ x) :
    ∀ {n : ℕ} {x : X}, μ x ≤ n → f^[n] x = x0 := by
  have hz : ∀ x, μ x = 0 → x = x0 := by
    intro x hx
    by_contra hne
    have := hdec x hne
    omega
  intro n
  induction n with
  | zero => intro x hx; exact hz x (Nat.le_zero.mp hx)
  | succ n ih =>
      intro x hx
      by_cases hex : x = x0
      · subst hex; exact Function.iterate_fixed hx0 (n + 1)
      · have hlt : μ (f x) < μ x := hdec x hex
        have hle : μ (f x) ≤ n := by omega
        rw [Function.iterate_succ_apply]
        exact ih hle

end Lax461425Proofs
