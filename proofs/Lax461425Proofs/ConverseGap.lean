import Lax461425Proofs.ConverseLevel

/-!
A "gap-free" lemma for subsets of a rooted tree satisfying the single-exit-point
connectivity condition used by `DepthDecomposition.connected` (and by our own normalised
decompositions): if `U` holds at a node `d` and at an ancestor `parent^[j] d`, it holds at
every node strictly in between. This is the key combinatorial fact needed to transfer tree
decomposition data through the contractions performed in `ConverseDecomposition.lean`.
-/

namespace Lax461425Proofs

open Classical

variable {Node : Type*} {Δ : ℕ} {parent : Node → Node} {root : Node}
variable (hdepth : ∀ t, parent^[Δ] t = root) (hroot : parent root = root)

include hdepth hroot

theorem level_iterate {d : Node} {i : ℕ} (hi : i ≤ level hdepth d) :
    level hdepth (parent^[i] d) = level hdepth d - i := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hi' : i ≤ level hdepth d := Nat.le_of_succ_le hi
      have hlt : i < level hdepth d := hi
      have hlevel_e : level hdepth (parent^[i] d) = level hdepth d - i := ih hi'
      have hpos : 0 < level hdepth (parent^[i] d) := by omega
      have hene : parent^[i] d ≠ root := by
        intro h
        rw [h, level_eq_zero_of_eq_root hdepth hroot] at hlevel_e
        omega
      have hstep : level hdepth (parent^[i] d) = level hdepth (parent (parent^[i] d)) + 1 :=
        level_succ hdepth hroot hene
      have heq : parent^[i + 1] d = parent (parent^[i] d) := Function.iterate_succ_apply' _ _ _
      rw [heq]
      omega

/-- Beyond the level of `d`, iterating `parent` stays at the root. -/
theorem iterate_eq_root_of_le_level {d : Node} {j : ℕ} (hj : level hdepth d ≤ j) :
    parent^[j] d = root := by
  have hr : j = (j - level hdepth d) + level hdepth d := by omega
  rw [hr, Function.iterate_add_apply, iterate_level hdepth]
  exact Function.iterate_fixed hroot _

/-- If a node has an ancestor satisfying `U`, that ancestor's level is at most the node's
level: beyond that, iterating `parent` reaches the root, where `U` fails. -/
theorem le_level_of_holds {U : Node → Prop} (hUroot : ¬ U root) {d : Node} {j : ℕ}
    (hj : U (parent^[j] d)) : j ≤ level hdepth d := by
  by_contra hcon
  push_neg at hcon
  exact hUroot (iterate_eq_root_of_le_level hdepth hroot (le_of_lt hcon) ▸ hj)

omit hroot in
/-- `level hdepth d` is itself a witness that iterating `parent` from `d` eventually leaves
any `U` not containing the root. -/
private theorem exists_not_holds {U : Node → Prop} (hUroot : ¬ U root) (d : Node) :
    ∃ i, ¬ U (parent^[i] d) :=
  ⟨Δ, hdepth d ▸ hUroot⟩

/-- The first node, going up from `d`, where `U` fails: it is an honest exit point, within
`level hdepth d` steps of `d`, and `U` holds at every node strictly closer to `d` (inclusive)
along this chain. -/
theorem exists_exit {U : Node → Prop} (hUroot : ¬ U root) (d : Node) (hd : U d) :
    ∃ t0 m, U t0 ∧ ¬ U (parent t0) ∧ m ≤ level hdepth d ∧ parent^[m] d = t0 ∧
      ∀ k ≤ m, U (parent^[k] d) := by
  have hex := exists_not_holds hdepth hUroot d
  have hqle : Nat.find hex ≤ level hdepth d := by
    apply Nat.find_le
    rw [iterate_level hdepth]
    exact hUroot
  have hqpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · exfalso
      have hq0 : ¬ U (parent^[0] d) := h0 ▸ Nat.find_spec hex
      rw [Function.iterate_zero_apply] at hq0
      exact hq0 hd
    · exact hpos
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hqpos)
  have hmin : ∀ k ≤ m, U (parent^[k] d) := by
    intro k hk
    have hklt : k < Nat.find hex := by omega
    exact not_not.mp (Nat.find_min hex hklt)
  have hUm : U (parent^[m] d) := hmin m le_rfl
  have hUm' : ¬ U (parent (parent^[m] d)) := by
    have heq : parent (parent^[m] d) = parent^[m + 1] d := (Function.iterate_succ_apply' _ _ _).symm
    rw [heq]
    have hspec := Nat.find_spec hex
    rw [hm] at hspec
    exact hspec
  exact ⟨parent^[m] d, m, hUm, hUm', by omega, rfl, hmin⟩

/-- **Gap-free lemma.** If `U` holds at `d` and at an ancestor `parent^[j] d`, it holds at
every node strictly in between. -/
theorem gap_free {U : Node → Prop} (hUroot : ¬ U root)
    (hconn : ∀ t t', U t → ¬ U (parent t) → U t' → ¬ U (parent t') → t = t')
    {d : Node} (hd : U d) {j : ℕ} (hj : U (parent^[j] d)) {i : ℕ} (hij : i ≤ j) :
    U (parent^[i] d) := by
  obtain ⟨t0, m0, hUt0, hUt0', hm0le, hm0, hmin0⟩ := exists_exit hdepth hroot hUroot d hd
  obtain ⟨t1, m1, hUt1, hUt1', hm1le, hm1, hmin1⟩ := exists_exit hdepth hroot hUroot (parent^[j] d) hj
  have ht01 : t0 = t1 := hconn t0 t1 hUt0 hUt0' hUt1 hUt1'
  have hjled : j ≤ level hdepth d := le_level_of_holds hdepth hroot hUroot hj
  have hm1' : parent^[m1 + j] d = t1 := by
    rw [Function.iterate_add_apply]; exact hm1
  have hlevelanc : level hdepth (parent^[j] d) = level hdepth d - j := level_iterate hdepth hroot hjled
  have hm1le' : m1 + j ≤ level hdepth d := by
    have hm1le2 : m1 ≤ level hdepth (parent^[j] d) := hm1le
    omega
  have hlev0 : level hdepth t0 = level hdepth d - m0 := hm0 ▸ level_iterate hdepth hroot hm0le
  have hlev1 : level hdepth t1 = level hdepth d - (m1 + j) := hm1' ▸ level_iterate hdepth hroot hm1le'
  have heqpos : m0 = m1 + j := by
    have heqlev : level hdepth d - m0 = level hdepth d - (m1 + j) := by
      rw [← hlev0, ← hlev1, ht01]
    omega
  exact hmin0 i (by omega)

end Lax461425Proofs
