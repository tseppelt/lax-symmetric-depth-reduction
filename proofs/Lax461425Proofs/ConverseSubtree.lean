import Lax461425Proofs.ConverseCorrectness

/-!
The vertex set `V t` of the subtree rooted at a node `t` of a `NormDecomp`: the union of the
bags of `t` and all its descendants. This file sets up `Above` (descendant-or-self, via
iterating `parent`), proves that `Above` is canonically witnessed by the level difference
(`above_iterate_level_sub`), defines `V`, and proves the two independence facts needed to glue
admissible maps on `V t` from admissible maps on each child's `V c`:

* `V_inter_bag_eq_of_parent`: for a child `c` of `t`, `V c ∩ bag t = bag c ∩ bag t`.
* `V_inter_V_subset_bag`: for distinct children `c, c'` of `t`, `V c ∩ V c' ⊆ bag t`.

Both are proved from `NormDecomp.connected` via the "gap-free"/"single exit point" structure of
`ConverseGap.lean`, specialised using the canonical level-indexed ancestor.
-/

namespace Lax461425Proofs

open Classical Lax461425.HomomorphismPolynomials Lax461425.Forestwidth

variable {F : Pattern} {Δ k : ℕ}

section Above

variable (N : NormDecomp F Δ k)

/-- `t'` is `t` or a descendant of `t`: iterating `parent` from `t'` eventually reaches `t`. -/
def Above (t' t : N.Node) : Prop := ∃ m, N.parent^[m] t' = t

theorem above_self (t : N.Node) : Above N t t := ⟨0, rfl⟩

theorem above_trans {t'' t' t : N.Node} (h1 : Above N t'' t') (h2 : Above N t' t) :
    Above N t'' t := by
  obtain ⟨m1, hm1⟩ := h1
  obtain ⟨m2, hm2⟩ := h2
  exact ⟨m2 + m1, by rw [Function.iterate_add_apply, hm1, hm2]⟩

theorem above_of_parent_eq {t' t : N.Node} (h : N.parent t' = t) : Above N t' t :=
  ⟨1, by simpa using h⟩

/-- Along `Above N t' t`, the level of `t` is at most the level of `t'`: iterating `parent`
never increases the level. -/
theorem level_above_le {t' t : N.Node} (h : Above N t' t) :
    level N.depth_le t ≤ level N.depth_le t' := by
  obtain ⟨m, hm⟩ := h
  by_cases hmle : m ≤ level N.depth_le t'
  · rw [← hm, level_iterate N.depth_le N.parent_root hmle]; omega
  · push_neg at hmle
    rw [← hm, show m = (m - level N.depth_le t') + level N.depth_le t' by omega,
      Function.iterate_add_apply, iterate_level N.depth_le t', Function.iterate_fixed N.parent_root]
    simp [level_eq_zero_of_eq_root N.depth_le N.parent_root]

/-- `Above N t' t` is canonically witnessed by the level difference: whichever exponent
witnesses it, iterating `parent` by exactly `level t' - level t` steps from `t'` reaches `t`.
This is the key fact making the ancestor at a given level unique. -/
theorem above_iterate_level_sub {t' t : N.Node} (h : Above N t' t) :
    N.parent^[level N.depth_le t' - level N.depth_le t] t' = t := by
  obtain ⟨m, hm⟩ := h
  by_cases hmle : m ≤ level N.depth_le t'
  · have hlevel_t : level N.depth_le t = level N.depth_le t' - m := by
      rw [← hm]; exact level_iterate N.depth_le N.parent_root hmle
    rw [show level N.depth_le t' - level N.depth_le t = m by omega, hm]
  · push_neg at hmle
    have hm' : N.parent^[m] t' = t := hm
    rw [show m = (m - level N.depth_le t') + level N.depth_le t' by omega,
      Function.iterate_add_apply, iterate_level N.depth_le t',
      Function.iterate_fixed N.parent_root] at hm'
    have hteq : t = N.root := hm'.symm
    subst hteq
    rw [level_eq_zero_of_eq_root N.depth_le N.parent_root, Nat.sub_zero]
    exact iterate_level N.depth_le t'

/-- If `t' ≠ t` and `t` is an ancestor-or-self of `t'`, then `t` is a strict ancestor: its
level is strictly smaller. -/
theorem level_lt_of_above_ne {t' t : N.Node} (h : Above N t' t) (hne : t' ≠ t) :
    level N.depth_le t < level N.depth_le t' := by
  rcases lt_or_eq_of_le (level_above_le N h) with hlt | heq
  · exact hlt
  · exfalso
    have hcanon := above_iterate_level_sub N h
    rw [heq, Nat.sub_self, Function.iterate_zero_apply] at hcanon
    exact hne hcanon

/-- If `s` reaches `e` after exactly `m0 ≤ level s` steps, `s` is a descendant-or-self of `w`,
and `level w ≤ level e`, then `e` is a descendant-or-self of `w` too: `e` lies on the segment of
the unique path from `s` to the root that is at or above `w`. -/
theorem above_of_ge_level {s w e : N.Node} (hAsw : Above N s w) {m0 : ℕ}
    (hm0le : m0 ≤ level N.depth_le s) (he : N.parent^[m0] s = e)
    (hle : level N.depth_le w ≤ level N.depth_le e) : Above N e w := by
  have hcanon : N.parent^[level N.depth_le s - level N.depth_le w] s = w :=
    above_iterate_level_sub N hAsw
  have hlevel_e : level N.depth_le e = level N.depth_le s - m0 := by
    rw [← he]; exact level_iterate N.depth_le N.parent_root hm0le
  have hwle : level N.depth_le w ≤ level N.depth_le s := level_above_le N hAsw
  have hm0_le_dw : m0 ≤ level N.depth_le s - level N.depth_le w := by omega
  refine ⟨level N.depth_le s - level N.depth_le w - m0, ?_⟩
  rw [← he, ← Function.iterate_add_apply,
    show level N.depth_le s - level N.depth_le w - m0 + m0 = level N.depth_le s - level N.depth_le w
      by omega, hcanon]

end Above

section SubtreeSet

variable (N : NormDecomp F Δ k)

/-- The vertex set of the subtree rooted at `t`: the union of the bags of `t` and all its
descendants. -/
noncomputable def V (t : N.Node) : Finset (F.A ⊕ F.B) :=
  (Finset.univ.filter (fun t' => Above N t' t)).biUnion N.bag

theorem mem_V {t : N.Node} {v : F.A ⊕ F.B} :
    v ∈ V N t ↔ ∃ t', Above N t' t ∧ v ∈ N.bag t' := by
  simp [V, Finset.mem_biUnion]

theorem bag_subset_V (t : N.Node) : N.bag t ⊆ V N t :=
  fun v hv => (mem_V N).mpr ⟨t, above_self N t, hv⟩

theorem V_subset_of_above {t' t : N.Node} (h : Above N t' t) : V N t' ⊆ V N t :=
  fun v hv => by
    obtain ⟨s, hs, hvs⟩ := (mem_V N).mp hv
    exact (mem_V N).mpr ⟨s, above_trans N hs h, hvs⟩

/-- The subtree of a child is contained in the subtree of its parent. -/
theorem V_subset_of_child {t c : N.Node} (hp : N.parent c = t) : V N c ⊆ V N t :=
  V_subset_of_above N (above_of_parent_eq N hp)

end SubtreeSet

section Independence

variable (N : NormDecomp F Δ k)

/-- **Independence fact (b).** For a child `c` of `t`, the part of `c`'s subtree lying in `t`'s
bag is exactly the overlap of the two bags: `V c ∩ bag t = bag c ∩ bag t`. Proved via the
"gap-free" lemma of `ConverseGap.lean`. -/
theorem V_inter_bag_eq_of_parent {t : N.Node} {c : NonRoot N} (hp : N.parent c.1 = t) :
    V N c.1 ∩ N.bag t = N.bag c.1 ∩ N.bag t := by
  apply Finset.Subset.antisymm
  · intro v hv
    simp only [Finset.mem_inter] at hv ⊢
    obtain ⟨hvc, hvt⟩ := hv
    obtain ⟨t', hAbove, hv'⟩ := (mem_V N).mp hvc
    obtain ⟨m, hm⟩ := hAbove
    have hj : (fun s => v ∈ N.bag s) (N.parent^[m + 1] t') := by
      rw [Function.iterate_succ_apply', hm, hp]; exact hvt
    have hres := gap_free N.depth_le N.parent_root (U := fun s => v ∈ N.bag s)
      (by rw [N.bag_root]; simp) (N.connected v) hv' hj (i := m) (by omega)
    rw [hm] at hres
    exact ⟨hres, hvt⟩
  · intro v hv
    simp only [Finset.mem_inter] at hv ⊢
    exact ⟨bag_subset_V N c.1 hv.1, hv.2⟩

/-- **Independence fact (a).** For two *distinct* children `c, c'` of `t`, the two subtrees can
only overlap inside `t`'s bag: `V c ∩ V c' ⊆ bag t`. Proved using the uniqueness of the exit
point from `ConverseGap.lean`'s `exists_exit`, combined with the canonical level-indexed
ancestor (`above_iterate_level_sub`). -/
theorem V_inter_V_subset_bag {t : N.Node} {c c' : NonRoot N} (hp : N.parent c.1 = t)
    (hp' : N.parent c'.1 = t) (hne : c.1 ≠ c'.1) :
    V N c.1 ∩ V N c'.1 ⊆ N.bag t := by
  intro v hv
  simp only [Finset.mem_inter] at hv
  obtain ⟨hvc, hvc'⟩ := hv
  obtain ⟨s, hAs, hvs⟩ := (mem_V N).mp hvc
  obtain ⟨s', hAs', hvs'⟩ := (mem_V N).mp hvc'
  obtain ⟨e, m0, hUe, hUe', hm0le, hm0, hmin0⟩ :=
    exists_exit N.depth_le N.parent_root
      (U := fun x => v ∈ N.bag x) (by rw [N.bag_root]; simp) s hvs
  obtain ⟨e', m0', hUe'2, hUe'2', hm0le', hm0', hmin0'⟩ :=
    exists_exit N.depth_le N.parent_root
      (U := fun x => v ∈ N.bag x) (by rw [N.bag_root]; simp) s' hvs'
  have heE : e = e' := N.connected v e e' hUe hUe' hUe'2 hUe'2'
  subst heE
  have hlevelc : level N.depth_le c.1 = level N.depth_le t + 1 := by
    rw [← hp]; exact level_succ N.depth_le N.parent_root c.2
  have hlevelc' : level N.depth_le c'.1 = level N.depth_le t + 1 := by
    rw [← hp']; exact level_succ N.depth_le N.parent_root c'.2
  have hlevel_le : level N.depth_le e ≤ level N.depth_le t := by
    by_contra hcon
    push_neg at hcon
    have hAec : Above N e c.1 :=
      above_of_ge_level N hAs hm0le hm0 (by omega)
    have hAec' : Above N e c'.1 :=
      above_of_ge_level N hAs' hm0le' hm0' (by omega)
    have hcanon1 := above_iterate_level_sub N hAec
    have hcanon2 := above_iterate_level_sub N hAec'
    rw [show level N.depth_le c.1 = level N.depth_le c'.1 by omega] at hcanon1
    exact hne (hcanon1.symm.trans hcanon2)
  have hAst : Above N s t := above_trans N hAs (above_of_parent_eq N hp)
  have hcanon_t := above_iterate_level_sub N hAst
  have hlevel_e_eq : level N.depth_le e = level N.depth_le s - m0 := by
    rw [← hm0]; exact level_iterate N.depth_le N.parent_root hm0le
  have hk_le : level N.depth_le s - level N.depth_le t ≤ m0 := by omega
  have := hmin0 (level N.depth_le s - level N.depth_le t) hk_le
  rw [hcanon_t] at this
  exact this

end Independence

end Lax461425Proofs
