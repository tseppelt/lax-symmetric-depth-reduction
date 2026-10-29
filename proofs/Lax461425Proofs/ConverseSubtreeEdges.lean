import Lax461425Proofs.ConverseSubtree

/-!
The edges represented at-or-below a node `t`, and the disjoint decomposition of this set into
the edges represented exactly at `t` and the edges represented at-or-below each child of `t`.
This mirrors, at the level of edges, the decomposition of the vertex set `V t` from
`ConverseSubtree.lean`, and is the combinatorial fact needed to split the "product over edges
below `t`" when relating `P t γ` to a sum over admissible maps on `V t`.
-/

namespace Lax461425Proofs

open Classical Lax461425.HomomorphismPolynomials Lax461425.Forestwidth

variable {F : Pattern} {Δ k : ℕ}

section EdgesBelow

variable (N : NormDecomp F Δ k)

/-- The edges of `F` represented at `t` or at some descendant of `t`. -/
noncomputable def edgesBelow (t : N.Node) : Finset (F.A × F.B) :=
  Finset.univ.filter (fun ab => F.mult ab.1 ab.2 ≠ 0 ∧ Above N (N.rep ab.1 ab.2) t)

theorem mem_edgesBelow_iff {t : N.Node} {ab : F.A × F.B} :
    ab ∈ edgesBelow N t ↔ F.mult ab.1 ab.2 ≠ 0 ∧ Above N (N.rep ab.1 ab.2) t := by
  simp [edgesBelow]

theorem edgesAt_subset_edgesBelow (t : N.Node) : edgesAt N t ⊆ edgesBelow N t := by
  intro ab hab
  obtain ⟨hmult, heq⟩ := (mem_edgesAt_iff N).mp hab
  exact (mem_edgesBelow_iff N).mpr ⟨hmult, heq ▸ above_self N t⟩

theorem mem_V_left {t : N.Node} {ab : F.A × F.B} (h : ab ∈ edgesBelow N t) :
    Sum.inl ab.1 ∈ V N t := by
  obtain ⟨hmult, hAbove⟩ := (mem_edgesBelow_iff N).mp h
  exact (mem_V N).mpr ⟨N.rep ab.1 ab.2, hAbove, (N.rep_mem ab.1 ab.2 hmult).1⟩

theorem mem_V_right {t : N.Node} {ab : F.A × F.B} (h : ab ∈ edgesBelow N t) :
    Sum.inr ab.2 ∈ V N t := by
  obtain ⟨hmult, hAbove⟩ := (mem_edgesBelow_iff N).mp h
  exact (mem_V N).mpr ⟨N.rep ab.1 ab.2, hAbove, (N.rep_mem ab.1 ab.2 hmult).2⟩

/-- If `x` is a descendant-or-self of `t` other than `t`, it is a descendant-or-self of some
specific child of `t`. -/
theorem exists_child_of_above_ne {t x : N.Node} (h : Above N x t) (hne : x ≠ t) :
    ∃ c : NonRoot N, N.parent c.1 = t ∧ Above N x c.1 := by
  have hlt : level N.depth_le t < level N.depth_le x := level_lt_of_above_ne N h hne
  set d := level N.depth_le x - level N.depth_le t with hd
  have hdpos : 0 < d := by omega
  set c0 := N.parent^[d - 1] x with hc0
  have hledx : d - 1 ≤ level N.depth_le x := by omega
  have hlevelc0 : level N.depth_le c0 = level N.depth_le t + 1 := by
    rw [hc0, level_iterate N.depth_le N.parent_root hledx]
    omega
  have hc0ne : c0 ≠ N.root := by
    intro hr
    rw [hr, level_eq_zero_of_eq_root N.depth_le N.parent_root] at hlevelc0
    omega
  refine ⟨⟨c0, hc0ne⟩, ?_, ⟨d - 1, rfl⟩⟩
  show N.parent c0 = t
  have hcanon : N.parent^[d] x = t := by rw [hd]; exact above_iterate_level_sub N h
  have hstep : N.parent c0 = N.parent^[d - 1 + 1] x := by
    rw [hc0]; exact (Function.iterate_succ_apply' N.parent (d - 1) x).symm
  rw [hstep, show d - 1 + 1 = d by omega]
  exact hcanon

/-- If `x` is a descendant-or-self of two nodes `c, c'` at the same level, those nodes
coincide: the ancestor at a given level is unique. -/
theorem above_unique_of_level_eq {x c c' : N.Node} (h1 : Above N x c) (h2 : Above N x c')
    (hlev : level N.depth_le c = level N.depth_le c') : c = c' := by
  have e1 := above_iterate_level_sub N h1
  have e2 := above_iterate_level_sub N h2
  rw [hlev] at e1
  exact e1.symm.trans e2

/-- A child's level is one more than its parent's. -/
theorem level_child (t : N.Node) (c : NonRoot N) (hp : N.parent c.1 = t) :
    level N.depth_le c.1 = level N.depth_le t + 1 := by
  rw [← hp]; exact level_succ N.depth_le N.parent_root c.2

/-- A child is never equal to its parent. -/
theorem child_ne_parent {t : N.Node} {c : NonRoot N} (hp : N.parent c.1 = t) : c.1 ≠ t :=
  fun h => by have := level_child N t c hp; rw [h] at this; omega

/-- **The disjoint decomposition of `edgesBelow`.** The edges represented at-or-below `t` split
into the edges represented exactly at `t` and the edges represented at-or-below some child of
`t`. -/
theorem edgesBelow_eq_union (t : N.Node) :
    edgesBelow N t = edgesAt N t ∪ (children N t).biUnion (fun c => edgesBelow N c.1) := by
  apply Finset.Subset.antisymm
  · intro ab hab
    obtain ⟨hmult, hAbove⟩ := (mem_edgesBelow_iff N).mp hab
    by_cases heq : N.rep ab.1 ab.2 = t
    · exact Finset.mem_union_left _ ((mem_edgesAt_iff N).mpr ⟨hmult, heq⟩)
    · obtain ⟨c, hpc, hAc⟩ := exists_child_of_above_ne N hAbove heq
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨c, (mem_children N).mpr hpc, (mem_edgesBelow_iff N).mpr ⟨hmult, hAc⟩⟩)
  · intro ab hab
    rw [Finset.mem_union] at hab
    rcases hab with h1 | h2
    · exact edgesAt_subset_edgesBelow N t h1
    · obtain ⟨c, hc, hab2⟩ := Finset.mem_biUnion.mp h2
      obtain ⟨hmult, hAc⟩ := (mem_edgesBelow_iff N).mp hab2
      exact (mem_edgesBelow_iff N).mpr
        ⟨hmult, above_trans N hAc (above_of_parent_eq N ((mem_children N).mp hc))⟩

/-- `edgesAt t` is disjoint from the edges represented below any child of `t`. -/
theorem edgesAt_disjoint_biUnion (t : N.Node) :
    Disjoint (edgesAt N t) ((children N t).biUnion (fun c => edgesBelow N c.1)) := by
  rw [Finset.disjoint_left]
  intro ab hab1 hab2
  obtain ⟨_, heq⟩ := (mem_edgesAt_iff N).mp hab1
  obtain ⟨c, hc, hab3⟩ := Finset.mem_biUnion.mp hab2
  obtain ⟨_, hAc⟩ := (mem_edgesBelow_iff N).mp hab3
  have hp := (mem_children N).mp hc
  have h1 : Above N t c.1 := heq ▸ hAc
  have hlt := level_lt_of_above_ne N h1 (Ne.symm (child_ne_parent N hp))
  have hlevelc := level_child N t c hp
  omega

/-- The edges represented below distinct children of `t` are disjoint. -/
theorem edgesBelow_pairwise_disjoint (t : N.Node) :
    ∀ c ∈ children N t, ∀ c' ∈ children N t, c ≠ c' →
      Disjoint (edgesBelow N c.1) (edgesBelow N c'.1) := by
  intro c hc c' hc' hne
  rw [Finset.disjoint_left]
  intro ab hab hab'
  obtain ⟨_, hAc⟩ := (mem_edgesBelow_iff N).mp hab
  obtain ⟨_, hAc'⟩ := (mem_edgesBelow_iff N).mp hab'
  have hlev : level N.depth_le c.1 = level N.depth_le c'.1 := by
    rw [level_child N t c ((mem_children N).mp hc), level_child N t c' ((mem_children N).mp hc')]
  exact hne (Subtype.ext (above_unique_of_level_eq N hAc hAc' hlev))

/-- The `Set.PairwiseDisjoint` form of `edgesBelow_pairwise_disjoint`, as needed by
`Finset.prod_biUnion`/`Finset.sum_biUnion`. -/
theorem edgesBelow_pairwiseDisjoint_set (t : N.Node) :
    (↑(children N t) : Set (NonRoot N)).PairwiseDisjoint (fun c => edgesBelow N c.1) :=
  fun c hc c' hc' hne =>
    edgesBelow_pairwise_disjoint N t c (Finset.mem_coe.mp hc) c' (Finset.mem_coe.mp hc') hne

end EdgesBelow

end Lax461425Proofs
