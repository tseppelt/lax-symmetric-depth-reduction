import Lax461425.Forestwidth
import Lax461425Proofs.ConverseGap

/-!
A normalised tree decomposition of a pattern `F`, built from an arbitrary
`DepthDecomposition`. Compared to the given decomposition, the normalised one additionally
has: every vertex of a bag incident with an edge represented at that node or below (so that
`γ(β(t))` is the minimal support of a gate `R_{t,γ}`, see `ConverseSupports.lean`), and no bag
contained in its parent's bag (so that the number of nodes is at most `|V(F)| + 1`).

The construction proceeds in two steps. First (`preNormA`), vertices are deleted from bags
wherever no incident edge is represented at-or-below; this preserves all tree decomposition
properties (using the "gap-free" lemma of `ConverseGap.lean`) and establishes the "represented
below" property, without changing the tree. Second (`stepB` / `NormDecomp.ofPreNorm`), nodes
whose bag is contained in their parent's bag are contracted away, by passing to the subtype of
"keeper" nodes and jumping each node to its nearest keeper ancestor.
-/

namespace Lax461425Proofs

open Classical Lax461425.HomomorphismPolynomials Lax461425.Forestwidth

variable {F : Pattern} {Δ k : ℕ}

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Intermediate decomposition data for `F`: a rooted tree of depth `≤ Δ` with empty root bag,
bags of size `≤ k`, an edge representative map, and the "every bag vertex is incident with an
edge represented at or below" property, but not yet satisfying "no bag is a subset of its
parent's". -/
structure PreNorm (F : Pattern) (Δ k : ℕ) where
  /-- The nodes of the tree. -/
  Node : Type
  [fintypeNode : Fintype Node]
  /-- The root of the tree. -/
  root : Node
  /-- The parent of each node; the root is its own parent. -/
  parent : Node → Node
  parent_root : parent root = root
  /-- Every node is at distance at most `Δ` from the root. -/
  depth_le : ∀ t, parent^[Δ] t = root
  /-- The bag of each node. -/
  bag : Node → Finset (F.A ⊕ F.B)
  bag_root : bag root = ∅
  card_bag_le : ∀ t, (bag t).card ≤ k
  /-- The nodes whose bags contain a vertex `v` induce a connected subtree. -/
  connected : ∀ v t t', v ∈ bag t → v ∉ bag (parent t) → v ∈ bag t' → v ∉ bag (parent t') →
    t = t'
  /-- The node representing the edge (if any) between `a` and `b`. -/
  rep : F.A → F.B → Node
  rep_mem : ∀ a b, F.mult a b ≠ 0 → Sum.inl a ∈ bag (rep a b) ∧ Sum.inr b ∈ bag (rep a b)
  /-- Every vertex of a bag is incident with an edge represented at that node or below. -/
  represented_below : ∀ t v, v ∈ bag t →
    ∃ a b, F.mult a b ≠ 0 ∧ (v = Sum.inl a ∨ v = Sum.inr b) ∧ ∃ m, parent^[m] (rep a b) = t

attribute [instance] PreNorm.fintypeNode

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A normalised tree decomposition of `F`: like `PreNorm`, but also with no bag contained in
its parent's bag (so there are at most `|V(F)| + 1` nodes, see `NormDecomp.card_node_le`). -/
structure NormDecomp (F : Pattern) (Δ k : ℕ) where
  Node : Type
  [fintypeNode : Fintype Node]
  root : Node
  parent : Node → Node
  parent_root : parent root = root
  depth_le : ∀ t, parent^[Δ] t = root
  bag : Node → Finset (F.A ⊕ F.B)
  bag_root : bag root = ∅
  card_bag_le : ∀ t, (bag t).card ≤ k
  connected : ∀ v t t', v ∈ bag t → v ∉ bag (parent t) → v ∈ bag t' → v ∉ bag (parent t') →
    t = t'
  rep : F.A → F.B → Node
  rep_mem : ∀ a b, F.mult a b ≠ 0 → Sum.inl a ∈ bag (rep a b) ∧ Sum.inr b ∈ bag (rep a b)
  represented_below : ∀ t v, v ∈ bag t →
    ∃ a b, F.mult a b ≠ 0 ∧ (v = Sum.inl a ∨ v = Sum.inr b) ∧ ∃ m, parent^[m] (rep a b) = t
  not_subset_parent : ∀ c, c ≠ root → ¬ bag c ⊆ bag (parent c)

attribute [instance] NormDecomp.fintypeNode

/-! ### Step A: deleting vertices whose incident edges are not represented below -/

section StepA

variable (D : DepthDecomposition F Δ k)

/-- A choice of representative node for the edge `ab`, when it is an edge. -/
noncomputable def repA (a : F.A) (b : F.B) : D.Node :=
  if h : F.mult a b ≠ 0 then (D.exists_edge_mem_bag a b h).choose else D.root

theorem repA_mem {a : F.A} {b : F.B} (h : F.mult a b ≠ 0) :
    Sum.inl a ∈ D.bag (repA D a b) ∧ Sum.inr b ∈ D.bag (repA D a b) := by
  simp only [repA, dif_pos h]
  exact (D.exists_edge_mem_bag a b h).choose_spec

/-- `v` is kept in the bag of `t`: there is an edge incident with `v`, represented at `t` or
below. -/
def goodA (t : D.Node) (v : F.A ⊕ F.B) : Prop :=
  ∃ a b, F.mult a b ≠ 0 ∧ (v = Sum.inl a ∨ v = Sum.inr b) ∧ ∃ m, D.parent^[m] (repA D a b) = t

/-- The shrunk bag: vertices of `D.bag t` that are kept. -/
noncomputable def bagA (t : D.Node) : Finset (F.A ⊕ F.B) :=
  (D.bag t).filter (goodA D t)

theorem mem_bagA {t : D.Node} {v : F.A ⊕ F.B} : v ∈ bagA D t ↔ v ∈ D.bag t ∧ goodA D t v :=
  Finset.mem_filter

/-- If `v` is kept at `t`, it is also kept at `parent t`: the witnessing edge is represented
one step closer to the root. -/
theorem goodA_parent {t : D.Node} {v : F.A ⊕ F.B} (h : goodA D t v) :
    goodA D (D.parent t) v := by
  obtain ⟨a, b, hmult, hv, m, hm⟩ := h
  refine ⟨a, b, hmult, hv, m + 1, ?_⟩
  rw [Function.iterate_succ_apply', hm]

/-- The pre-normalised decomposition obtained from `D` by deleting, from every bag, the
vertices with no incident edge represented at that node or below. -/
noncomputable def preNormA : PreNorm F Δ k where
  Node := D.Node
  root := D.root
  parent := D.parent
  parent_root := D.parent_root
  depth_le := D.depth_le
  bag := bagA D
  bag_root := by
    show bagA D D.root = ∅
    unfold bagA
    rw [D.bag_root]
    simp
  card_bag_le := fun t => le_trans (Finset.card_filter_le _ _) (D.card_bag_le t)
  connected := by
    intro v t t' ht hpt ht2 hpt2
    obtain ⟨hvt, hgt⟩ := (mem_bagA D).mp ht
    obtain ⟨hvt2, hgt2⟩ := (mem_bagA D).mp ht2
    have hnt : v ∉ D.bag (D.parent t) := fun hc =>
      hpt ((mem_bagA D).mpr ⟨hc, goodA_parent D hgt⟩)
    have hnt2 : v ∉ D.bag (D.parent t') := fun hc =>
      hpt2 ((mem_bagA D).mpr ⟨hc, goodA_parent D hgt2⟩)
    exact D.connected v t t' hvt hnt hvt2 hnt2
  rep := repA D
  rep_mem := by
    intro a b hmult
    obtain ⟨h1, h2⟩ := repA_mem D hmult
    exact ⟨(mem_bagA D).mpr ⟨h1, a, b, hmult, Or.inl rfl, 0, rfl⟩,
      (mem_bagA D).mpr ⟨h2, a, b, hmult, Or.inr rfl, 0, rfl⟩⟩
  represented_below := fun t v hv => ((mem_bagA D).mp hv).2

end StepA

/-! ### Step B: contracting nodes whose bag is contained in their parent's -/

section StepB

variable (P : PreNorm F Δ k)

/-- A node is a "keeper" if it is the root, or its bag is not contained in its parent's. -/
def IsKeeper (t : P.Node) : Prop := t = P.root ∨ ¬ P.bag t ⊆ P.bag (P.parent t)

theorem isKeeper_root : IsKeeper P P.root := Or.inl rfl

private theorem exists_isKeeper_iterate (t : P.Node) : ∃ j, IsKeeper P (P.parent^[j] t) :=
  ⟨Δ, by rw [P.depth_le t]; exact isKeeper_root P⟩

/-- The number of steps from `t` to its nearest keeper ancestor (or `t` itself). -/
noncomputable def stepsB (t : P.Node) : ℕ :=
  Nat.find (exists_isKeeper_iterate P t)

theorem stepsB_spec (t : P.Node) : IsKeeper P (P.parent^[stepsB P t] t) :=
  Nat.find_spec (exists_isKeeper_iterate P t)

theorem stepsB_min {t : P.Node} {i : ℕ} (hi : i < stepsB P t) : ¬ IsKeeper P (P.parent^[i] t) :=
  Nat.find_min (exists_isKeeper_iterate P t) hi

theorem stepsB_le {t : P.Node} {j : ℕ} (hj : IsKeeper P (P.parent^[j] t)) : stepsB P t ≤ j :=
  Nat.find_le hj

/-- The contracted node type: keepers of `P.Node`. -/
def NodeB := {t : P.Node // IsKeeper P t}

noncomputable instance : Fintype (NodeB P) := Subtype.fintype _

/-- The nearest keeper ancestor-or-self of `t`. -/
noncomputable def upB (t : P.Node) : NodeB P := ⟨P.parent^[stepsB P t] t, stepsB_spec P t⟩

theorem stepsB_le_level (t : P.Node) : stepsB P t ≤ level P.depth_le t := by
  apply stepsB_le
  rw [iterate_level P.depth_le]
  exact isKeeper_root P

theorem level_upB_le (t : P.Node) : level P.depth_le (upB P t).1 ≤ level P.depth_le t := by
  show level P.depth_le (P.parent^[stepsB P t] t) ≤ level P.depth_le t
  rw [level_iterate P.depth_le P.parent_root (stepsB_le_level P t)]
  omega

/-- The contracted root. -/
def rootB : NodeB P := ⟨P.root, isKeeper_root P⟩

/-- The contracted parent map: jump to the nearest keeper ancestor of the original parent. -/
noncomputable def parentB (t' : NodeB P) : NodeB P :=
  if _h : t'.1 = P.root then t' else upB P (P.parent t'.1)

theorem parentB_root : parentB P (rootB P) = rootB P := by
  unfold parentB
  exact dif_pos rfl

theorem parentB_of_ne {t' : NodeB P} (h : t'.1 ≠ P.root) :
    parentB P t' = upB P (P.parent t'.1) :=
  dif_neg h

/-- The contracted bag: unchanged from the original node's bag. -/
def bagB (t' : NodeB P) : Finset (F.A ⊕ F.B) := P.bag t'.1

/-- The contracted edge-representative map. -/
noncomputable def repB (a : F.A) (b : F.B) : NodeB P := upB P (P.rep a b)

/-- Along a maximal run of non-keepers, bags only grow. -/
theorem bag_subset_iterate {t : P.Node} {n : ℕ} (h : ∀ i < n, ¬ IsKeeper P (P.parent^[i] t)) :
    P.bag t ⊆ P.bag (P.parent^[n] t) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprev : P.bag t ⊆ P.bag (P.parent^[n] t) := ih (fun i hi => h i (by omega))
      have hnk : ¬ IsKeeper P (P.parent^[n] t) := h n (by omega)
      have hsub : P.bag (P.parent^[n] t) ⊆ P.bag (P.parent (P.parent^[n] t)) := by
        rw [IsKeeper, not_or] at hnk
        exact not_not.mp hnk.2
      have heq2 : P.parent^[n + 1] t = P.parent (P.parent^[n] t) :=
        Function.iterate_succ_apply' _ _ _
      rw [heq2]
      exact hprev.trans hsub

theorem bagB_subset_up (t : P.Node) : P.bag t ⊆ P.bag (upB P t).1 := by
  show P.bag t ⊆ P.bag (P.parent^[stepsB P t] t)
  exact bag_subset_iterate P (fun i hi => stepsB_min P hi)

/-- If `t` is reachable from `s` by iterating `parent`, the nearest keeper ancestor of `s`
can reach `t` by iterating the contracted `parentB`. -/
theorem reachB : ∀ m0 (s t : P.Node) (ht : IsKeeper P t), P.parent^[m0] s = t →
    ∃ m, (parentB P)^[m] (upB P s) = ⟨t, ht⟩ := by
  intro m0
  induction m0 using Nat.strong_induction_on with
  | _ m0 IH =>
    intro s t ht heq
    by_cases hteq : (upB P s).1 = t
    · exact ⟨0, Subtype.ext hteq⟩
    · have hd0 : stepsB P s ≤ m0 := by
        apply stepsB_le
        rw [heq]; exact ht
      have hd0lt : stepsB P s < m0 := by
        rcases lt_or_eq_of_le hd0 with h | h
        · exact h
        · exact absurd (by show P.parent^[stepsB P s] s = t; rw [h]; exact heq) hteq
      have hsplit : P.parent^[(m0 - stepsB P s) + stepsB P s] s = t := by
        rw [Nat.sub_add_cancel hd0]; exact heq
      have hcomb : P.parent^[m0 - stepsB P s] ((upB P s).1) = t := by
        rwa [Function.iterate_add_apply] at hsplit
      have ht0root : (upB P s).1 ≠ P.root := by
        intro hroot0
        apply hteq
        have hfixed : P.parent^[m0 - stepsB P s] ((upB P s).1) = (upB P s).1 :=
          Function.iterate_fixed (hroot0 ▸ P.parent_root) _
        exact hfixed.symm.trans hcomb
      have hreach' : P.parent^[m0 - stepsB P s - 1] (P.parent ((upB P s).1)) = t := by
        have heq2 : P.parent^[(m0 - stepsB P s - 1) + 1] ((upB P s).1) = t := by
          rw [Nat.sub_add_cancel (by omega)]
          exact hcomb
        rwa [Function.iterate_succ_apply] at heq2
      obtain ⟨m', hm'⟩ := IH (m0 - stepsB P s - 1) (by omega) (P.parent ((upB P s).1)) t ht
        hreach'
      refine ⟨m' + 1, ?_⟩
      have hstep : parentB P (upB P s) = upB P (P.parent ((upB P s).1)) := parentB_of_ne P ht0root
      rw [Function.iterate_succ_apply, hstep]
      exact hm'

theorem depth_leB (t' : NodeB P) : (parentB P)^[Δ] t' = rootB P := by
  apply iterate_eq_of_measure_decreasing (parentB P) (rootB P) (fun t' => level P.depth_le t'.1)
    (parentB_root P) (level_eq_zero_of_eq_root P.depth_le P.parent_root)
  · intro x hx
    have hx1 : x.1 ≠ P.root := by
      intro h; exact hx (Subtype.ext h)
    have hpar : parentB P x = upB P (P.parent x.1) := parentB_of_ne P hx1
    rw [hpar]
    calc level P.depth_le (upB P (P.parent x.1)).1
        ≤ level P.depth_le (P.parent x.1) := level_upB_le P _
      _ < level P.depth_le x.1 := level_parent_lt P.depth_le P.parent_root hx1
  · exact level_le P.depth_le t'.1

theorem card_bagB_le (t' : NodeB P) : (bagB P t').card ≤ k := P.card_bag_le t'.1

theorem bagB_root : bagB P (rootB P) = ∅ := P.bag_root

theorem connectedB : ∀ v t' t'', v ∈ bagB P t' → v ∉ bagB P (parentB P t') → v ∈ bagB P t'' →
    v ∉ bagB P (parentB P t'') → t' = t'' := by
  intro v t' t'' h1 h2 h3 h4
  by_cases he1 : t'.1 = P.root
  · exfalso
    apply h2
    have heq1 : parentB P t' = t' := by unfold parentB; exact dif_pos he1
    rw [heq1]
    exact h1
  by_cases he2 : t''.1 = P.root
  · exfalso
    apply h4
    have heq2 : parentB P t'' = t'' := by unfold parentB; exact dif_pos he2
    rw [heq2]
    exact h3
  have h2' : v ∉ P.bag (P.parent t'.1) := by
    intro hc
    have : v ∈ P.bag (parentB P t').1 := by
      rw [parentB_of_ne P he1]
      exact bagB_subset_up P (P.parent t'.1) hc
    exact h2 this
  have h4' : v ∉ P.bag (P.parent t''.1) := by
    intro hc
    have : v ∈ P.bag (parentB P t'').1 := by
      rw [parentB_of_ne P he2]
      exact bagB_subset_up P (P.parent t''.1) hc
    exact h4 this
  exact Subtype.ext (P.connected v t'.1 t''.1 h1 h2' h3 h4')

/-- **Item 3 of the normalised decomposition.** No non-root bag is contained in its parent's,
after contraction: this is where the "gap-free" lemma is used. -/
theorem not_subset_parentB (c' : NodeB P) (hc : c' ≠ rootB P) :
    ¬ bagB P c' ⊆ bagB P (parentB P c') := by
  have hc1 : c'.1 ≠ P.root := fun h => hc (Subtype.ext h)
  have hns : ¬ P.bag c'.1 ⊆ P.bag (P.parent c'.1) := c'.2.resolve_left hc1
  obtain ⟨v0, hv0mem, hv0notmem⟩ := Finset.not_subset.mp hns
  intro hcontra
  have hv0' : v0 ∈ P.bag (parentB P c').1 := hcontra hv0mem
  rw [parentB_of_ne P hc1] at hv0'
  have hreach : P.parent^[stepsB P (P.parent c'.1) + 1] c'.1 = (upB P (P.parent c'.1)).1 := by
    rw [Function.iterate_succ_apply]
    rfl
  have hU : (fun t => v0 ∈ P.bag t) (P.parent^[stepsB P (P.parent c'.1) + 1] c'.1) := by
    rw [hreach]; exact hv0'
  have hUd : (fun t => v0 ∈ P.bag t) c'.1 := hv0mem
  have hgap := gap_free P.depth_le P.parent_root (U := fun t => v0 ∈ P.bag t)
    (by rw [P.bag_root]; simp) (P.connected v0) hUd hU (i := 1) (by omega)
  have h1 : P.parent^[1] c'.1 = P.parent c'.1 := by simp
  rw [h1] at hgap
  exact hv0notmem hgap

theorem rep_memB (a : F.A) (b : F.B) (h : F.mult a b ≠ 0) :
    Sum.inl a ∈ bagB P (repB P a b) ∧ Sum.inr b ∈ bagB P (repB P a b) :=
  ⟨bagB_subset_up P (P.rep a b) (P.rep_mem a b h).1, bagB_subset_up P (P.rep a b) (P.rep_mem a b h).2⟩

theorem represented_belowB : ∀ t' v, v ∈ bagB P t' →
    ∃ a b, F.mult a b ≠ 0 ∧ (v = Sum.inl a ∨ v = Sum.inr b) ∧
      ∃ m, (parentB P)^[m] (repB P a b) = t' := by
  intro t' v hv
  obtain ⟨a, b, hmult, hveq, m0, hm0⟩ := P.represented_below t'.1 v hv
  obtain ⟨m, hm⟩ := reachB P m0 (P.rep a b) t'.1 t'.2 hm0
  exact ⟨a, b, hmult, hveq, m, hm⟩

/-- The normalised decomposition obtained from `P` by contracting every node whose bag is
contained in its parent's bag into its parent. -/
noncomputable def NormDecomp.ofPreNorm : NormDecomp F Δ k where
  Node := NodeB P
  root := rootB P
  parent := parentB P
  parent_root := parentB_root P
  depth_le := depth_leB P
  bag := bagB P
  bag_root := bagB_root P
  card_bag_le := card_bagB_le P
  connected := connectedB P
  rep := repB P
  rep_mem := rep_memB P
  represented_below := represented_belowB P
  not_subset_parent := not_subset_parentB P

end StepB

/-- Every pattern admitting a `DepthDecomposition` admits a normalised one, with the same
`Δ` and `k`. -/
noncomputable def normDecompOfDepthDecomposition (D : DepthDecomposition F Δ k) :
    NormDecomp F Δ k :=
  NormDecomp.ofPreNorm (preNormA D)

/-- **Item 4 of the normalised decomposition.** There are at most `|V(F)| + 1` nodes. -/
theorem NormDecomp.card_node_le (N : NormDecomp F Δ k) :
    Fintype.card N.Node ≤ Fintype.card (F.A ⊕ F.B) + 1 := by
  classical
  have hex : ∀ c : {c : N.Node // c ≠ N.root},
      ∃ v, v ∈ N.bag c.1 ∧ v ∉ N.bag (N.parent c.1) :=
    fun c => Finset.not_subset.mp (N.not_subset_parent c.1 c.2)
  choose f hf1 hf2 using hex
  have hfinj : Function.Injective f := by
    intro c1 c2 heq
    refine Subtype.ext (N.connected (f c1) c1.1 c2.1 (hf1 c1) (hf2 c1) ?_ ?_)
    · rw [heq]; exact hf1 c2
    · rw [heq]; exact hf2 c2
  have hcard : Fintype.card {c : N.Node // c ≠ N.root} ≤ Fintype.card (F.A ⊕ F.B) :=
    Fintype.card_le_of_injective f hfinj
  have hsplit : Fintype.card {c : N.Node // c ≠ N.root}
      = Fintype.card N.Node - Fintype.card {c : N.Node // c = N.root} :=
    Fintype.card_subtype_compl (fun c : N.Node => c = N.root)
  rw [Fintype.card_subtype_eq N.root] at hsplit
  have hpos : 1 ≤ Fintype.card N.Node := Fintype.card_pos_iff.mpr ⟨N.root⟩
  omega

end Lax461425Proofs
