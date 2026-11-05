import Lax461425.TreewidthForestwidth
import Lax461425Proofs.TreewidthForestwidthBasic

/-! Bounded-depth decompositions with empty root bag versus tree decompositions. -/

namespace Lax461425Proofs.TreewidthForestwidth

open Lax461425.HomomorphismPolynomials Lax461425.Forestwidth Lax461425.PatternWidths
open Lax461425Proofs.TreewidthForestwidthBasic

/-- In a connected graph, a property preserved along edges holds everywhere once it holds
somewhere. -/
theorem forall_of_connected {V : Type} {G : SimpleGraph V} (hG : G.Connected) (Q : V → Prop)
    {x₀ : V} (h₀ : Q x₀) (hstep : ∀ x y, G.Adj x y → Q x → Q y) (y : V) : Q y := by
  obtain ⟨p⟩ := hG.preconnected x₀ y
  induction p with
  | nil => exact h₀
  | cons h _ ih => exact ih (hstep _ _ h h₀)

theorem underlying_adj {F : Pattern} {u v : F.A ⊕ F.B} (h : (underlying F).Adj u v) :
    ∃ a b, F.mult a b ≠ 0 ∧ ((u = Sum.inl a ∧ v = Sum.inr b) ∨ (u = Sum.inr b ∧ v = Sum.inl a)) := by
  simp only [underlying, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨a, b, rfl, rfl, hab⟩ | ⟨a, b, rfl, rfl, hab⟩
  · exact ⟨a, b, hab, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨a, b, hab, Or.inr ⟨rfl, rfl⟩⟩

section ToTree

variable {F : Pattern} {Δ k : ℕ} (D : DepthDecomposition F Δ k)

/-- The tree of a bounded-depth decomposition: each node is joined to its parent. -/
def treeGraph : SimpleGraph D.Node := SimpleGraph.fromRel fun s t => D.parent s = t

theorem reachable_parent (t : D.Node) : (treeGraph D).Reachable t (D.parent t) := by
  by_cases h : t = D.parent t
  · rw [← h]
  · exact SimpleGraph.Adj.reachable (by simp [treeGraph, h])

theorem reachable_root (t : D.Node) : (treeGraph D).Reachable t D.root := by
  have : ∀ i, (treeGraph D).Reachable t (D.parent^[i] t) := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (reachable_parent D _)
  rw [← D.depth_le t]
  exact this Δ

theorem treeGraph_connected : (treeGraph D).Connected :=
  { preconnected := fun u v => (reachable_root D u).trans (reachable_root D v).symm
    nonempty := ⟨D.root⟩ }

theorem treeGraph_card : Nat.card (treeGraph D).edgeSet + 1 = Nat.card D.Node := by
  classical
  have hne : ∀ t : {t // t ≠ D.root}, (treeGraph D).Adj t.1 (D.parent t.1) := by
    rintro ⟨t, ht⟩
    refine ⟨fun h => ht (eq_root_of_parent_eq D h.symm), Or.inl rfl⟩
  let f : {t // t ≠ D.root} → (treeGraph D).edgeSet := fun t =>
    ⟨s(t.1, D.parent t.1), hne t⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨t, ht⟩ ⟨t', ht'⟩ h
      have h' := congrArg Subtype.val h
      simp only [f] at h'
      rw [Sym2.eq_iff] at h'
      apply Subtype.ext
      show t = t'
      rcases h' with ⟨h, _⟩ | ⟨h₁, h₂⟩
      · exact h
      · have e₁ : IsAnc D t t' := by rw [h₁]; exact isAnc_parent D t'
        have e₂ : IsAnc D t' t := by rw [← h₂]; exact isAnc_parent D t
        exact isAnc_antisymm D e₁ e₂
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | _ a b =>
        have hab : (treeGraph D).Adj a b := he
        simp only [treeGraph, SimpleGraph.fromRel_adj] at hab
        rcases hab.2 with h | h
        · refine ⟨⟨a, fun ha => hab.1 ?_⟩, ?_⟩
          · rw [← h, ha, D.parent_root]
          · simp [f, h]
        · refine ⟨⟨b, fun hb => hab.1 ?_⟩, ?_⟩
          · rw [← h, hb, D.parent_root]
          · simp [f, h, Sym2.eq_swap]
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have : 0 < Fintype.card D.Node := Fintype.card_pos_iff.mpr ⟨D.root⟩
  omega

theorem treeGraph_isTree : (treeGraph D).IsTree :=
  SimpleGraph.isTree_iff_connected_and_card.mpr ⟨treeGraph_connected D, treeGraph_card D⟩

theorem bag_connected (v : F.A ⊕ F.B) :
    ((treeGraph D).induce {i | v ∈ D.bag i}).Connected := by
  have key : ∀ (b : D.Node) (hb : v ∈ D.bag b),
      ((treeGraph D).induce {i | v ∈ D.bag i}).Reachable ⟨b, hb⟩ ⟨top D v, mem_bag_top D v⟩ := by
    intro b hb
    obtain ⟨i, hi, hj⟩ := exists_exit D hb
    have step : ∀ j (hji : j ≤ i), ((treeGraph D).induce {i | v ∈ D.bag i}).Reachable ⟨b, hb⟩
        ⟨D.parent^[j] b, hj j hji⟩ := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hji
        refine (ih (by omega)).trans ?_
        have hmem := hj (j + 1) hji
        rw [Function.iterate_succ_apply'] at hmem
        by_cases h : D.parent^[j] b = D.parent (D.parent^[j] b)
        · have : (⟨D.parent^[j] b, hj j (by omega)⟩ : {i | v ∈ D.bag i}) =
              ⟨D.parent^[j + 1] b, hj (j + 1) hji⟩ := by
            apply Subtype.ext
            simp only [Function.iterate_succ_apply']
            exact h
          rw [this]
        · apply SimpleGraph.Adj.reachable
          show (treeGraph D).Adj _ _
          simp [treeGraph, h, Function.iterate_succ_apply']
    have := step i le_rfl
    have htop : D.parent^[i] b = top D v := eq_top D ⟨hj i le_rfl, hi⟩
    convert this using 2
    exact htop.symm
  obtain ⟨b, hb⟩ := D.exists_mem_bag v
  exact
    { preconnected := fun x y => (key x.1 x.2).trans (key y.1 y.2).symm
      nonempty := ⟨⟨b, hb⟩⟩ }

end ToTree

/--
---
conclusion: Lax461425.TreewidthForestwidth.treewidthLE_of_forestwidthLE
---
Joining every node to its parent gives a tree (connected, with one edge per non-root node),
and the nodes whose bags contain a vertex are connected to its unique top node.
-/
theorem treewidthLE_of_forestwidthLE {Δ w : ℕ} {F : Pattern} (h : ForestwidthLE Δ w F) :
    TreewidthLE w F := by
  obtain ⟨D⟩ := h
  have hedge : ∀ ⦃u v : F.A ⊕ F.B⦄, (underlying F).Adj u v →
      ∃ i : D.Node, u ∈ D.bag i ∧ v ∈ D.bag i := by
    intro u v huv
    obtain ⟨a, b, hab, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := underlying_adj huv
    · exact D.exists_edge_mem_bag a b hab
    · obtain ⟨t, h₁, h₂⟩ := D.exists_edge_mem_bag a b hab
      exact ⟨t, h₂, h₁⟩
  exact ⟨⟨D.Node, treeGraph D, treeGraph_isTree D, D.bag, D.exists_mem_bag, hedge,
    bag_connected D⟩, D.card_bag_le⟩

section FromTree

variable {V : Type} {T : SimpleGraph V} (hT : T.IsTree) (r : V)

/-- The unique path from a node to the chosen root `r`. -/
noncomputable def path (t : V) : T.Walk t r := (hT.existsUnique_path t r).exists.choose

theorem path_isPath (t : V) : (path hT r t).IsPath := (hT.existsUnique_path t r).exists.choose_spec

theorem eq_path {t : V} {q : T.Walk t r} (hq : q.IsPath) : q = path hT r t :=
  (hT.existsUnique_path t r).unique hq (path_isPath hT r t)

/-- The parent of a node: the second vertex on its path to the root. -/
noncomputable def par (t : V) : V := (path hT r t).getVert 1

theorem path_root : path hT r r = .nil := (eq_path hT r SimpleGraph.Walk.IsPath.nil).symm

theorem par_root : par hT r r = r := by
  unfold par; rw [path_root]; rfl

theorem length_path_par {t : V} (ht : t ≠ r) :
    (path hT r (par hT r t)).length + 1 = (path hT r t).length := by
  have key : ∀ (p : T.Walk t r), p.IsPath →
      ∃ q : T.Walk (p.getVert 1) r, q.IsPath ∧ q.length + 1 = p.length := by
    intro p hp
    cases p with
    | nil => exact absurd rfl ht
    | cons h q =>
      exact ⟨q.copy q.getVert_zero.symm rfl, by simpa using hp.of_cons, by simp⟩
  obtain ⟨q, hq, hl⟩ := key _ (path_isPath hT r t)
  have e := eq_path hT r hq
  unfold par
  rw [← e]; exact hl

theorem eq_root_of_length {t : V} (h : (path hT r t).length = 0) : t = r :=
  SimpleGraph.Walk.eq_of_length_eq_zero h

theorem length_path_iterate (t : V) (i : ℕ) :
    (path hT r ((par hT r)^[i] t)).length = (path hT r t).length - i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    by_cases h : (par hT r)^[i] t = r
    · rw [h, par_root, path_root]
      rw [h, path_root] at ih
      simp only [SimpleGraph.Walk.length_nil] at ih ⊢
      omega
    · have := length_path_par hT r h
      omega

theorem par_of_adj {s t : V} (h : T.Adj s t) : par hT r s = t ∨ par hT r t = s := by
  classical
  by_cases hs : s ∈ (path hT r t).support
  · right
    have hq := (path_isPath hT r t).takeUntil hs
    have hq' : (SimpleGraph.Walk.cons h.symm (SimpleGraph.Walk.nil : T.Walk s s)).IsPath := by
      simp [h.ne.symm]
    have e1 : (path hT r t).takeUntil s hs =
        SimpleGraph.Walk.cons h.symm (SimpleGraph.Walk.nil : T.Walk s s) :=
      congrArg Subtype.val
        ((hT.isAcyclic.subsingleton_path t s).elim ⟨_, hq⟩ ⟨_, hq'⟩)
    have e2 := SimpleGraph.Walk.take_spec (path hT r t) hs
    rw [e1] at e2
    unfold par
    rw [← e2]
    simp
  · left
    have hp : (SimpleGraph.Walk.cons h (path hT r t)).IsPath := (path_isPath hT r t).cons hs
    unfold par
    rw [← eq_path hT r hp]
    simp

theorem par_antisymm {a b : V} {i j : ℕ} (h₁ : (par hT r)^[i] b = a)
    (h₂ : (par hT r)^[j] a = b) : a = b := by
  by_contra hne
  have l₁ := length_path_iterate hT r b i
  have l₂ := length_path_iterate hT r a j
  rw [h₁] at l₁
  rw [h₂] at l₂
  have hi : i ≠ 0 := by rintro rfl; exact hne h₁.symm
  have hj : j ≠ 0 := by rintro rfl; exact hne h₂
  have hb : (path hT r b).length ≠ 0 := by
    intro hb
    have hbr := eq_root_of_length hT r hb
    rw [hbr, Function.iterate_fixed (par_root hT r)] at h₁
    exact hne (h₁.symm.trans hbr.symm)
  omega

/-- Every node of a connected set `S` lies below a top node of `S`. -/
theorem isAnc_of_top (S : Set V) (hS : (T.induce S).Connected) {a : V} (ha : a ∈ S)
    (htop : a ≠ r → par hT r a ∉ S) {b : V} (hb : b ∈ S) : ∃ i, (par hT r)^[i] b = a := by
  refine forall_of_connected hS (fun y : S => ∃ i, (par hT r)^[i] y.1 = a) (x₀ := ⟨a, ha⟩)
    ⟨0, rfl⟩ ?_ ⟨b, hb⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy ⟨i, hi⟩
  have hxy' : T.Adj x y := hxy
  rcases par_of_adj hT r hxy' with hp | hp
  · by_cases hxa : x = a
    · subst hxa
      have hxr : x ≠ r := by
        rintro rfl
        rw [par_root] at hp
        exact hxy'.ne hp
      exact absurd (hp ▸ hy) (htop hxr)
    · obtain _ | i := i
      · exact absurd hi hxa
      · refine ⟨i, ?_⟩
        rw [Function.iterate_succ_apply, hp] at hi
        exact hi
  · refine ⟨i + 1, ?_⟩
    simp only
    rw [Function.iterate_succ_apply, hp]
    exact hi

/-- The parent map on the nodes below a new root `none`. -/
noncomputable def oparent [DecidableEq V] : Option V → Option V
  | none => none
  | some t => if t = r then none else some (par hT r t)

theorem oparent_iterate [DecidableEq V] :
    ∀ (n : ℕ) (t : V), (path hT r t).length < n → (oparent hT r)^[n] (some t) = none := by
  intro n
  induction n with
  | zero => intro t h; omega
  | succ n ih =>
    intro t h
    rw [Function.iterate_succ_apply]
    by_cases ht : t = r
    · simp only [oparent, ht, if_true]
      exact Function.iterate_fixed rfl n
    · simp only [oparent, ht, if_false]
      apply ih
      have := length_path_par hT r ht
      omega

end FromTree

/--
---
conclusion: Lax461425.TreewidthForestwidth.exists_forestwidthLE_of_treewidthLE
---
Root the tree at any node `r`, take as parent the next node on the unique path to `r`, and add
a new root with an empty bag above `r`. A vertex has a unique top node because every node
containing it lies below each of its top nodes.
-/
theorem exists_forestwidthLE_of_treewidthLE {w : ℕ} {F : Pattern} (h : TreewidthLE w F) :
    ∃ Δ, 1 ≤ Δ ∧ ForestwidthLE Δ w F := by
  classical
  obtain ⟨TD, hcard⟩ := h
  have := TD.nodeFintype
  have hT := TD.isTree
  let r : TD.Node := hT.connected.nonempty.some
  let bag : Option TD.Node → Finset (F.A ⊕ F.B) := fun x => x.elim ∅ TD.bag
  refine ⟨Fintype.card TD.Node + 1, by omega, ⟨{
    Node := Option TD.Node
    root := none
    parent := oparent hT r
    parent_root := rfl
    depth_le := ?_
    bag := bag
    bag_root := rfl
    card_bag_le := ?_
    exists_mem_bag := ?_
    exists_edge_mem_bag := ?_
    connected := ?_ }⟩⟩
  · rintro (_ | t)
    · exact Function.iterate_fixed rfl _
    · apply oparent_iterate
      have := (path_isPath hT r t).length_lt
      omega
  · rintro (_ | t)
    · simp [bag]
    · exact hcard t
  · intro v
    obtain ⟨i, hi⟩ := TD.vertex_mem_bag v
    exact ⟨some i, hi⟩
  · intro a b hab
    have hadj : (underlying F).Adj (Sum.inl a) (Sum.inr b) := by
      simp only [underlying, SimpleGraph.fromRel_adj]
      exact ⟨Sum.inl_ne_inr, Or.inl ⟨a, b, rfl, rfl, hab⟩⟩
    obtain ⟨i, hi⟩ := TD.edge_mem_bag hadj
    exact ⟨some i, hi⟩
  · intro v x x' hx hpx hx' hpx'
    obtain _ | a := x
    · simp [bag] at hx
    obtain _ | a' := x'
    · simp [bag] at hx'
    have htop : ∀ c : TD.Node, v ∉ bag (oparent hT r (some c)) →
        c ≠ r → par hT r c ∉ {i | v ∈ TD.bag i} := by
      intro c hc hcr
      simpa [oparent, hcr, bag] using hc
    obtain ⟨i, hi⟩ := isAnc_of_top hT r _ (TD.bag_indices_connected v) hx (htop a hpx) hx'
    obtain ⟨j, hj⟩ := isAnc_of_top hT r _ (TD.bag_indices_connected v) hx' (htop a' hpx') hx
    rw [par_antisymm hT r hi hj]

end Lax461425Proofs.TreewidthForestwidth
