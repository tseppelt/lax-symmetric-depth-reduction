import Lax461425.TreedepthForestwidth
import Lax461425Proofs.TreewidthForestwidth

/-! Bounded-depth decompositions with empty root bag versus elimination forests. -/

namespace Lax461425Proofs.TreedepthForestwidth

open Lax461425.HomomorphismPolynomials Lax461425.Forestwidth Lax461425.PatternWidths
open Lax461425Proofs.TreewidthForestwidthBasic Lax461425Proofs.TreewidthForestwidth
open Lax183560.AncestorForest

section ToForest

open Classical

variable {F : Pattern} {Δ w : ℕ} (D : DepthDecomposition F Δ (w + 1))

/-- An injective numbering of the vertices, used to order vertices with the same top node. -/
noncomputable def num (v : F.A ⊕ F.B) : ℕ := Fintype.equivFin (F.A ⊕ F.B) v

theorem num_injective : Function.Injective (num (F := F)) := by
  intro u v h
  exact (Fintype.equivFin _).injective (Fin.ext h)

/-- The position of a vertex among the vertices with the same top node. -/
noncomputable def pos (v : F.A ⊕ F.B) : ℕ :=
  (Finset.univ.filter fun u => top D u = top D v ∧ num u < num v).card

/-- The rank of a vertex in the elimination forest. -/
noncomputable def rk (v : F.A ⊕ F.B) : ℕ := (depth D (top D v) - 1) * (w + 1) + pos D v

theorem pos_lt (v : F.A ⊕ F.B) : pos D v < w + 1 := by
  refine lt_of_lt_of_le (Finset.card_lt_card ?_) (D.card_bag_le (top D v))
  refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨v, mem_bag_top D v, by simp⟩
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rw [← hu.1]
  exact mem_bag_top D u

theorem pos_lt_pos {u v : F.A ⊕ F.B} (ht : top D u = top D v) (hn : num u < num v) :
    pos D u < pos D v := by
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).mpr ⟨u, ?_, ?_⟩)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1.trans ht, hx.2.trans hn⟩
  · simp [ht, hn]
  · simp

theorem depth_top_pos (v : F.A ⊕ F.B) : 1 ≤ depth D (top D v) := by
  by_contra h
  exact top_ne_root D v (eq_root_of_depth_eq_zero D (by omega))

theorem rk_lt (v : F.A ⊕ F.B) : rk D v < (w + 1) * Δ := by
  have h1 := depth_top_pos D v
  have h2 := depth_le_Δ D (top D v)
  have h3 := pos_lt D v
  obtain ⟨d, hd⟩ : ∃ d, depth D (top D v) = d + 1 := ⟨_, (Nat.sub_add_cancel h1).symm⟩
  unfold rk
  rw [hd, Nat.add_sub_cancel]
  calc d * (w + 1) + pos D v < d * (w + 1) + (w + 1) := by omega
    _ = (w + 1) * (d + 1) := by ring
    _ ≤ (w + 1) * Δ := Nat.mul_le_mul_left _ (by omega)

theorem rk_lt_of_isAnc {u v : F.A ⊕ F.B} (h : IsAnc D (top D u) (top D v))
    (hne : top D u ≠ top D v) : rk D u < rk D v := by
  have hd := depth_lt_of_isAnc D h hne
  have h1 := depth_top_pos D u
  have h3 := pos_lt D u
  obtain ⟨d, hd'⟩ : ∃ d, depth D (top D u) = d + 1 := ⟨_, (Nat.sub_add_cancel h1).symm⟩
  obtain ⟨e, he⟩ : ∃ e, depth D (top D v) = d + 1 + e + 1 := ⟨depth D (top D v) - d - 2, by omega⟩
  unfold rk
  rw [hd', he]
  simp only [Nat.add_sub_cancel]
  calc d * (w + 1) + pos D u < d * (w + 1) + (w + 1) := by omega
    _ = (d + 1) * (w + 1) := by ring
    _ ≤ (d + 1 + e) * (w + 1) := Nat.mul_le_mul_right _ (by omega)
    _ ≤ (d + 1 + e) * (w + 1) + pos D v := Nat.le_add_right _ _

theorem cmp {u v : F.A ⊕ F.B} (h : IsAnc D (top D u) (top D v)) :
    u = v ∨ rk D u < rk D v ∨ (rk D v < rk D u ∧ top D u = top D v) := by
  by_cases hne : top D u = top D v
  · rcases lt_trichotomy (num u) (num v) with hn | hn | hn
    · right; left
      have := pos_lt_pos D hne hn
      unfold rk; rw [hne] at *; omega
    · exact Or.inl (num_injective hn)
    · right; right
      have := pos_lt_pos D hne.symm hn
      refine ⟨?_, hne⟩
      unfold rk; rw [hne] at *; omega
  · exact Or.inr (Or.inl (rk_lt_of_isAnc D h hne))

/-- The elimination forest: `u` is an ancestor of `v` if it has smaller rank and its top node
is an ancestor of that of `v`. -/
def forest : AncestorForest (F.A ⊕ F.B) where
  ancestor u v := rk D u < rk D v ∧ IsAnc D (top D u) (top D v)
  transitive := ⟨fun _ _ _ h₁ h₂ => ⟨h₁.1.trans h₂.1, isAnc_trans D h₁.2 h₂.2⟩⟩
  irreflexive := ⟨fun _ h => lt_irrefl _ h.1⟩
  ancestors_linearly_ordered := by
    rintro u v x ⟨⟨_, hu⟩, ⟨_, hv⟩⟩
    rcases isAnc_total D hu hv with h | h
    · rcases cmp D h with h' | h' | ⟨h', he⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl ⟨h', h⟩)
      · exact Or.inr (Or.inr ⟨h', he ▸ isAnc_refl D _⟩)
    · rcases cmp D h with h' | h' | ⟨h', he⟩
      · exact Or.inl h'.symm
      · exact Or.inr (Or.inr ⟨h', h⟩)
      · exact Or.inr (Or.inl ⟨h', he ▸ isAnc_refl D _⟩)

end ToForest

/--
---
conclusion: Lax461425.TreedepthForestwidth.treedepthLE_of_forestwidthLE
---
Each vertex is placed at its unique top node. Vertices at a node of depth `d` receive the ranks
`(d - 1)(w + 1), …, d(w + 1) - 1` in a fixed order, and `u` is an ancestor of `v` if it has
smaller rank and its top node is an ancestor of that of `v`. The endpoints of an edge lie in a
common bag, so their top nodes are both ancestors of that node, hence comparable.
-/
theorem treedepthLE_of_forestwidthLE {Δ w : ℕ} {F : Pattern} (h : ForestwidthLE Δ w F) :
    TreedepthLE ((w + 1) * Δ) F := by
  obtain ⟨D⟩ := h
  refine ⟨forest D, ?_, fun v => ⟨rk D v, rk_lt D v⟩, fun _ _ h => h.1⟩
  intro u v huv
  have hne : u ≠ v := huv.ne
  have hs : ∃ s, u ∈ D.bag s ∧ v ∈ D.bag s := by
    obtain ⟨a, b, hab, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := underlying_adj huv
    · exact D.exists_edge_mem_bag a b hab
    · obtain ⟨t, h₁, h₂⟩ := D.exists_edge_mem_bag a b hab
      exact ⟨t, h₂, h₁⟩
  obtain ⟨s, hu, hv⟩ := hs
  rcases isAnc_total D (isAnc_top D hu) (isAnc_top D hv) with h | h
  · rcases cmp D h with h' | h' | ⟨h', he⟩
    · exact absurd h' hne
    · exact Or.inl ⟨h', h⟩
    · exact Or.inr ⟨h', he ▸ isAnc_refl D _⟩
  · rcases cmp D h with h' | h' | ⟨h', he⟩
    · exact absurd h'.symm hne
    · exact Or.inr ⟨h', h⟩
    · exact Or.inl ⟨h', he ▸ isAnc_refl D _⟩

section FromForest

open Classical

variable {V : Type} [Fintype V] {t : ℕ} (A : AncestorForest V) (rank : V → Fin t)
  (hrank : ∀ ⦃u v : V⦄, A.ancestor u v → rank u < rank v)

omit [Fintype V] in
theorem anc_trichotomy {u v x : V} (hu : A.ancestor u x) (hv : A.ancestor v x) :
    u = v ∨ A.ancestor u v ∨ A.ancestor v u := A.ancestors_linearly_ordered u v x ⟨hu, hv⟩

include hrank

omit hrank in
theorem exists_imm {v : V} (h : ∃ u, A.ancestor u v) :
    ∃ u, A.ancestor u v ∧ ∀ x, A.ancestor x v → (rank x : ℕ) ≤ rank u := by
  obtain ⟨u₀, hu₀⟩ := h
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun u => A.ancestor u v)
    (fun u => (rank u : ℕ)) ⟨u₀, by simp [hu₀]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hmax
  exact ⟨u, hu, hmax⟩

omit hrank in
/-- The immediate ancestor of a vertex (if it has an ancestor). -/
noncomputable def imm {v : V} (h : ∃ u, A.ancestor u v) : V := (exists_imm A rank h).choose

omit hrank in
theorem imm_anc {v : V} (h : ∃ u, A.ancestor u v) : A.ancestor (imm A rank h) v :=
  (exists_imm A rank h).choose_spec.1

theorem anc_imm {v x : V} (h : ∃ u, A.ancestor u v) (hx : A.ancestor x v) :
    x = imm A rank h ∨ A.ancestor x (imm A rank h) := by
  have hmax := (exists_imm A rank h).choose_spec.2 x hx
  rcases anc_trichotomy A hx (imm_anc A rank h) with e | e | e
  · exact Or.inl e
  · exact Or.inr e
  · have := hrank e
    exact absurd hmax (by unfold imm at this; exact Nat.not_le.mpr this)

omit hrank in
/-- The parent map: a vertex's immediate ancestor, or the new root `none`. -/
noncomputable def fparent : Option V → Option V
  | none => none
  | some v => if h : ∃ u, A.ancestor u v then some (imm A rank h) else none

omit hrank in
/-- The bag of a vertex: the vertex and its ancestors. -/
noncomputable def fbag : Option V → Finset V
  | none => ∅
  | some v => insert v (Finset.univ.filter fun u => A.ancestor u v)

/-- The height measure decreasing along the parent map. -/
noncomputable def height : Option V → ℕ
  | none => 0
  | some v => rank v + 1

theorem fparent_iterate : ∀ (n : ℕ) (x : Option V), height rank x ≤ n →
    (fparent A rank)^[n] x = none := by
  intro n
  induction n with
  | zero =>
    rintro (_ | v) h
    · rfl
    · simp [height] at h
  | succ n ih =>
    rintro (_ | v) h
    · exact Function.iterate_fixed rfl _
    · rw [Function.iterate_succ_apply]
      apply ih
      simp only [fparent]
      split_ifs with hv
      · have := hrank (imm_anc A rank hv)
        simp only [height] at h ⊢
        omega
      · simp [height]

theorem card_fbag_le (x : Option V) : (fbag A x).card ≤ t := by
  obtain _ | v := x
  · simp [fbag]
  · calc (fbag A (some v)).card ≤ (Finset.univ : Finset (Fin t)).card := by
          apply Finset.card_le_card_of_injOn rank (fun _ _ => Finset.mem_univ _)
          intro x hx y hy hxy
          simp only [fbag, Finset.coe_insert, Finset.coe_filter, Finset.mem_univ, true_and,
            Set.mem_insert_iff, Set.mem_ofPred_eq] at hx hy
          rcases hx with rfl | hx <;> rcases hy with rfl | hy
          · rfl
          · exact absurd hxy (hrank hy).ne'
          · exact absurd hxy (hrank hx).ne
          · rcases anc_trichotomy A hx hy with e | e | e
            · exact e
            · exact absurd hxy (hrank e).ne
            · exact absurd hxy (hrank e).ne'
      _ = t := by simp

end FromForest

/--
---
conclusion: Lax461425.TreedepthForestwidth.forestwidthLE_of_treedepthLE
---
The nodes are the vertices below a new root; the parent of a vertex is its immediate
ancestor (the ancestor of largest rank), or the new root, and its bag consists of the vertex
and its ancestors. Bags are chains, so ranks are injective on them; ranks decrease towards
the root, so the depth is at most `t`. A vertex `v` leaves the bags exactly at the node `v`.
-/
theorem forestwidthLE_of_treedepthLE {t : ℕ} {F : Pattern} (h : TreedepthLE t F) :
    ForestwidthLE t (t - 1) F := by
  classical
  obtain ⟨A, hedge, rank, hrank⟩ := h
  refine ⟨{
    Node := Option (F.A ⊕ F.B)
    root := none
    parent := fparent A rank
    parent_root := rfl
    depth_le := fun x => fparent_iterate A rank hrank t x ?_
    bag := fbag A
    bag_root := rfl
    card_bag_le := fun x => (card_fbag_le A rank hrank x).trans (by omega)
    exists_mem_bag := fun v => ⟨some v, by simp [fbag]⟩
    exists_edge_mem_bag := ?_
    connected := ?_ }⟩
  · obtain _ | v := x
    · simp [height]
    · simp only [height]
      have := (rank v).isLt
      omega
  · intro a b hab
    have hadj : (underlying F).Adj (Sum.inl a) (Sum.inr b) := by
      simp only [underlying, SimpleGraph.fromRel_adj]
      exact ⟨Sum.inl_ne_inr, Or.inl ⟨a, b, rfl, rfl, hab⟩⟩
    rcases hedge hadj with h | h
    · exact ⟨some (Sum.inr b), by simp [fbag, h]⟩
    · exact ⟨some (Sum.inl a), by simp [fbag, h]⟩
  · have key : ∀ (v : F.A ⊕ F.B) (x : Option (F.A ⊕ F.B)), v ∈ fbag A x →
        v ∉ fbag A (fparent A rank x) → x = some v := by
      rintro v (_ | z) hx hpx
      · simp [fbag] at hx
      simp only [fbag, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rcases hx with rfl | hx
      · rfl
      exfalso
      apply hpx
      have hz : ∃ u, A.ancestor u z := ⟨v, hx⟩
      simp only [fparent, hz, dif_pos, fbag, Finset.mem_insert, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact anc_imm A rank hrank hz hx
    intro v x x' hx hpx hx' hpx'
    rw [key v x hx hpx, key v x' hx' hpx']

end Lax461425Proofs.TreedepthForestwidth
