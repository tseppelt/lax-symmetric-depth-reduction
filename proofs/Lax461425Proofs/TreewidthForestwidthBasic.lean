import Lax461425.Forestwidth

/-! Basic facts about bounded-depth decompositions: depths of nodes, the ancestor relation,
and the unique top node of each vertex. -/

namespace Lax461425Proofs.TreewidthForestwidthBasic

open Lax461425.HomomorphismPolynomials Lax461425.Forestwidth

variable {F : Pattern} {Δ k : ℕ} (D : DepthDecomposition F Δ k)

theorem iterate_root (i : ℕ) : D.parent^[i] D.root = D.root :=
  Function.iterate_fixed D.parent_root i

/-- The depth of a node: the least number of parent steps reaching the root. -/
noncomputable def depth (t : D.Node) : ℕ := sInf {i | D.parent^[i] t = D.root}

theorem iterate_depth (t : D.Node) : D.parent^[depth D t] t = D.root :=
  Nat.sInf_mem (s := {i | D.parent^[i] t = D.root}) ⟨Δ, D.depth_le t⟩

theorem depth_le_of {t : D.Node} {i : ℕ} (h : D.parent^[i] t = D.root) : depth D t ≤ i :=
  Nat.sInf_le h

theorem depth_le_Δ (t : D.Node) : depth D t ≤ Δ := depth_le_of D (D.depth_le t)

theorem depth_root : depth D D.root = 0 :=
  Nat.le_zero.mp (depth_le_of D (i := 0) rfl)

theorem eq_root_of_depth_eq_zero {t : D.Node} (h : depth D t = 0) : t = D.root := by
  have := iterate_depth D t
  rwa [h] at this

theorem depth_parent (t : D.Node) : depth D (D.parent t) = depth D t - 1 := by
  by_cases ht : t = D.root
  · subst ht; rw [D.parent_root]
    simp [depth_root]
  have h0 : depth D t ≠ 0 := fun h => ht (eq_root_of_depth_eq_zero D h)
  have h1 : depth D (D.parent t) ≤ depth D t - 1 := by
    apply depth_le_of
    rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel
      (Nat.pos_of_ne_zero h0)]
    exact iterate_depth D t
  have h2 : depth D t ≤ depth D (D.parent t) + 1 := by
    apply depth_le_of
    rw [Function.iterate_succ_apply]
    exact iterate_depth D _
  omega

theorem depth_iterate (t : D.Node) (i : ℕ) :
    depth D (D.parent^[i] t) = depth D t - i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', depth_parent, ih]
    omega

/-- `a` is an ancestor of `b` (or equal to it). -/
def IsAnc (a b : D.Node) : Prop := ∃ i, D.parent^[i] b = a

theorem isAnc_refl (a : D.Node) : IsAnc D a a := ⟨0, rfl⟩

theorem isAnc_parent (b : D.Node) : IsAnc D (D.parent b) b := ⟨1, rfl⟩

theorem isAnc_trans {a b c : D.Node} (h₁ : IsAnc D a b) (h₂ : IsAnc D b c) : IsAnc D a c := by
  obtain ⟨i, rfl⟩ := h₁
  obtain ⟨j, rfl⟩ := h₂
  exact ⟨i + j, Function.iterate_add_apply _ _ _ _⟩

theorem isAnc_total {a b c : D.Node} (h₁ : IsAnc D a c) (h₂ : IsAnc D b c) :
    IsAnc D a b ∨ IsAnc D b a := by
  obtain ⟨i, rfl⟩ := h₁
  obtain ⟨j, rfl⟩ := h₂
  rcases le_total i j with h | h
  · right
    refine ⟨j - i, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]
  · left
    refine ⟨i - j, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]

theorem depth_le_of_isAnc {a b : D.Node} (h : IsAnc D a b) : depth D a ≤ depth D b := by
  obtain ⟨i, rfl⟩ := h
  rw [depth_iterate]; omega

theorem depth_lt_of_isAnc {a b : D.Node} (h : IsAnc D a b) (hne : a ≠ b) :
    depth D a < depth D b := by
  obtain ⟨i, rfl⟩ := h
  rw [depth_iterate]
  have hi : i ≠ 0 := by rintro rfl; exact hne rfl
  have hb : depth D b ≠ 0 := by
    intro hb
    have := eq_root_of_depth_eq_zero D hb
    subst this
    exact hne (iterate_root D i)
  omega

theorem isAnc_antisymm {a b : D.Node} (h₁ : IsAnc D a b) (h₂ : IsAnc D b a) : a = b := by
  by_contra hne
  have := depth_lt_of_isAnc D h₁ hne
  have := depth_le_of_isAnc D h₂
  omega

theorem eq_root_of_parent_eq {t : D.Node} (h : D.parent t = t) : t = D.root := by
  have := D.depth_le t
  rwa [Function.iterate_fixed h] at this

/-- Walking up from a node containing `v`, the vertex `v` stays in the bags until it leaves. -/
theorem exists_exit {v : F.A ⊕ F.B} {b : D.Node} (hb : v ∈ D.bag b) :
    ∃ i, v ∉ D.bag (D.parent (D.parent^[i] b)) ∧ ∀ j ≤ i, v ∈ D.bag (D.parent^[j] b) := by
  set S := {i | v ∉ D.bag (D.parent^[i] b)}
  have hS : Δ ∈ S := by
    show v ∉ D.bag _
    rw [D.depth_le b, D.bag_root]; simp
  have hm : sInf S ∈ S := Nat.sInf_mem ⟨Δ, hS⟩
  have h0 : sInf S ≠ 0 := by
    intro h; rw [h] at hm; exact hm hb
  refine ⟨sInf S - 1, ?_, fun j hj => ?_⟩
  · rw [← Function.iterate_succ_apply' D.parent, Nat.succ_eq_add_one,
      Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)]
    exact hm
  · by_contra hc
    have := Nat.sInf_le (s := S) hc
    omega

/-- `t` is a top node of `v`: its bag contains `v` and its parent's bag does not. -/
def IsTop (v : F.A ⊕ F.B) (t : D.Node) : Prop := v ∈ D.bag t ∧ v ∉ D.bag (D.parent t)

theorem exists_isTop (v : F.A ⊕ F.B) : ∃ t, IsTop D v t := by
  obtain ⟨b, hb⟩ := D.exists_mem_bag v
  obtain ⟨i, hi, hj⟩ := exists_exit D hb
  exact ⟨_, hj i le_rfl, hi⟩

/-- The unique top node of a vertex. -/
noncomputable def top (v : F.A ⊕ F.B) : D.Node := (exists_isTop D v).choose

theorem isTop_top (v : F.A ⊕ F.B) : IsTop D v (top D v) := (exists_isTop D v).choose_spec

theorem mem_bag_top (v : F.A ⊕ F.B) : v ∈ D.bag (top D v) := (isTop_top D v).1

theorem eq_top {v : F.A ⊕ F.B} {t : D.Node} (h : IsTop D v t) : t = top D v :=
  D.connected v t (top D v) h.1 h.2 (isTop_top D v).1 (isTop_top D v).2

theorem top_ne_root (v : F.A ⊕ F.B) : top D v ≠ D.root := by
  intro h
  have := mem_bag_top D v
  rw [h, D.bag_root] at this
  simp at this

theorem isAnc_top {v : F.A ⊕ F.B} {b : D.Node} (hb : v ∈ D.bag b) : IsAnc D (top D v) b := by
  obtain ⟨i, hi, hj⟩ := exists_exit D hb
  exact ⟨i, eq_top D ⟨hj i le_rfl, hi⟩⟩

end Lax461425Proofs.TreewidthForestwidthBasic
