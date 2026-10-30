import Lax461425Proofs.NUDefs

namespace Lax461425Proofs.NU

open Lax461425.HomomorphismPolynomials Lax461425.NonUniformClosure

open scoped Classical

/-- Label families over `ψ` satisfying the CFI constraints. -/
def robAlg_Set {U V : Type} [Fintype V] {F : SimpleGraph U} {G : SimpleGraph V} (ψ : F →g G)
    (W : V → ZMod 2) : Type :=
  {T : (a : U) → G.neighborSet (ψ a) → ZMod 2 //
    (∀ a, ∑ u, T a u = W (ψ a)) ∧
    ∀ a b (h : F.Adj a b), T a ⟨ψ b, ψ.map_rel h⟩ = T b ⟨ψ a, ψ.map_rel h.symm⟩}

theorem robAlg_sum_transport {V : Type} [Fintype V] {G : SimpleGraph V} {W : V → ZMod 2}
    (x : CfiV G W) (v : V) (hv : x.vertex = v) :
    ∑ u : G.neighborSet v, x.label ⟨u.1, by subst hv; exact u.2⟩ = W v := by
  obtain ⟨vx, l, s⟩ := x
  simp only at hv
  subst hv
  simpa using s

theorem robAlg_adj_transport {V : Type} [Fintype V] {G : SimpleGraph V} {W : V → ZMod 2}
    (x y : CfiV G W) (hadj : (cfi G W).Adj x y) (p q : V) (hx : x.vertex = p) (hy : y.vertex = q)
    (hu : q ∈ G.neighborSet x.vertex) (hu' : p ∈ G.neighborSet y.vertex) :
    x.label ⟨q, hu⟩ = y.label ⟨p, hu'⟩ := by
  subst hx hy
  exact hadj.2

theorem robAlg_cfiV_ext {V : Type} [Fintype V] {G : SimpleGraph V} {W : V → ZMod 2}
    (x y : CfiV G W) (hv : x.vertex = y.vertex)
    (hl : ∀ u (hu : u ∈ G.neighborSet x.vertex) (hu' : u ∈ G.neighborSet y.vertex),
      x.label ⟨u, hu⟩ = y.label ⟨u, hu'⟩) : x = y := by
  obtain ⟨vx, l, s⟩ := x
  obtain ⟨vy, l', s'⟩ := y
  simp only at hv
  subst hv
  have : l = l' := funext fun u => by simpa using hl u.1 u.2 u.2
  subst this
  rfl

noncomputable def robAlg_equiv {U V : Type} [Fintype V] {F : SimpleGraph U} {G : SimpleGraph V}
    (ψ : F →g G) (W : V → ZMod 2) :
    {h : F →g cfi G W // ∀ x, (h x).vertex = ψ x} ≃ robAlg_Set ψ W where
  toFun h := ⟨fun a u => (h.1 a).label ⟨u.1, by rw [h.2 a]; exact u.2⟩,
    fun a => robAlg_sum_transport (h.1 a) (ψ a) (h.2 a),
    fun a b hab => by
      exact robAlg_adj_transport _ _ (h.1.map_rel hab) _ _ (h.2 a) (h.2 b) _ _⟩
  invFun T := ⟨⟨fun a => ⟨ψ a, T.1 a, T.2.1 a⟩, fun {a b} hab => ⟨ψ.map_rel hab, T.2.2 a b hab⟩⟩,
    fun _ => rfl⟩
  left_inv h := by
    apply Subtype.ext
    apply RelHom.ext
    intro a
    apply robAlg_cfiV_ext
    · exact (h.2 a).symm
    · intro u hu hu'
      rfl
  right_inv T := by
    apply Subtype.ext
    rfl

theorem robAlg_cnt {U V : Type} [Fintype V] {F : SimpleGraph U} {G : SimpleGraph V}
    (ψ : F →g G) (W : V → ZMod 2) : cntOver ψ W = Nat.card (robAlg_Set ψ W) :=
  Nat.card_congr (robAlg_equiv ψ W)

def robAlg_add {U V : Type} [Fintype V] {F : SimpleGraph U} {G : SimpleGraph V}
    (ψ : F →g G) {W1 W2 W3 : V → ZMod 2} (hW : ∀ v, W1 v + W2 v = W3 v)
    (t1 : robAlg_Set ψ W1) (t2 : robAlg_Set ψ W2) : robAlg_Set ψ W3 :=
  ⟨fun a u => t1.1 a u + t2.1 a u,
    fun a => by
      rw [Finset.sum_add_distrib, t1.2.1 a, t2.2.1 a, hW],
    fun a b h => by
      simp only [t1.2.2 a b h, t2.2.2 a b h]⟩

theorem robAlg_card_eq {U V : Type} [Fintype V] {F : SimpleGraph U} {G : SimpleGraph V}
    (ψ : F →g G) (W : V → ZMod 2) (t : robAlg_Set ψ W) :
    Nat.card (robAlg_Set ψ W) = Nat.card (robAlg_Set ψ 0) := by
  have hW : ∀ v, W v + W v = (0 : V → ZMod 2) v := fun v => by
    have : ∀ x : ZMod 2, x + x = 0 := by decide
    exact this _
  have hW' : ∀ v, (0 : V → ZMod 2) v + W v = W v := fun v => by simp
  symm
  refine Nat.card_congr
    { toFun := fun s => robAlg_add ψ hW' s t
      invFun := fun s => robAlg_add ψ hW s t
      left_inv := fun s => ?_
      right_inv := fun s => ?_ }
  · apply Subtype.ext
    funext a u
    show s.1 a u + t.1 a u + t.1 a u = s.1 a u
    have h2 : ∀ x y : ZMod 2, y + x + x = y := by decide
    exact h2 _ _
  · apply Subtype.ext
    funext a u
    show s.1 a u + t.1 a u + t.1 a u = s.1 a u
    have h2 : ∀ x y : ZMod 2, y + x + x = y := by decide
    exact h2 _ _

theorem cntOver_dichotomy {U V : Type} [Fintype U] [Fintype V] {F : SimpleGraph U}
    {G : SimpleGraph V} (ψ : F →g G) (v₀ : V) :
    0 < cntOver ψ 0 ∧
      (cntOver ψ (Pi.single v₀ 1) = 0 ∨ cntOver ψ (Pi.single v₀ 1) = cntOver ψ 0) := by
  rw [robAlg_cnt, robAlg_cnt]
  have hne : Nonempty (robAlg_Set ψ 0) :=
    ⟨⟨fun _ _ => 0, fun a => by simp, fun a b h => rfl⟩⟩
  have hfin : Finite (robAlg_Set ψ 0) := by
    unfold robAlg_Set; infer_instance
  refine ⟨Nat.card_pos, ?_⟩
  by_cases h : Nonempty (robAlg_Set ψ (Pi.single v₀ 1))
  · right
    obtain ⟨t⟩ := h
    exact robAlg_card_eq ψ _ t
  · left
    rw [not_nonempty_iff] at h
    exact Nat.card_of_isEmpty
end Lax461425Proofs.NU
