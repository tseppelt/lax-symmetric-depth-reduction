import Lax461425Proofs.NUDefs
import Mathlib

namespace Lax461425Proofs.NU

open Lax461425.HomomorphismPolynomials Lax461425.NonUniformClosure

open scoped Classical

section Generic

variable {V X : Type} (U : SimpleGraph V) (H : SimpleGraph X)

/-- Admissible maps: edges go to equal or adjacent vertices. -/
def BipcAdm (h : V → X) : Prop := ∀ x y, U.Adj x y → h x = h y ∨ H.Adj (h x) (h y)

/-- Edges of `U` inside fibres of `h`. -/
def bipcFib (h : V → X) : SimpleGraph V where
  Adj x y := U.Adj x y ∧ h x = h y
  symm := ⟨fun _ _ hh => ⟨hh.1.symm, hh.2.symm⟩⟩
  loopless := ⟨fun _ hh => U.irrefl hh.1⟩

lemma bipc_reach_eq (h : V → X) {x y : V} (hr : (bipcFib U h).Reachable x y) : h x = h y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  induction hr with
  | refl => rfl
  | tail _ hs ih => exact ih.trans hs.2

lemma bipc_reach_induce (h : V → X) {x y : V} (hr : (bipcFib U h).Reachable x y) :
    ∃ hy : y ∈ {v | (bipcFib U h).Reachable v x}, 
      (U.induce {v | (bipcFib U h).Reachable v x}).Reachable ⟨x, SimpleGraph.Reachable.refl _⟩ ⟨y, hy⟩ := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  induction hr with
  | refl => exact ⟨SimpleGraph.Reachable.refl _, SimpleGraph.Reachable.refl _⟩
  | @tail b c _ hs ih =>
    obtain ⟨hb, hb'⟩ := ih
    have hcx : (bipcFib U h).Reachable c x := by
      have : (bipcFib U h).Reachable c b := SimpleGraph.Adj.reachable hs.symm
      exact this.trans hb
    refine ⟨hcx, hb'.trans (SimpleGraph.Adj.reachable ?_)⟩
    exact hs.1

/-- The partition into connected components of fibres. -/
noncomputable def bipcPart (h : V → X) : ConnPart U where
  setoid := (bipcFib U h).reachableSetoid
  connected := by
    intro a
    induction a using Quotient.inductionOn with
    | h x =>
      have hS : {v | Quotient.mk (bipcFib U h).reachableSetoid v =
          Quotient.mk (bipcFib U h).reachableSetoid x} = {v | (bipcFib U h).Reachable v x} := by
        ext v
        exact Quotient.eq (r := (bipcFib U h).reachableSetoid)
      rw [hS]
      haveI : Nonempty {v | (bipcFib U h).Reachable v x} := ⟨⟨x, SimpleGraph.Reachable.refl _⟩⟩
      refine ⟨fun ⟨y, hy⟩ ⟨z, hz⟩ => ?_⟩
      obtain ⟨_, h1⟩ := bipc_reach_induce U h (x := x) (y := y) hy.symm
      obtain ⟨_, h2⟩ := bipc_reach_induce U h (x := x) (y := z) hz.symm
      exact h1.symm.trans h2

variable {U H}

lemma bipc_compat {h : V → X} {𝓡 : ConnPart U}
    (hR : ∀ x y, 𝓡.setoid x y ↔ (bipcFib U h).Reachable x y) {x y : V} (hxy : 𝓡.setoid x y) :
    h x = h y :=
  bipc_reach_eq U h ((hR x y).1 hxy)

/-- Compatible map out of the quotient. -/
noncomputable def bipcLift {h : V → X} {𝓡 : ConnPart U}
    (hR : ∀ x y, 𝓡.setoid x y ↔ (bipcFib U h).Reachable x y) : Quotient 𝓡.setoid → X :=
  Quotient.lift h (fun _ _ hxy => bipc_compat hR hxy)

lemma bipcLift_hom {h : V → X} {𝓡 : ConnPart U} (hadm : BipcAdm U H h)
    (hR : ∀ x y, 𝓡.setoid x y ↔ (bipcFib U h).Reachable x y) {a b : Quotient 𝓡.setoid}
    (hab : 𝓡.quotientGraph.Adj a b) : H.Adj (bipcLift hR a) (bipcLift hR b) := by
  obtain ⟨hne, x, y, hxy, hx, hy⟩ := hab
  subst hx hy
  show H.Adj (h x) (h y)
  rcases hadm x y hxy with he | ha
  · exfalso
    apply hne
    exact Quotient.sound ((hR x y).2 (SimpleGraph.Adj.reachable ⟨hxy, he⟩))
  · exact ha

/-- The map `g ∘ proj` is admissible. -/
lemma bipc_comp_adm {𝓡 : ConnPart U} (g : 𝓡.quotientGraph →g H) :
    BipcAdm U H (fun x => g (𝓡.proj x)) := by
  intro x y hxy
  by_cases h : 𝓡.proj x = 𝓡.proj y
  · left; simp [h]
  · right
    exact g.map_rel ⟨h, x, y, hxy, rfl, rfl⟩

lemma bipc_comp_key {𝓡 : ConnPart U} (g : 𝓡.quotientGraph →g H) (x y : V) :
    (bipcFib U fun x => g (𝓡.proj x)).Reachable x y ↔ 𝓡.setoid x y := by
  constructor
  · intro hr
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    induction hr with
    | refl => exact 𝓡.setoid.refl _
    | @tail b c _ hstep ih =>
      refine 𝓡.setoid.trans ih ?_
      by_contra hne
      have hne' : 𝓡.proj b ≠ 𝓡.proj c := fun e => hne (Quotient.exact e)
      have h1 := g.map_rel (a := 𝓡.proj b) (b := 𝓡.proj c) ⟨hne', b, c, hstep.1, rfl, rfl⟩
      have e : g (𝓡.proj b) = g (𝓡.proj c) := hstep.2
      rw [e] at h1
      exact H.irrefl h1
  · intro hxy
    have hcon := 𝓡.connected (Quotient.mk 𝓡.setoid x)
    have hx : x ∈ {v | Quotient.mk 𝓡.setoid v = Quotient.mk 𝓡.setoid x} := rfl
    have hy : y ∈ {v | Quotient.mk 𝓡.setoid v = Quotient.mk 𝓡.setoid x} :=
      Quotient.sound (𝓡.setoid.symm hxy)
    have hr := hcon.preconnected ⟨x, hx⟩ ⟨y, hy⟩
    let φ : (U.induce {v | Quotient.mk 𝓡.setoid v = Quotient.mk 𝓡.setoid x}) →g
        bipcFib U fun x => g (𝓡.proj x) :=
      ⟨Subtype.val, fun {a b} hab => ⟨hab, by
        have h1 : 𝓡.proj a.1 = 𝓡.proj b.1 := a.2.trans b.2.symm
        show g (𝓡.proj a.1) = g (𝓡.proj b.1)
        rw [h1]⟩⟩
    exact hr.map φ

lemma bipc_comp_part {𝓡 : ConnPart U} (g : 𝓡.quotientGraph →g H) :
    bipcPart U (fun x => g (𝓡.proj x)) = 𝓡 := by
  have key := bipc_comp_key g
  obtain ⟨s, hs⟩ := 𝓡
  have e : (bipcFib U fun x => g (ConnPart.proj ⟨s, hs⟩ x)).reachableSetoid = s :=
    Setoid.ext key
  show ConnPart.mk _ _ = ConnPart.mk s hs
  congr

/-- The fibre of `h ↦ bipcPart h` over `𝓡` is `Hom(U/𝓡, H)`. -/
noncomputable def bipcFibreEquiv (𝓡 : ConnPart U) :
    (𝓡.quotientGraph →g H) ≃ {t : {h : V → X // BipcAdm U H h} // bipcPart U t.1 = 𝓡} :=
  Equiv.ofBijective
    (fun g => ⟨⟨fun x => g (𝓡.proj x), bipc_comp_adm g⟩, bipc_comp_part g⟩)
    (by
      constructor
      · intro g1 g2 hg
        have := congrArg (fun t => t.1.1) hg
        refine DFunLike.ext _ _ fun a => ?_
        induction a using Quotient.inductionOn with
        | h x => exact congrFun this x
      · rintro ⟨⟨h, hadm⟩, ht⟩
        have hR : ∀ x y, 𝓡.setoid x y ↔ (bipcFib U h).Reachable x y := by
          intro x y
          rw [← ht]
          exact Iff.rfl
        exact ⟨⟨bipcLift hR, fun hab => bipcLift_hom hadm hR hab⟩, rfl⟩)

end Generic

theorem bipc_generic {V X : Type} [Finite V] (U : SimpleGraph V) (H : SimpleGraph X)
    [Finite X] :
    Nat.card {h : V → X // BipcAdm U H h} =
      ∑ᶠ 𝓡 : ConnPart U, homCount 𝓡.quotientGraph H := by
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype X := Fintype.ofFinite X
  rw [finsum_eq_sum_of_fintype]
  let f : {h : V → X // BipcAdm U H h} → ConnPart U := fun t => bipcPart U t.1
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f)]
  rw [Nat.card_sigma]
  refine Finset.sum_congr rfl fun 𝓡 _ => ?_
  unfold homCount
  exact (Nat.card_congr (bipcFibreEquiv 𝓡)).symm

theorem homBip_BRel (F : Pattern) {X : Type} [Finite X] (H : SimpleGraph X) :
    homBip F (BRel H) =
      ∑ᶠ 𝓡 : ConnPart (underlying F), homCount 𝓡.quotientGraph H := by
  rw [← bipc_generic]
  unfold homBip
  refine Nat.card_congr ((Equiv.subtypeEquiv (Equiv.sumArrowEquivProdArrow F.A F.B X).symm ?_))
  rintro ⟨p1, p2⟩
  simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk, BipcAdm]
  constructor
  · intro hp x y hxy
    simp only [underlying, SimpleGraph.fromRel_adj] at hxy
    obtain ⟨-, hxy | hxy⟩ := hxy
    · obtain ⟨a, b, rfl, rfl, hab⟩ := hxy
      simpa [BRel] using hp a b hab
    · obtain ⟨a, b, rfl, rfl, hab⟩ := hxy
      have := hp a b hab
      simp only [BRel] at this
      simp only [Sum.elim_inl, Sum.elim_inr]
      rcases this with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  · intro hp a b hab
    have := hp (Sum.inl a) (Sum.inr b) (by simp [underlying, hab])
    simpa [BRel] using this

end Lax461425Proofs.NU
