import Lax461425Proofs.DepthHierarchyRichDefs
import Lax461425.Oddomorphisms

/-!
Oddomorphisms (even weak ones) reflect richness.
-/

namespace Lax461425Proofs.DepthHierarchy

open Lax461425 Lax461425.Oddomorphisms

section Oddo

variable {V W : Type*} {H : SimpleGraph V} {G : SimpleGraph W}

/-- Restricted oddomorphism data: `A ⊆ V` (closed under neighbours over `U`) maps to `U ⊆ W`, with
a fixed designation `o` of the odd vertices. -/
structure OddoOn (ψ : H →g G) (o : V → Prop) (A : Set V) (U : Set W) : Prop where
  maps : ∀ a ∈ A, ψ a ∈ U
  closed : ∀ a ∈ A, ∀ b, H.Adj a b → ψ b ∈ U → b ∈ A
  odd : ∀ a ∈ A, o a → ∀ x ∈ U, G.Adj (ψ a) x → Odd (neighborsOver ψ a x).ncard
  even : ∀ a ∈ A, ¬ o a → ∀ x ∈ U, G.Adj (ψ a) x → Even (neighborsOver ψ a x).ncard
  fibre : ∀ x ∈ U, Odd {a | a ∈ A ∧ ψ a = x ∧ o a}.ncard

variable {ψ : H →g G} {o : V → Prop} {A C : Set V} {U : Set W}

theorem OddoOn.restrict (h : OddoOn ψ o A U) {U' : Set W} (hU : U' ⊆ U) :
    OddoOn ψ o (A ∩ ψ ⁻¹' U') U' where
  maps a ha := ha.2
  closed a ha b hab hb := ⟨h.closed a ha.1 b hab (hU hb), hb⟩
  odd a ha ho x hx hadj := h.odd a ha.1 ho x (hU hx) hadj
  even a ha ho x hx hadj := h.even a ha.1 ho x (hU hx) hadj
  fibre x hx := by
    have : {a | a ∈ A ∩ ψ ⁻¹' U' ∧ ψ a = x ∧ o a} = {a | a ∈ A ∧ ψ a = x ∧ o a} := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨⟨h1, _⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2 ▸ hx⟩, h2, h3⟩
    rw [this]; exact h.fibre x (hU hx)

theorem OddoOn.sub (h : OddoOn ψ o A U) (hC : C ⊆ A)
    (hcl : ∀ a ∈ C, ∀ b ∈ A, H.Adj a b → b ∈ C)
    (hf : ∀ x ∈ U, Odd {a | a ∈ C ∧ ψ a = x ∧ o a}.ncard) : OddoOn ψ o C U where
  maps a ha := h.maps a (hC ha)
  closed a ha b hab hb := hcl a ha b (h.closed a (hC ha) b hab hb) hab
  odd a ha := h.odd a (hC ha)
  even a ha := h.even a (hC ha)
  fibre := hf

open Classical in
theorem ncard_eq_sum [Fintype V] (p : V → Prop) :
    {a | p a}.ncard = ∑ a, if p a then 1 else 0 := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf, Finset.card_filter]

open Classical in
theorem OddoOn.cnt_adj [Finite V] (h : OddoOn ψ o A U) (hC : C ⊆ A)
    (hcl : ∀ a ∈ C, ∀ b ∈ A, H.Adj a b → b ∈ C) {x y : W} (hx : x ∈ U) (hy : y ∈ U)
    (hxy : G.Adj x y) :
    Odd {a | a ∈ C ∧ ψ a = x ∧ o a}.ncard ↔ Odd {a | a ∈ C ∧ ψ a = y ∧ o a}.ncard := by
  haveI := Fintype.ofFinite V
  -- F1 : counting edges
  have F1 : ∀ x y : W, x ∈ U → y ∈ U → G.Adj x y →
      (Odd {a | a ∈ C ∧ ψ a = x ∧ o a}.ncard ↔
        Odd (∑ a, ∑ b, if (a ∈ C ∧ ψ a = x ∧ H.Adj a b ∧ ψ b = y) then 1 else 0)) := by
    intro x y hx hy hxy
    have inner : ∀ a, (∑ b, if (a ∈ C ∧ ψ a = x ∧ H.Adj a b ∧ ψ b = y) then 1 else 0) % 2
        = (if (a ∈ C ∧ ψ a = x ∧ o a) then 1 else 0) % 2 := by
      intro a
      by_cases hax : a ∈ C ∧ ψ a = x
      · have e : (∑ b, if (a ∈ C ∧ ψ a = x ∧ H.Adj a b ∧ ψ b = y) then 1 else 0)
            = (neighborsOver ψ a y).ncard := by
          show _ = ({b | H.Adj a b ∧ ψ b = y}).ncard
          rw [ncard_eq_sum]
          apply Finset.sum_congr rfl
          intro b _
          simp [hax]
        rw [e]
        have hadj : G.Adj (ψ a) y := hax.2 ▸ hxy
        by_cases hoa : o a
        · have := h.odd a (hC hax.1) hoa y hy hadj
          simp [hax, hoa, Nat.odd_iff.mp this]
        · have := h.even a (hC hax.1) hoa y hy hadj
          simp [hax, hoa, Nat.even_iff.mp this]
      · have h2 : ¬ (a ∈ C ∧ ψ a = x ∧ o a) := fun hh => hax ⟨hh.1, hh.2.1⟩
        simp only [h2, if_false]
        rw [Finset.sum_eq_zero]
        intro b _
        rw [if_neg]
        exact fun hh => hax ⟨hh.1, hh.2.1⟩
    rw [ncard_eq_sum, Nat.odd_iff, Nat.odd_iff, Finset.sum_nat_mod,
      Finset.sum_nat_mod (f := fun a => ∑ b, if (a ∈ C ∧ ψ a = x ∧ H.Adj a b ∧ ψ b = y) then 1 else 0)]
    simp only [inner]
    first | exact Iff.rfl | convert Iff.rfl
  have F2 : (∑ a, ∑ b, if (a ∈ C ∧ ψ a = x ∧ H.Adj a b ∧ ψ b = y) then 1 else 0) =
      (∑ a, ∑ b, if (a ∈ C ∧ ψ a = y ∧ H.Adj a b ∧ ψ b = x) then 1 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro a _
    apply if_congr _ rfl rfl
    constructor
    · rintro ⟨ha, hax, hab, hby⟩
      exact ⟨hcl a ha b (h.closed a (hC ha) b hab (hby ▸ hy)) hab, hby, hab.symm, hax⟩
    · rintro ⟨hb, hby, hba, hax⟩
      exact ⟨hcl b hb a (h.closed b (hC hb) a hba (hax ▸ hx)) hba, hax, hba.symm, hby⟩
  rw [F1 x y hx hy hxy, F1 y x hy hx hxy.symm, F2]

theorem OddoOn.cnt_const [Finite V] (h : OddoOn ψ o A U) (hU : (G.induce U).Preconnected)
    (hC : C ⊆ A) (hcl : ∀ a ∈ C, ∀ b ∈ A, H.Adj a b → b ∈ C) :
    ∀ x ∈ U, ∀ y ∈ U, (Odd {a | a ∈ C ∧ ψ a = x ∧ o a}.ncard ↔
      Odd {a | a ∈ C ∧ ψ a = y ∧ o a}.ncard) := by
  intro x hx y hy
  obtain ⟨w⟩ := hU ⟨x, hx⟩ ⟨y, hy⟩
  suffices K : ∀ (p q : U) (w : (G.induce U).Walk p q),
      (Odd {a | a ∈ C ∧ ψ a = p.1 ∧ o a}.ncard ↔ Odd {a | a ∈ C ∧ ψ a = q.1 ∧ o a}.ncard) from
    K ⟨x, hx⟩ ⟨y, hy⟩ w
  intro p q w
  induction w with
  | nil => exact Iff.rfl
  | cons hadj _ ih => exact (h.cnt_adj hC hcl (Subtype.property _) (Subtype.property _) hadj).trans ih

theorem OddoOn.exists_connected [Finite V] (hU : (G.induce U).Connected) :
    ∀ (n : ℕ) (A : Set V), A.ncard = n → OddoOn ψ o A U →
      ∃ A' ⊆ A, OddoOn ψ o A' U ∧ (H.induce A').Connected := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hn h
  classical
  obtain ⟨x0, hx0⟩ : ∃ x, x ∈ U := ⟨hU.nonempty.some.1, hU.nonempty.some.2⟩
  have hne : ∃ a, a ∈ A := by
    obtain ⟨a, ha⟩ := Set.nonempty_of_ncard_ne_zero (h.fibre x0 hx0).pos.ne'
    exact ⟨a, ha.1⟩
  obtain ⟨a0, ha0⟩ := hne
  by_cases hc : (H.induce A).Connected
  · exact ⟨A, subset_rfl, h, hc⟩
  · have hpre : ¬ (H.induce A).Preconnected := fun hp =>
      hc { preconnected := hp, nonempty := ⟨⟨a0, ha0⟩⟩ }
    obtain ⟨u, v, huv⟩ : ∃ u v : A, ¬ (H.induce A).Reachable u v := by
      by_contra hh
      push_neg at hh
      exact hpre hh
    let C : Set V := {b | ∃ hb : b ∈ A, (H.induce A).Reachable u ⟨b, hb⟩}
    have hCA : C ⊆ A := fun b hb => hb.1
    have hcl : ∀ a ∈ C, ∀ b ∈ A, H.Adj a b → b ∈ C := by
      rintro a ⟨ha, hr⟩ b hb hab
      exact ⟨hb, hr.trans (SimpleGraph.Adj.reachable
        (show (H.induce A).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab))⟩
    have hcl' : ∀ a ∈ A \ C, ∀ b ∈ A, H.Adj a b → b ∈ A \ C := by
      rintro a ⟨ha, hna⟩ b hb hab
      refine ⟨hb, fun hbC => hna ?_⟩
      obtain ⟨_, hr⟩ := hbC
      exact ⟨ha, hr.trans (SimpleGraph.Adj.reachable
        (show (H.induce A).Adj ⟨b, hb⟩ ⟨a, ha⟩ from hab.symm))⟩
    have uC : u.1 ∈ C := ⟨u.2, SimpleGraph.Reachable.refl _⟩
    have vC : v.1 ∉ C := fun hv => huv (by obtain ⟨_, hr⟩ := hv; exact hr)
    have hD : A \ C ⊆ A := Set.diff_subset
    have cC := h.cnt_const hU.preconnected hCA hcl
    have cD := h.cnt_const hU.preconnected hD hcl'
    have split : {a | a ∈ A ∧ ψ a = x0 ∧ o a} =
        {a | a ∈ C ∧ ψ a = x0 ∧ o a} ∪ {a | a ∈ A \ C ∧ ψ a = x0 ∧ o a} := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_diff]
      constructor
      · rintro ⟨h1, h2, h3⟩
        by_cases hac : a ∈ C
        · exact Or.inl ⟨hac, h2, h3⟩
        · exact Or.inr ⟨⟨h1, hac⟩, h2, h3⟩
      · rintro (⟨h1, h2, h3⟩ | ⟨⟨h1, _⟩, h2, h3⟩)
        · exact ⟨hCA h1, h2, h3⟩
        · exact ⟨h1, h2, h3⟩
    have disj : Disjoint {a | a ∈ C ∧ ψ a = x0 ∧ o a} {a | a ∈ A \ C ∧ ψ a = x0 ∧ o a} := by
      refine Set.disjoint_left.2 fun a h1 h2 => h2.1.2 h1.1
    have hsum := h.fibre x0 hx0
    rw [split, Set.ncard_union_eq disj (Set.toFinite _) (Set.toFinite _)] at hsum
    by_cases hoC : Odd {a | a ∈ C ∧ ψ a = x0 ∧ o a}.ncard
    · have hCo := h.sub hCA hcl (fun x hx => (cC x0 hx0 x hx).1 hoC)
      have hlt : C.ncard < n := by
        rw [← hn]
        exact Set.ncard_lt_ncard (by rw [Set.ssubset_def]; exact ⟨hCA, fun hs => vC (hs v.2)⟩)
          (Set.toFinite _)
      obtain ⟨A', hA', hodd', hconn'⟩ := ih _ hlt C rfl hCo
      exact ⟨A', hA'.trans hCA, hodd', hconn'⟩
    · have hoD : Odd {a | a ∈ A \ C ∧ ψ a = x0 ∧ o a}.ncard := by
        rw [Nat.not_odd_iff_even] at hoC
        rcases Nat.even_or_odd {a | a ∈ A \ C ∧ ψ a = x0 ∧ o a}.ncard with hE | hO
        · exact absurd (Nat.even_add.2 ⟨fun _ => hE, fun _ => hoC⟩) (Nat.not_even_iff_odd.2 hsum)
        · exact hO
      have hDo := h.sub hD hcl' (fun x hx => (cD x0 hx0 x hx).1 hoD)
      have hlt : (A \ C).ncard < n := by
        rw [← hn]
        exact Set.ncard_lt_ncard (by rw [Set.ssubset_def]; exact ⟨hD, fun hs => (hs u.2).2 uC⟩)
          (Set.toFinite _)
      obtain ⟨A', hA', hodd', hconn'⟩ := ih _ hlt (A \ C) rfl hDo
      exact ⟨A', hA'.trans hD, hodd', hconn'⟩

theorem exists_rich_of_oddoOn [Finite V] (k : ℕ) :
    ∀ (j : ℕ) (S : Set W), RichSet G k j S → ∀ (ψ : H →g G) (o : V → Prop) (A : Set V),
      OddoOn ψ o A S → ∃ S' ⊆ A, RichSet H k j S'
  | 0, S, hS, ψ, o, A, hA => by
      obtain ⟨hSc, hSk⟩ : (G.induce S).Connected ∧ k + 1 ≤ S.ncard := hS
      obtain ⟨A0, hA0, hodd, hconn⟩ := OddoOn.exists_connected hSc _ A rfl hA
      refine ⟨A0, hA0, hconn, ?_⟩
      calc k + 1 ≤ S.ncard := hSk
        _ ≤ (ψ '' A0).ncard := by
          apply Set.ncard_le_ncard _ (Set.toFinite _)
          intro x hx
          obtain ⟨a, ha⟩ := Set.nonempty_of_ncard_ne_zero (hodd.fibre x hx).pos.ne'
          exact ⟨a, ha.1, ha.2.1⟩
        _ ≤ A0.ncard := Set.ncard_image_le (Set.toFinite _)
  | j + 1, S, hS, ψ, o, A, hA => by
      obtain ⟨hSc, T, hT, hdisj⟩ :
        (G.induce S).Connected ∧ ∃ T : Fin (k + 1) → Set W,
          (∀ i, T i ⊆ S ∧ RichSet G k j (T i)) ∧ Pairwise (Function.onFun Disjoint T) := hS
      obtain ⟨A0, hA0, hodd, hconn⟩ := OddoOn.exists_connected hSc _ A rfl hA
      have key : ∀ i, ∃ D ⊆ A0 ∩ ψ ⁻¹' (T i), RichSet H k j D := fun i =>
        exists_rich_of_oddoOn k j (T i) (hT i).2 ψ o _ (hodd.restrict (hT i).1)
      choose D hD1 hD2 using key
      refine ⟨A0, hA0, hconn, D, fun i => ⟨(hD1 i).trans Set.inter_subset_left, hD2 i⟩, ?_⟩
      intro i i' hne
      refine Set.disjoint_left.2 fun a ha ha' => ?_
      exact Set.disjoint_left.1 (hdisj hne) (hD1 i ha).2 (hD1 i' ha').2

end Oddo

theorem RichSet.map {V V' : Type*} {H : SimpleGraph V} {F : SimpleGraph V'} (f : H →g F)
    (hf : Function.Injective f) (k : ℕ) :
    ∀ (j : ℕ) (S : Set V), RichSet H k j S → RichSet F k j (f '' S)
  | 0, S, hS => by
      obtain ⟨hc, hk⟩ : (H.induce S).Connected ∧ k + 1 ≤ S.ncard := hS
      refine ⟨?_, by rw [Set.ncard_image_of_injective _ hf]; exact hk⟩
      let g : H.induce S →g F.induce (f '' S) :=
        ⟨fun x => ⟨f x.1, Set.mem_image_of_mem _ x.2⟩, fun hab => f.map_adj hab⟩
      refine hc.map g ?_
      rintro ⟨_, a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  | j + 1, S, hS => by
      obtain ⟨hc, T, hT, hdisj⟩ :
        (H.induce S).Connected ∧ ∃ T : Fin (k + 1) → Set V,
          (∀ i, T i ⊆ S ∧ RichSet H k j (T i)) ∧ Pairwise (Function.onFun Disjoint T) := hS
      refine ⟨?_, fun i => f '' T i, fun i => ⟨Set.image_mono (hT i).1,
        RichSet.map f hf k j _ (hT i).2⟩, ?_⟩
      · let g : H.induce S →g F.induce (f '' S) :=
          ⟨fun x => ⟨f x.1, Set.mem_image_of_mem _ x.2⟩, fun hab => f.map_adj hab⟩
        refine hc.map g ?_
        rintro ⟨_, a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
      · intro i i' hne
        exact (Set.disjoint_image_iff hf).2 (hdisj hne)

/-- Oddomorphisms (even weak) reflect richness. -/
theorem isRich_of_weakOddomorphism {V W : Type} [Finite V] [Finite W] {F : SimpleGraph V}
    {G : SimpleGraph W} (φ : F →g G) (hφ : IsWeakOddomorphism φ) {k Δ : ℕ}
    (hG : IsRich G k Δ) : IsRich F k Δ := by
  obtain ⟨F', hF'⟩ := hφ
  obtain ⟨S, hS⟩ := hG
  have hO : OddoOn (φ.comp F'.hom) (IsOdd (φ.comp F'.hom)) Set.univ Set.univ :=
    { maps := fun _ _ => Set.mem_univ _
      closed := fun _ _ _ _ _ => Set.mem_univ _
      odd := fun a _ ho x _ hadj => ho x hadj
      even := fun a _ ho x _ hadj =>
        (hF'.even_or_odd a).resolve_right ho x hadj
      fibre := fun x _ => by
        have := hF'.odd_card_fibre x
        simpa using this }
  have hO' := hO.restrict (Set.subset_univ S)
  obtain ⟨S', _, hS'⟩ := exists_rich_of_oddoOn k (Δ - 1) S hS (φ.comp F'.hom) _ _ hO'
  exact ⟨F'.hom '' S', RichSet.map F'.hom (fun a b h => Subtype.ext h) k _ S' hS'⟩

end Lax461425Proofs.DepthHierarchy
