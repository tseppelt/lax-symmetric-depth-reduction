import Lax461425Proofs.NUDefs
import Mathlib

namespace Lax461425Proofs.NU

open Lax461425.HomomorphismPolynomials Lax461425.NonUniformClosure

open scoped Classical

theorem eval_hom {K : Type*} [CommSemiring K] (F : Pattern) (N : ℕ) (R : Fin N → Fin N → Prop) :
    (MvPolynomial.eval (fun p : Fin N × Fin N => if R p.1 p.2 then (1 : K) else 0)) (hom K F N) =
      (homBip F R : K) := by
  simp only [hom, map_sum, map_prod, map_pow, MvPolynomial.eval_X]
  have key : ∀ (hA : F.A → Fin N) (hB : F.B → Fin N),
      (∏ a, ∏ b, (if R (hA a) (hB b) then (1 : K) else 0) ^ F.mult a b) =
        if (∀ a b, F.mult a b ≠ 0 → R (hA a) (hB b)) then 1 else 0 := by
    intro hA hB
    split_ifs with h
    · apply Finset.prod_eq_one; intro a _; apply Finset.prod_eq_one; intro b _
      by_cases hm : F.mult a b = 0
      · simp [hm]
      · simp [h a b hm]
    · push Not at h
      obtain ⟨a, b, hm, hr⟩ := h
      apply Finset.prod_eq_zero (Finset.mem_univ a)
      apply Finset.prod_eq_zero (Finset.mem_univ b)
      simp [hr, hm]
  simp_rw [key]
  unfold homBip
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum,
    Fintype.sum_prod_type]
  simp

/-- Padding with `N - |X|` isolated vertices on the left and `N - |Y|` on the right. -/
theorem homBip_pad (F : Pattern) {X Y : Type} [Finite X] [Finite Y] (R : X → Y → Prop) {N : ℕ}
    (e : X ↪ Fin N) (f : Y ↪ Fin N) :
    homBip F (fun i j : Fin N => ∃ x y, e x = i ∧ f y = j ∧ R x y) =
      N ^ ((Nat.card F.A - Nat.card (nzPat F).A) + (Nat.card F.B - Nat.card (nzPat F).B)) *
        homBip (nzPat F) R := by
  set R' : Fin N → Fin N → Prop := fun i j => ∃ x y, e x = i ∧ f y = j ∧ R x y with hR'
  let isoA := {a : F.A // ¬ ∃ b, F.mult a b ≠ 0}
  let isoB := {b : F.B // ¬ ∃ a, F.mult a b ≠ 0}
  let g : (({p : ((nzPat F).A → X) × ((nzPat F).B → Y) // ∀ a b, (nzPat F).mult a b ≠ 0 → R (p.1 a) (p.2 b)}) ×
      (isoA → Fin N) × (isoB → Fin N)) →
      {p : (F.A → Fin N) × (F.B → Fin N) // ∀ a b, F.mult a b ≠ 0 → R' (p.1 a) (p.2 b)} :=
    fun s => ⟨(fun a => if h : ∃ b, F.mult a b ≠ 0 then e (s.1.1.1 ⟨a, h⟩) else s.2.1 ⟨a, h⟩,
      fun b => if h : ∃ a, F.mult a b ≠ 0 then f (s.1.1.2 ⟨b, h⟩) else s.2.2 ⟨b, h⟩), by
        intro a b hm
        have ha : ∃ b, F.mult a b ≠ 0 := ⟨b, hm⟩
        have hb : ∃ a, F.mult a b ≠ 0 := ⟨a, hm⟩
        simp only [dif_pos ha, dif_pos hb]
        exact ⟨_, _, rfl, rfl, s.1.2 ⟨a, ha⟩ ⟨b, hb⟩ hm⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨⟨⟨xs, ys⟩, hs⟩, ha, hb⟩ ⟨⟨⟨xs', ys'⟩, hs'⟩, ha', hb'⟩ h
      have h1 := congrArg (fun p => p.1.1) h
      have h2 := congrArg (fun p => p.1.2) h
      simp only [g] at h1 h2
      have hxs : xs = xs' := by
        funext a
        have := congrFun h1 a.1
        simp only [dif_pos a.2] at this
        exact e.injective this
      have hys : ys = ys' := by
        funext b
        have := congrFun h2 b.1
        simp only [dif_pos b.2] at this
        exact f.injective this
      have hha : ha = ha' := by
        funext a
        have := congrFun h1 a.1
        simp only [dif_neg a.2] at this
        exact this
      have hhb : hb = hb' := by
        funext b
        have := congrFun h2 b.1
        simp only [dif_neg b.2] at this
        exact this
      subst hxs hys hha hhb
      rfl
    · rintro ⟨⟨hA, hB⟩, hp⟩
      have hxa : ∀ a : (nzPat F).A, ∃ x, e x = hA a.1 := by
        intro a
        obtain ⟨b, hb⟩ := a.2
        obtain ⟨x, y, hx, _, _⟩ := hp a.1 b hb
        exact ⟨x, hx⟩
      have hyb : ∀ b : (nzPat F).B, ∃ y, f y = hB b.1 := by
        intro b
        obtain ⟨a, ha⟩ := b.2
        obtain ⟨x, y, _, hy, _⟩ := hp a b.1 ha
        exact ⟨y, hy⟩
      choose xs hxs using hxa
      choose ys hys using hyb
      have hR : ∀ a b, (nzPat F).mult a b ≠ 0 → R (xs a) (ys b) := by
        intro a b hm
        obtain ⟨x, y, hx, hy, hr⟩ := hp a.1 b.1 hm
        have h1 : x = xs a := e.injective (hx.trans (hxs a).symm)
        have h2 : y = ys b := f.injective (hy.trans (hys b).symm)
        subst h1 h2
        exact hr
      refine ⟨⟨⟨(xs, ys), hR⟩, fun a => hA a.1, fun b => hB b.1⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · funext a
        simp only [g]
        by_cases h : ∃ b, F.mult a b ≠ 0
        · simp only [dif_pos h]; exact hxs ⟨a, h⟩
        · simp only [dif_neg h]
      · funext b
        simp only [g]
        by_cases h : ∃ a, F.mult a b ≠ 0
        · simp only [dif_pos h]; exact hys ⟨b, h⟩
        · simp only [dif_neg h]
  have hcard := Nat.card_eq_of_bijective g hg
  unfold homBip
  rw [← hcard, Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin N), Fintype.card_fin]
  have hA : Nat.card isoA = Nat.card F.A - Nat.card (nzPat F).A := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_compl _
  have hB : Nat.card isoB = Nat.card F.B - Nat.card (nzPat F).B := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_compl _
  rw [hA, hB, pow_add]
  ring

theorem evalp_fibre_card {S : Type} [Fintype S] (s0 : S) (c : ZMod 2) :
    Nat.card {T : S → ZMod 2 // ∑ u, T u = c} = 2 ^ (Fintype.card S - 1) := by
  let E : {T : S → ZMod 2 // ∑ u, T u = c} ≃ ({s : S // s ≠ s0} → ZMod 2) :=
    { toFun := fun T s => T.1 s.1
      invFun := fun T' => ⟨fun s => if h : s = s0 then c - ∑ s' : {s // s ≠ s0}, T' s' else T' ⟨s, h⟩, by
        rw [Fintype.sum_eq_add_sum_subtype_ne _ s0]
        have : ∀ x : {s // s ≠ s0}, (if h : (x : S) = s0 then c - ∑ s' : {s // s ≠ s0}, T' s'
            else T' ⟨x, h⟩) = T' x := fun x => by rw [dif_neg x.2]
        simp only [this, dif_pos]
        ring⟩
      left_inv := by
        rintro ⟨T, hT⟩
        apply Subtype.ext
        funext s
        by_cases h : s = s0
        · subst h
          simp only [dif_pos]
          rw [Fintype.sum_eq_add_sum_subtype_ne _ s] at hT
          rw [← hT]; ring
        · simp only [dif_neg h]
      right_inv := by
        intro T'
        funext s
        simp [s.2] }
  have h := Fintype.card_subtype_compl (fun s => s = s0)
  rw [Fintype.card_subtype_eq] at h
  rw [Nat.card_congr E, Nat.card_fun, Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card,
    Nat.card_eq_fintype_card]
  congr 2

/-- The CFI vertices as a sigma type. -/
def evalp_cfiVEquiv {V : Type} [Fintype V] (G : SimpleGraph V) (W : V → ZMod 2) :
    CfiV G W ≃ Σ v : V, {T : G.neighborSet v → ZMod 2 // ∑ u, T u = W v} where
  toFun p := ⟨p.vertex, p.label, p.sum_label⟩
  invFun q := ⟨q.1, q.2.1, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance finite_cfiV {V : Type} [Fintype V] (G : SimpleGraph V) (W : V → ZMod 2) :
    Finite (CfiV G W) :=
  Finite.of_injective (fun p : CfiV G W => (⟨p.vertex, p.label⟩ : Σ v : V, (G.neighborSet v → ZMod 2)))
    (by
      rintro ⟨v, l, hl⟩ ⟨v', l', hl'⟩ h
      simp only [Sigma.mk.inj_iff] at h
      obtain ⟨rfl, h⟩ := h
      simp only [heq_eq_eq] at h
      subst h
      rfl)

theorem card_cfiV {V : Type} [Fintype V] (G : SimpleGraph V) (W : V → ZMod 2)
    (hG : ∀ v, ∃ u, G.Adj v u) : Nat.card (CfiV G W) = cfiSize G := by
  rw [Nat.card_congr (evalp_cfiVEquiv G W), Nat.card_sigma]
  unfold cfiSize
  refine Finset.sum_congr rfl fun v _ => ?_
  obtain ⟨u, hu⟩ := hG v
  have := evalp_fibre_card (S := G.neighborSet v) ⟨u, hu⟩ (W v)
  rw [this, Set.ncard_eq_toFinset_card', Set.toFinset_card]

end Lax461425Proofs.NU
