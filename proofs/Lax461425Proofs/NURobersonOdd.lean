import Lax461425Proofs.NUDefs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace Lax461425Proofs.NU

open Lax461425.Oddomorphisms
open scoped Classical

section Aux

variable {U V : Type} [Fintype U] [Fintype V]

lemma robOdd_ncard_cast (A : U → U → Prop) (ψ : U → V) (a : U) (x : V) :
    (({b | A a b ∧ ψ b = x} : Set U).ncard : ZMod 2) =
      ∑ b, if A a b ∧ ψ b = x then (1 : ZMod 2) else 0 := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf, Finset.card_filter]
  push_cast
  rfl

lemma robOdd_ncard_cast' (P : U → Prop) :
    (({b | P b} : Set U).ncard : ZMod 2) = ∑ b, if P b then (1 : ZMod 2) else 0 := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf, Finset.card_filter]
  push_cast
  rfl

lemma robOdd_two (x : ZMod 2) : x + x = 0 := by revert x; decide

lemma robOdd_add_eq (x y : ZMod 2) (h : x + y = 0) : x = y := by revert x y; decide

lemma robOdd_01 (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

/-- Parity argument: no solution when there is an odd-type structure. -/
lemma robOdd_noSol {F : SimpleGraph U} {G : SimpleGraph V} (ψ : F →g G) (v₀ : V)
    (A : U → U → Prop) (hsymm : ∀ a b, A a b → A b a) (hirr : ∀ a, ¬ A a a)
    (hF : ∀ a b, A a b → F.Adj a b) (odd : U → Prop)
    (hodd : ∀ a, odd a → ∀ x, G.Adj (ψ a) x → Odd ({b | A a b ∧ ψ b = x} : Set U).ncard)
    (hev : ∀ a, ¬ odd a → ∀ x, G.Adj (ψ a) x → Even ({b | A a b ∧ ψ b = x} : Set U).ncard)
    (hfib : Odd ({a | ψ a = v₀ ∧ odd a} : Set U).ncard) :
    ¬ ∃ T : U → V → ZMod 2,
      (∀ a, ∑ u, (if G.Adj (ψ a) u then T a u else 0) = (Pi.single v₀ 1 : V → ZMod 2) (ψ a)) ∧
      ∀ a b, F.Adj a b → T a (ψ b) = T b (ψ a) := by
  rintro ⟨T, hT1, hT2⟩
  set o : U → ZMod 2 := fun a => if odd a then 1 else 0 with ho
  have claim1 : ∀ a, ∑ b, (if A a b then T a (ψ b) else 0) =
      o a * ∑ u, (if G.Adj (ψ a) u then T a u else 0) := by
    intro a
    have h1 : ∑ b, (if A a b then T a (ψ b) else 0) =
        ∑ u, ((({b | A a b ∧ ψ b = u} : Set U).ncard : ZMod 2) * T a u) := by
      simp_rw [robOdd_ncard_cast, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases h : A a b
      · simp [h]
      · simp [h]
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : G.Adj (ψ a) u
    · simp only [hu, if_true]
      by_cases hoa : odd a
      · have := (ZMod.natCast_eq_one_iff_odd).2 (hodd a hoa u hu)
        simp [ho, hoa, this]
      · have := (ZMod.natCast_eq_zero_iff_even).2 (hev a hoa u hu)
        simp [ho, hoa, this]
    · have : ({b | A a b ∧ ψ b = u} : Set U) = ∅ := by
        ext b
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hab hb
        exact hu (hb ▸ ψ.map_rel (hF a b hab))
      simp [hu, this]
  have claim2 : ∑ a, ∑ b, (if A a b then T a (ψ b) else 0) = 0 := by
    rw [← Fintype.sum_prod_type' (f := fun a b => if A a b then T a (ψ b) else 0)]
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · rintro ⟨a, b⟩ _
      by_cases h : A a b
      · have h' := hsymm a b h
        have := hT2 a b (hF a b h)
        simp [h, h', this, robOdd_two]
      · have h' : ¬ A b a := fun h'' => h (hsymm b a h'')
        simp [h, h']
    · rintro ⟨a, b⟩ _ hne
      intro heq
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      apply hne
      simp [hirr]
    · intro p _; exact Finset.mem_univ _
    · intro p _; simp
  simp_rw [claim1] at claim2
  simp_rw [hT1] at claim2
  have : ∑ a, o a * (Pi.single v₀ 1 : V → ZMod 2) (ψ a) =
      (({a | ψ a = v₀ ∧ odd a} : Set U).ncard : ZMod 2) := by
    rw [robOdd_ncard_cast']
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h1 : ψ a = v₀ <;> by_cases h2 : odd a <;> simp [ho, h1, h2, Pi.single_apply]
  rw [this] at claim2
  have := (ZMod.natCast_eq_one_iff_odd).2 hfib
  rw [claim2] at this
  exact zero_ne_one this

end Aux


section Trans

variable {U V : Type} [Fintype U] [Fintype V] {F : SimpleGraph U} {G : SimpleGraph V}

/-- The affine system over `ZMod 2` describing homomorphisms over `ψ`. -/
def RobSol (ψ : F →g G) (W : V → ZMod 2) : Prop :=
  ∃ T : U → V → ZMod 2,
    (∀ a, ∑ u, (if G.Adj (ψ a) u then T a u else 0) = W (ψ a)) ∧
    ∀ a b, F.Adj a b → T a (ψ b) = T b (ψ a)

/-- evaluation of a label at an arbitrary vertex. -/
noncomputable def robEv {W : V → ZMod 2} (p : CfiV G W) (u : V) : ZMod 2 :=
  if h : G.Adj p.vertex u then p.label ⟨u, h⟩ else 0

lemma robEv_sum {W : V → ZMod 2} (p : CfiV G W) :
    ∑ u, (if G.Adj p.vertex u then robEv p u else 0) = W p.vertex := by
  rw [← p.sum_label, ← Finset.sum_filter]
  have := Finset.sum_subtype (Finset.univ.filter (fun u => G.Adj p.vertex u))
    (p := fun u => u ∈ G.neighborSet p.vertex) (F := inferInstance) (by simp) (fun u => robEv p u)
  rw [this]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hu : G.Adj p.vertex u.1 := u.2
  simp only [robEv, dif_pos hu]


lemma robOdd_sum_nbr (v : V) (f : V → ZMod 2) :
    ∑ u : G.neighborSet v, f u.1 = ∑ u, (if G.Adj v u then f u else 0) := by
  rw [← Finset.sum_filter]
  have := Finset.sum_subtype (Finset.univ.filter (fun u => G.Adj v u))
    (p := fun u => u ∈ G.neighborSet v) (F := inferInstance) (by simp) f
  rw [this]

instance robOdd_finite (W : V → ZMod 2) : Finite (CfiV G W) := by
  refine Finite.of_injective (fun p : CfiV G W => (⟨p.vertex, p.label⟩ : Σ v, G.neighborSet v → ZMod 2)) ?_
  rintro ⟨v, l, s⟩ ⟨v', l', s'⟩ h
  simp only [Sigma.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  have := eq_of_heq h2
  subst this
  rfl

lemma robOdd_cnt_eq_zero_iff (ψ : F →g G) (W : V → ZMod 2) :
    cntOver ψ W = 0 ↔ ¬ RobSol ψ W := by
  haveI : Finite {h : F →g cfi G W // ∀ x, (h x).vertex = ψ x} :=
    Finite.of_injective (fun h => (h.1 : U → CfiV G W)) (fun h h' e => Subtype.ext (DFunLike.coe_injective e))
  have key : (¬ RobSol ψ W) ↔ IsEmpty {h : F →g cfi G W // ∀ x, (h x).vertex = ψ x} := by
    rw [← not_nonempty_iff]
    refine not_congr ⟨?_, ?_⟩
    · rintro ⟨T, h1, h2⟩
      refine ⟨⟨⟨fun a => ⟨ψ a, fun u => T a u.1, ?_⟩, ?_⟩, fun x => rfl⟩⟩
      · rw [robOdd_sum_nbr (G := G) (ψ a) (T a)]; exact h1 a
      · intro a b hab
        exact ⟨ψ.map_rel hab, h2 a b hab⟩
    · rintro ⟨⟨h, hv⟩⟩
      refine ⟨fun a u => robEv (h a) u, ?_, ?_⟩
      · intro a
        have := robEv_sum (h a)
        rwa [hv a] at this
      · intro a b hab
        obtain ⟨hh, he⟩ := h.map_rel hab
        have e1 : robEv (h a) (h b).vertex = robEv (h b) (h a).vertex := by
          simp only [robEv, dif_pos hh, dif_pos hh.symm, he]
        rwa [hv a, hv b] at e1
  unfold cntOver
  rw [Nat.card_eq_zero, key]
  simp [not_infinite_iff_finite.2 this]


lemma robOdd_nbrs_ncard (ψ : F →g G) (F' : F.Subgraph) (a : F'.verts) (x : V) :
    (neighborsOver (ψ.comp F'.hom) a x).ncard = ({b | F'.Adj a b ∧ ψ b = x} : Set U).ncard := by
  have : ({b | F'.Adj a b ∧ ψ b = x} : Set U) = Subtype.val '' neighborsOver (ψ.comp F'.hom) a x := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_image, neighborsOver]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨b, F'.edge_vert h1.symm⟩, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨b', ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, h2⟩
  rw [this, Set.ncard_image_of_injective _ Subtype.val_injective]

lemma robOdd_fibre_ncard (ψ : F →g G) (F' : F.Subgraph) (x : V) (Q : F'.verts → Prop) :
    ({a : F'.verts | (ψ.comp F'.hom) a = x ∧ Q a} : Set F'.verts).ncard =
      ({a : U | ψ a = x ∧ ∃ h : a ∈ F'.verts, Q ⟨a, h⟩} : Set U).ncard := by
  have : ({a : U | ψ a = x ∧ ∃ h : a ∈ F'.verts, Q ⟨a, h⟩} : Set U) =
      Subtype.val '' ({a : F'.verts | (ψ.comp F'.hom) a = x ∧ Q a} : Set F'.verts) := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨h1, h, h2⟩
      exact ⟨⟨b, h⟩, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨b', ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, b'.2, h2⟩
  rw [this, Set.ncard_image_of_injective _ Subtype.val_injective]

lemma robOdd_zero_of_weak [Nontrivial V] (ψ : F →g G) (v₀ : V) (hw : IsWeakOddomorphism ψ) :
    ¬ RobSol ψ (Pi.single v₀ 1) := by
  obtain ⟨F', hF'⟩ := hw
  refine robOdd_noSol ψ v₀ (fun a b => F'.Adj a b) (fun a b h => h.symm)
    (fun a h => F.irrefl (F'.adj_sub h)) (fun a b h => F'.adj_sub h)
    (fun a => ∃ h : a ∈ F'.verts, IsOdd (ψ.comp F'.hom) ⟨a, h⟩) ?_ ?_ ?_
  · rintro a ⟨h, ho⟩ x hx
    have := ho x hx
    rwa [robOdd_nbrs_ncard ψ F' ⟨a, h⟩ x] at this
  · intro a hna x hx
    by_cases h : a ∈ F'.verts
    · have hno : ¬ IsOdd (ψ.comp F'.hom) ⟨a, h⟩ := fun ho => hna ⟨h, ho⟩
      have := (hF'.even_or_odd ⟨a, h⟩).resolve_right hno x hx
      rwa [robOdd_nbrs_ncard ψ F' ⟨a, h⟩ x] at this
    · have : ({b | F'.Adj a b ∧ ψ b = x} : Set U) = ∅ := by
        ext b
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hab; exact absurd (F'.edge_vert hab) h
      rw [this]; simp
  · have := hF'.odd_card_fibre v₀
    rwa [robOdd_fibre_ncard ψ F' v₀ (fun a => IsOdd (ψ.comp F'.hom) a)] at this


lemma robOdd_S_const (hG : G.Connected) (ψ : F →g G) (v₀ : V) (A : U → U → Prop)
    (hsymm : ∀ a b, A a b → A b a) (α : U → ZMod 2)
    (hα : ∀ a u, G.Adj (ψ a) u → α a = ∑ b, if A a b ∧ ψ b = u then (1 : ZMod 2) else 0)
    (h0 : ∑ a, (if ψ a = v₀ then α a else 0) = 1) (x : V) :
    ∑ a, (if ψ a = x then α a else 0) = 1 := by
  have step : ∀ x y, G.Adj x y →
      ∑ a, (if ψ a = x then α a else 0) = ∑ a, (if ψ a = y then α a else 0) := by
    intro x y hxy
    have e1 : ∑ a, (if ψ a = x then α a else 0) =
        ∑ a, ∑ b, (if ψ a = x ∧ ψ b = y ∧ A a b then (1 : ZMod 2) else 0) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases h : ψ a = x
      · subst h
        rw [if_pos rfl, hα a y hxy]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases h1 : A a b <;> by_cases h2 : ψ b = y <;> simp [h1, h2]
      · simp [h]
    have e2 : ∑ a, (if ψ a = y then α a else 0) =
        ∑ a, ∑ b, (if ψ b = x ∧ ψ a = y ∧ A b a then (1 : ZMod 2) else 0) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases h : ψ a = y
      · subst h
        rw [if_pos rfl, hα a x hxy.symm]
        refine Finset.sum_congr rfl fun b _ => ?_
        have hiff : A a b ↔ A b a := ⟨hsymm a b, hsymm b a⟩
        by_cases h2 : ψ b = x <;> simp [h2, hiff]
      · simp [h]
    rw [e1, e2, Finset.sum_comm]
  have := hG.preconnected v₀ x
  rw [SimpleGraph.reachable_iff_reflTransGen] at this
  induction this with
  | refl => exact h0
  | tail _ hbc ih => rw [← step _ _ hbc, ih]


lemma robOdd_weak_of_data [Nontrivial V] (hG : G.Connected) (ψ : F →g G) (v₀ : V)
    (A : U → U → Prop) (hsymm : ∀ a b, A a b → A b a) (hF : ∀ a b, A a b → F.Adj a b)
    (α : U → ZMod 2)
    (hα : ∀ a u, G.Adj (ψ a) u → α a = ∑ b, if A a b ∧ ψ b = u then (1 : ZMod 2) else 0)
    (h0 : ∑ a, (if ψ a = v₀ then α a else 0) = 1) : IsWeakOddomorphism ψ := by
  let F' : F.Subgraph :=
    { verts := Set.univ, Adj := A, adj_sub := fun {a b} h => hF a b h,
      edge_vert := fun {a b} _ => Set.mem_univ a, symm := ⟨fun a b h => hsymm a b h⟩ }
  have hcnt : ∀ (a : F'.verts) x, G.Adj (ψ a) x →
      (((neighborsOver (ψ.comp F'.hom) a x).ncard : ℕ) : ZMod 2) = α a.1 := by
    intro a x hx
    rw [robOdd_nbrs_ncard, robOdd_ncard_cast, ← hα a.1 x hx]
  have hex : ∀ a : U, ∃ u, G.Adj (ψ a) u := by
    intro a
    obtain ⟨w, hw⟩ := exists_ne (ψ a)
    obtain ⟨p⟩ := hG.preconnected (ψ a) w
    cases p with
    | nil => exact absurd rfl hw
    | cons h _ => exact ⟨_, h⟩
  have hodd : ∀ a : F'.verts, IsOdd (ψ.comp F'.hom) a ↔ α a.1 = 1 := by
    intro a
    constructor
    · intro ho
      obtain ⟨u, hu⟩ := hex a.1
      rw [← hcnt a u hu]
      exact (ZMod.natCast_eq_one_iff_odd).2 (ho u hu)
    · intro h x hx
      rw [← hcnt a x hx] at h
      exact (ZMod.natCast_eq_one_iff_odd).1 h
  refine ⟨F', ?_, ?_⟩
  · intro a
    rcases robOdd_01 (α a.1) with h | h
    · left
      intro x hx
      rw [← hcnt a x hx] at h
      exact (ZMod.natCast_eq_zero_iff_even).1 h
    · right; exact (hodd a).2 h
  · intro x
    rw [robOdd_fibre_ncard ψ F' x (fun a => IsOdd (ψ.comp F'.hom) a)]
    have hset : ({a : U | ψ a = x ∧ ∃ h : a ∈ F'.verts, IsOdd (ψ.comp F'.hom) ⟨a, h⟩} : Set U) =
        {a : U | ψ a = x ∧ α a = 1} := by
      ext a
      simp only [Set.mem_ofPred_eq]
      refine and_congr_right fun _ => ?_
      constructor
      · rintro ⟨h, ho⟩; exact (hodd ⟨a, h⟩).1 ho
      · intro h1; exact ⟨Set.mem_univ a, (hodd ⟨a, Set.mem_univ a⟩).2 h1⟩
    rw [hset, ← ZMod.natCast_eq_one_iff_odd, robOdd_ncard_cast']
    refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) (robOdd_S_const hG ψ v₀ A hsymm α hα h0 x)
    by_cases h1 : ψ a = x
    · rcases robOdd_01 (α a) with h | h <;> simp [h1, h]
    · simp [h1]


section LinAlg

/-- the coefficient matrix of the system -/
noncomputable def robM (ψ : F →g G) : Matrix (U ⊕ (U × U)) (U × V) (ZMod 2) :=
  fun y x => Sum.elim (fun a => if x.1 = a ∧ G.Adj (ψ a) x.2 then (1 : ZMod 2) else 0)
    (fun p => if F.Adj p.1 p.2 then
      ((if x = (p.1, ψ p.2) then (1 : ZMod 2) else 0) + (if x = (p.2, ψ p.1) then 1 else 0))
      else 0) y

noncomputable def robC (ψ : F →g G) (W : V → ZMod 2) : U ⊕ (U × U) → ZMod 2 :=
  Sum.elim (fun a => W (ψ a)) (fun _ => 0)

lemma robM_mulVec_inl (ψ : F →g G) (T : U × V → ZMod 2) (a : U) :
    (robM ψ).mulVec T (Sum.inl a) = ∑ u, (if G.Adj (ψ a) u then T (a, u) else 0) := by
  simp only [Matrix.mulVec, dotProduct, robM, Sum.elim_inl]
  rw [Fintype.sum_prod_type]
  simp [ite_and, ite_mul]

lemma robM_mulVec_inr (ψ : F →g G) (T : U × V → ZMod 2) (p : U × U) :
    (robM ψ).mulVec T (Sum.inr p) =
      if F.Adj p.1 p.2 then T (p.1, ψ p.2) + T (p.2, ψ p.1) else 0 := by
  simp only [Matrix.mulVec, dotProduct, robM, Sum.elim_inr]
  by_cases h : F.Adj p.1 p.2
  · simp [h, add_mul, Finset.sum_add_distrib]
  · simp [h]

lemma robOdd_sol_of_mulVec (ψ : F →g G) (W : V → ZMod 2) (T : U × V → ZMod 2)
    (h : (robM ψ).mulVec T = robC ψ W) : RobSol ψ W := by
  refine ⟨fun a u => T (a, u), fun a => ?_, fun a b hab => ?_⟩
  · have := congrFun h (Sum.inl a)
    rw [robM_mulVec_inl] at this
    exact this
  · have := congrFun h (Sum.inr (a, b))
    rw [robM_mulVec_inr] at this
    simp only [robC, Sum.elim_inr, if_pos hab] at this
    exact robOdd_add_eq _ _ this


lemma robOdd_data (ψ : F →g G) (v₀ : V) (hns : ¬ RobSol ψ (Pi.single v₀ 1)) :
    ∃ (α : U → ZMod 2) (β : U × U → ZMod 2),
      (∀ a u, G.Adj (ψ a) u →
        α a = ∑ b, if F.Adj a b ∧ ψ b = u then β (a, b) + β (b, a) else 0) ∧
      ∑ a, (if ψ a = v₀ then α a else 0) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : robC ψ (Pi.single v₀ 1) ∉ LinearMap.range (robM ψ).mulVecLin := by
    rintro ⟨T, hT⟩
    exact hns (robOdd_sol_of_mulVec ψ _ T hT)
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hc
    (by have := Module.Free.of_divisionRing (ZMod 2) ((U ⊕ U × U → ZMod 2) ⧸ LinearMap.range (robM ψ).mulVecLin); infer_instance)
  have hf0 : ∀ T, f ((robM ψ).mulVec T) = 0 := by
    intro T
    have := Submodule.mem_map_of_mem (f := f) (LinearMap.mem_range_self (robM ψ).mulVecLin T)
    rw [hf2] at this
    simpa using this
  set φ : U ⊕ (U × U) → ZMod 2 := fun y => f (fun j => if y = j then 1 else 0) with hφ
  have hexp : ∀ z, f z = ∑ y, z y * φ y := fun z => by
    rw [LinearMap.pi_apply_eq_sum_univ f z]; rfl
  have hcol : ∀ x : U × V, ∑ y, robM ψ y x * φ y = 0 := by
    intro x
    have := hf0 (fun x' => if x = x' then 1 else 0)
    rw [hexp] at this
    convert this using 2 with y
    simp [Matrix.mulVec, dotProduct]
  have hcol' : ∀ a₀ u₀, (if G.Adj (ψ a₀) u₀ then φ (Sum.inl a₀) else 0) +
      ∑ b, (if F.Adj a₀ b ∧ ψ b = u₀ then φ (Sum.inr (a₀, b)) + φ (Sum.inr (b, a₀)) else 0) = 0 := by
    intro a₀ u₀
    have := hcol (a₀, u₀)
    rw [Fintype.sum_sum_type] at this
    simp only [robM, Sum.elim_inl, Sum.elim_inr] at this
    rw [Fintype.sum_prod_type] at this
    have e1 : ∑ a₁, (if a₀ = a₁ ∧ G.Adj (ψ a₁) u₀ then (1 : ZMod 2) else 0) * φ (Sum.inl a₁) =
        if G.Adj (ψ a₀) u₀ then φ (Sum.inl a₀) else 0 := by
      simp [ite_and, ite_mul]
    have e2 : ∑ x, ∑ y, (if F.Adj (x, y).1 (x, y).2 then
              (if (a₀, u₀) = ((x, y).1, ψ (x, y).2) then (1 : ZMod 2) else 0) +
                if (a₀, u₀) = ((x, y).2, ψ (x, y).1) then 1 else 0
            else 0) * φ (Sum.inr (x, y)) =
        ∑ b, (if F.Adj a₀ b ∧ ψ b = u₀ then φ (Sum.inr (a₀, b)) + φ (Sum.inr (b, a₀)) else 0) := by
      have s1 : ∀ x y, (if F.Adj (x, y).1 (x, y).2 then
              (if (a₀, u₀) = ((x, y).1, ψ (x, y).2) then (1 : ZMod 2) else 0) +
                if (a₀, u₀) = ((x, y).2, ψ (x, y).1) then 1 else 0
            else 0) * φ (Sum.inr (x, y)) =
          (if a₀ = x ∧ F.Adj x y ∧ ψ y = u₀ then φ (Sum.inr (x, y)) else 0) +
          (if a₀ = y ∧ F.Adj x y ∧ ψ x = u₀ then φ (Sum.inr (x, y)) else 0) := by
        intro x y
        by_cases h : F.Adj x y <;> simp [h, Prod.ext_iff, add_mul, ite_and, ite_mul, and_comm, eq_comm]
      simp_rw [s1, Finset.sum_add_distrib]
      have t1 : ∑ x, ∑ x_1, (if a₀ = x ∧ F.Adj x x_1 ∧ ψ x_1 = u₀ then φ (Sum.inr (x, x_1)) else 0) =
          ∑ b, if F.Adj a₀ b ∧ ψ b = u₀ then φ (Sum.inr (a₀, b)) else 0 := by
        simp [ite_and, Finset.sum_ite_eq]
      have t2 : ∑ x, ∑ x_1, (if a₀ = x_1 ∧ F.Adj x x_1 ∧ ψ x = u₀ then φ (Sum.inr (x, x_1)) else 0) =
          ∑ b, if F.Adj a₀ b ∧ ψ b = u₀ then φ (Sum.inr (b, a₀)) else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [ite_and]
        rw [Finset.sum_ite_eq]
        simp [F.adj_comm]
      rw [t1, t2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases h : F.Adj a₀ b ∧ ψ b = u₀ <;> simp [h]
    rw [e1, e2] at this
    exact this
  refine ⟨fun a => φ (Sum.inl a), fun p => φ (Sum.inr p), fun a u hu => ?_, ?_⟩
  · have := hcol' a u
    rw [if_pos hu] at this
    exact robOdd_add_eq _ _ this
  · have h1 := hexp (robC ψ (Pi.single v₀ 1))
    rw [Fintype.sum_sum_type] at h1
    simp only [robC, Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero] at h1
    have h2 : ∑ a, (if ψ a = v₀ then φ (Sum.inl a) else 0) =
        ∑ a, (Pi.single v₀ 1 : V → ZMod 2) (ψ a) * φ (Sum.inl a) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases h : ψ a = v₀ <;> simp [h, Pi.single_apply]
    rw [h2, ← h1]
    rcases robOdd_01 (f (robC ψ (Pi.single v₀ 1))) with h | h
    · exact absurd h hf1
    · exact h

end LinAlg

end Trans

/-- (NURobersonOdd) for connected `G` with at least two vertices, there is no homomorphism over
`ψ` to `G_1` iff `ψ` is a weak oddomorphism. -/
theorem cntOver_eq_zero_iff {U V : Type} [Fintype U] [Fintype V] [Nontrivial V]
    {F : SimpleGraph U} {G : SimpleGraph V} (hG : G.Connected) (ψ : F →g G) (v₀ : V) :
    cntOver ψ (Pi.single v₀ 1) = 0 ↔ IsWeakOddomorphism ψ := by
  rw [robOdd_cnt_eq_zero_iff]
  constructor
  · intro hns
    obtain ⟨α, β, hα, h0⟩ := robOdd_data ψ v₀ hns
    refine robOdd_weak_of_data hG ψ v₀ (fun a b => F.Adj a b ∧ β (a, b) + β (b, a) = 1)
      (fun a b h => ⟨h.1.symm, by rw [add_comm]; exact h.2⟩) (fun a b h => h.1) α ?_ h0
    intro a u hu
    rw [hα a u hu]
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases robOdd_01 (β (a, b) + β (b, a)) with h | h <;> simp [h]
  · exact robOdd_zero_of_weak ψ v₀


end Lax461425Proofs.NU
