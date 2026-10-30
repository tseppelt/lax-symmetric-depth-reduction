import Lax461425Proofs.NURobersonAlg
import Lax461425Proofs.NURobersonOdd
import Mathlib

/-!
The filled CFI graphs: `hom(F, Ĝ_W) = ∑_ψ cntOver (F_ψ → G) W`, and the consequences
`filled_le` and `filled_lt_iff`.
-/

namespace Lax461425Proofs.NU

open Lax461425.HomomorphismPolynomials Lax461425.NonUniformClosure Lax461425.Oddomorphisms
open Lax871432.GraphClasses

open scoped Classical

/-- The vertex maps `ψ : U → V` that are homomorphisms `F → K_V`. -/
abbrev filled_S {U V : Type} (F : SimpleGraph U) (_G : SimpleGraph V) :=
  {ψ : U → V // ∀ a b, F.Adj a b → ψ a ≠ ψ b}

theorem filled_finite {V : Type} [Fintype V] (G : SimpleGraph V) (W : V → ZMod 2) :
    Finite (CfiV G W) := by
  have hinj : Function.Injective
      (fun p : CfiV G W => (⟨p.vertex, p.label⟩ : Σ v : V, G.neighborSet v → ZMod 2)) := by
    intro p q h
    obtain ⟨p1, p2, p3⟩ := p
    obtain ⟨q1, q2, q3⟩ := q
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    have := eq_of_heq h2
    subst this
    rfl
  exact Finite.of_injective _ hinj

theorem filled_vertex_ne {U V : Type} [Fintype V] {F : SimpleGraph U} {G : SimpleGraph V}
    {W : V → ZMod 2} (f : F →g cfiHat G W) :
    ∀ a b, F.Adj a b → (f a).vertex ≠ (f b).vertex := by
  intro a b hab
  rcases f.map_rel hab with ⟨h, _⟩ | ⟨h, _⟩
  · exact G.ne_of_adj h
  · exact h

/-- Forward direction of the fibre equivalence. -/
def filled_fwd {U V : Type} [Fintype V] {F : SimpleGraph U} {G : SimpleGraph V}
    {W : V → ZMod 2} (ψ : filled_S F G) (f : F →g cfiHat G W)
    (hf : ∀ x, (f x).vertex = ψ.1 x) : Fpsi F G ψ.1 →g cfi G W where
  toFun := f
  map_rel' := by
    intro x y hxy
    have hxy' : F.Adj x y ∧ G.Adj (ψ.1 x) (ψ.1 y) := hxy
    rcases f.map_rel hxy'.1 with h | ⟨_, h⟩
    · exact h
    · exact absurd (by rw [hf, hf]; exact hxy'.2) h

/-- Backward direction of the fibre equivalence. -/
def filled_bwd {U V : Type} [Fintype V] {F : SimpleGraph U} {G : SimpleGraph V}
    {W : V → ZMod 2} (ψ : filled_S F G) (h : Fpsi F G ψ.1 →g cfi G W)
    (hh : ∀ x, (h x).vertex = ψ.1 x) : F →g cfiHat G W where
  toFun := h
  map_rel' := by
    intro a b hab
    by_cases hψ : G.Adj (ψ.1 a) (ψ.1 b)
    · exact Or.inl (h.map_rel (show (Fpsi F G ψ.1).Adj a b from ⟨hab, hψ⟩))
    · refine Or.inr ⟨?_, ?_⟩
      · rw [hh, hh]; exact ψ.2 a b hab
      · rw [hh, hh]; exact hψ

/-- The fibre of `f ↦ vertex ∘ f` over `ψ` is the set of homomorphisms counted by `cntOver`. -/
def filled_fiberEquiv {U V : Type} [Fintype V] (F : SimpleGraph U) (G : SimpleGraph V)
    (W : V → ZMod 2) (ψ : filled_S F G) :
    {f : F →g cfiHat G W //
        (⟨fun x => (f x).vertex, filled_vertex_ne f⟩ : filled_S F G) = ψ} ≃
      {h : Fpsi F G ψ.1 →g cfi G W // ∀ x, (h x).vertex = ψ.1 x} where
  toFun f :=
    ⟨filled_fwd ψ f.1 (fun x => congrFun (congrArg Subtype.val f.2) x), fun x =>
      congrFun (congrArg Subtype.val f.2) x⟩
  invFun h :=
    ⟨filled_bwd ψ h.1 h.2, Subtype.ext (funext fun x => h.2 x)⟩
  left_inv f := by
    apply Subtype.ext
    ext x
    rfl
  right_inv h := by
    apply Subtype.ext
    ext x
    rfl

theorem filled_homCount_eq {U V : Type} [Fintype U] [Fintype V] (F : SimpleGraph U)
    (G : SimpleGraph V) (W : V → ZMod 2) :
    homCount F (cfiHat G W) =
      ∑ ψ : filled_S F G, cntOver (psiHom F G ψ.1) W := by
  have : Finite (CfiV G W) := filled_finite G W
  have : Finite (F →g cfiHat G W) := by
    refine Finite.of_injective (fun f : F →g cfiHat G W => (f : U → CfiV G W)) ?_
    intro f g h
    exact RelHom.ext (congrFun h)
  let p : (F →g cfiHat G W) → filled_S F G := fun f => ⟨fun x => (f x).vertex, filled_vertex_ne f⟩
  unfold homCount
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv p), Nat.card_sigma]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  exact Nat.card_congr (filled_fiberEquiv F G W ψ)

theorem filled_term_le {U V : Type} [Fintype U] [Fintype V] (F : SimpleGraph U)
    {G : SimpleGraph V} (v₀ : V) (ψ : filled_S F G) :
    cntOver (psiHom F G ψ.1) (Pi.single v₀ 1) ≤ cntOver (psiHom F G ψ.1) 0 := by
  rcases cntOver_dichotomy (psiHom F G ψ.1) v₀ with ⟨h0, h | h⟩
  · omega
  · omega

theorem filled_term_lt {U V : Type} [Fintype U] [Fintype V] [Nontrivial V] (F : SimpleGraph U)
    {G : SimpleGraph V} (hG : G.Connected) (v₀ : V) (ψ : filled_S F G) :
    cntOver (psiHom F G ψ.1) (Pi.single v₀ 1) < cntOver (psiHom F G ψ.1) 0 ↔
      IsWeakOddomorphism (psiHom F G ψ.1) := by
  rw [← cntOver_eq_zero_iff hG (psiHom F G ψ.1) v₀]
  rcases cntOver_dichotomy (psiHom F G ψ.1) v₀ with ⟨h0, h | h⟩
  · omega
  · omega

theorem filled_le {U V : Type} [Fintype U] [Fintype V] [Nontrivial V] (F : SimpleGraph U)
    {G : SimpleGraph V} (hG : G.Connected) (v₀ : V) :
    homCount F (cfiHat G (Pi.single v₀ 1)) ≤ homCount F (cfiHat G 0) := by
  rw [filled_homCount_eq, filled_homCount_eq]
  exact Finset.sum_le_sum fun ψ _ => filled_term_le F v₀ ψ

theorem filled_lt_iff {U V : Type} [Fintype U] [Fintype V] [Nontrivial V] (F : SimpleGraph U)
    {G : SimpleGraph V} (hG : G.Connected) (v₀ : V) :
    homCount F (cfiHat G (Pi.single v₀ 1)) < homCount F (cfiHat G 0) ↔
      ∃ ψ : U → V, (∀ a b, F.Adj a b → ψ a ≠ ψ b) ∧ IsWeakOddomorphism (psiHom F G ψ) := by
  rw [filled_homCount_eq, filled_homCount_eq]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    refine absurd h (not_lt.2 (Finset.sum_le_sum fun ψ _ => ?_))
    by_contra hlt
    exact hne ψ.1 ψ.2 ((filled_term_lt F hG v₀ ψ).1 (not_le.1 hlt))
  · rintro ⟨ψ, hψ, hw⟩
    exact Finset.sum_lt_sum (fun ψ _ => filled_term_le F v₀ ψ)
      ⟨⟨ψ, hψ⟩, Finset.mem_univ _, (filled_term_lt F hG v₀ ⟨ψ, hψ⟩).2 hw⟩

end Lax461425Proofs.NU
