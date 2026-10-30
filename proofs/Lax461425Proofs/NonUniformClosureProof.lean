import Lax461425Proofs.NUMinorLifting
import Lax461425Proofs.NUMinors
import Lax461425Proofs.NUEval
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
Final assembly, discharging the concept axiom
`Lax461425.NonUniformClosure.hom_not_mem_homSpan`.
-/

namespace Lax461425Proofs

open Lax461425.HomomorphismPolynomials Lax461425.NonUniformClosure Lax461425.Oddomorphisms
open Lax871432.GraphClasses Lax871432.ClosureProperties Lax68.GraphMinors
open Lax461425Proofs.NU

open scoped Classical

/-- Any graph on a subsingleton vertex type is a minor of `⊥ : SimpleGraph (Fin 1)`. -/
theorem final_isMinor_of_subsingleton {V : Type} [Subsingleton V] (G : SimpleGraph V) :
    IsMinor G (⊥ : SimpleGraph (Fin 1)) := by
  refine ⟨⟨fun _ => Set.univ, ?_, ?_, ?_⟩⟩
  · intro w
    refine ⟨fun a b => ?_⟩
    · have : a = b := Subsingleton.elim a b
      subst this
      exact SimpleGraph.Reachable.refl _
  · intro u v huv
    exact absurd (Subsingleton.elim u v) huv
  · intro u v h
    have : u = v := Subsingleton.elim u v
    subst this
    exact absurd h (G.irrefl)

theorem final_nontrivial {𝓕 : GraphClass} (hK₁ : 𝓕.Mem (⊥ : SimpleGraph (Fin 1)))
    (hminor : IsMinorClosed 𝓕) {V : Type} [Fintype V] {G : SimpleGraph V}
    (hGF : ¬ 𝓕.Mem G) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact hGF (hminor G (final_isMinor_of_subsingleton G) hK₁)

theorem final_exists_adj {V : Type} [Nontrivial V] {G : SimpleGraph V} (hG : G.Connected)
    (v : V) : ∃ u, G.Adj v u := by
  obtain ⟨w, hw⟩ := exists_ne v
  obtain ⟨p⟩ := hG.preconnected v w
  cases p with
  | nil => exact absurd rfl hw
  | cons h _ => exact ⟨_, h⟩

/-- Evaluation point for `W`. -/
theorem final_exists_eval {K : Type*} [Field K] {V : Type} [Fintype V] (G : SimpleGraph V)
    (W : V → ZMod 2) {N : ℕ} (hN : Nat.card (CfiV G W) ≤ N) :
    ∃ M : Fin N × Fin N → K, ∀ F' : Pattern,
      MvPolynomial.eval M (hom K F' N) =
        ((N ^ ((Nat.card F'.A - Nat.card F'.nz.A) + (Nat.card F'.B - Nat.card F'.nz.B)) *
          homBip F'.nz (BRel (cfiHat G W)) : ℕ) : K) := by
  have hemb : Nonempty (CfiV G W ↪ Fin N) := by
    let _ : Fintype (CfiV G W) := Fintype.ofFinite _
    have hle : Fintype.card (CfiV G W) ≤ Fintype.card (Fin N) := by
      rw [Fintype.card_fin, Fintype.card_eq_nat_card]; exact hN
    exact Function.Embedding.nonempty_of_card_le hle
  obtain ⟨e⟩ := hemb
  refine ⟨fun p => if (fun i j : Fin N => ∃ x y, e x = i ∧ e y = j ∧ BRel (cfiHat G W) x y)
    p.1 p.2 then 1 else 0, fun F' => ?_⟩
  refine (eval_hom (K := K) F' N (fun i j : Fin N =>
    ∃ x y, e x = i ∧ e y = j ∧ BRel (cfiHat G W) x y)).trans ?_
  rw [homBip_pad F' (BRel (cfiHat G W)) e e]

/--
---
conclusion: Lax461425.NonUniformClosure.hom_not_mem_homSpan
---
Non-uniform closure. Fix `v₀` and evaluate at the (padded) bi-adjacency matrices of the bipartite
double covers of the filled CFI graphs `Ĝ_0` and `Ĝ_{δ_{v₀}}`. Both evaluations agree on every
`hom_{F',N}` with `F' ∈ 𝓕` (`NU.minorLifting_eq`, using `NU.eval_hom`, `NU.homBip_pad`), hence on
`homSpan`, but differ on `hom_{F,N}` (`NU.minorLifting_lt`).
-/
theorem hom_not_mem_homSpan {K : Type*} [Field K] [CharZero K] (𝓕 : GraphClass)
    (hK₁ : 𝓕.Mem (⊥ : SimpleGraph (Fin 1))) (hminor : IsMinorClosed 𝓕)
    (hodd : IsWeakOddomorphismClosed 𝓕) {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) (hGF : ¬ 𝓕.Mem G) (F : Pattern) (hF : IsMinor G (underlying F))
    {N : ℕ} (hN : cfiSize G ≤ N) :
    hom K F N ∉ homSpan K 𝓕 N := by
  have : Nontrivial V := final_nontrivial hK₁ hminor hGF
  obtain ⟨v₀⟩ : Nonempty V := inferInstance
  have hadj := final_exists_adj hG
  have hN₀ : Nat.card (CfiV G 0) ≤ N := by rw [card_cfiV G 0 hadj]; exact hN
  have hN₁ : Nat.card (CfiV G (Pi.single v₀ 1)) ≤ N := by
    rw [card_cfiV G _ hadj]; exact hN
  obtain ⟨M₀, hM₀⟩ := final_exists_eval (K := K) G 0 hN₀
  obtain ⟨M₁, hM₁⟩ := final_exists_eval (K := K) G (Pi.single v₀ 1) hN₁
  intro hmem
  have key : ∀ p ∈ homSpan K 𝓕 N, MvPolynomial.eval M₀ p = MvPolynomial.eval M₁ p := by
    intro p hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro q ⟨F', hF', rfl⟩
      rw [hM₀, hM₁, minorLifting_eq 𝓕 hminor hodd hG hGF v₀ F'.nz
        (hminor _ (isMinor_nz F') hF')]
    · simp
    · intro x y _ _ hx hy
      simp [hx, hy]
    · intro a x _ hx
      simp [MvPolynomial.smul_eval, hx]
  have h := key _ hmem
  rw [hM₀, hM₁] at h
  have h' := Nat.cast_injective h
  have hlt := minorLifting_lt hG v₀ F.nz (isMinor_nz_of_isMinor hG F hF)
  have hNpos : 0 < N := by
    refine lt_of_lt_of_le ?_ hN
    unfold cfiSize
    exact Finset.sum_pos (fun _ _ => pow_pos (by norm_num) _) ⟨v₀, Finset.mem_univ _⟩
  have := Nat.eq_of_mul_eq_mul_left (pow_pos hNpos _) h'
  omega

end Lax461425Proofs
