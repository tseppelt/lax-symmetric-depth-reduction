import Lax461425Proofs.Section6ABPToSkewRecovery

/-! Recovering affine labels, not just edges, from every extending circuit automorphism. -/

namespace Lax461425Proofs.Section6ABPToSkew

open Lax461425.Circuits Lax461425.SymmetricABPs Lax461425.MatrixSymmetry
open scoped Classical

noncomputable section

variable {V : Type} {K : Type*} [Fintype V] [CommSemiring K]
variable (G : ABP V K) (τ : Gate G ≃ Gate G) (π : Equiv.Perm V)
variable (hτ : Extends (circuit G) τ π)

omit hτ in
theorem term_fanin (e : Edge G) (x : Option V) :
    (∑ h, wire G (.term e x) h) = 2 + (if x.isSome then 1 else 0) := by
  rw [sum_gates]
  cases x <;> simp [wire, ite_and, eq_comm]

include hτ

theorem fanin_preserved (g : Gate G) :
    (∑ h, wire G (τ g) h) = ∑ h, wire G g h := by
  rw [← τ.sum_comp (fun h => wire G (τ g) h)]
  exact Finset.sum_congr rfl (fun h _ => hτ.2 g h)

theorem inputVar_image_exists (e : Edge G) (x : V) :
    ∃ f, τ (.inputVar e x) = .inputVar f (π x) := by
  have hl : label G (τ (.inputVar e x)) = .var (π x) := hτ.1 (.inputVar e x)
  cases he : τ (.inputVar e x) with
  | vertex _ => simp [he, label] at hl
  | term _ _ => simp [he, label] at hl
  | coeff _ _ => simp [he, label] at hl
  | sourceOne => simp [he, label] at hl
  | inputVar f y =>
    have hy : y = π x := by simpa [he, label] using hl
    exact ⟨f, by rw [hy]⟩

theorem term_slot_image {e f : Edge G} {x y : Option V}
    (he : τ (.term e x) = .term f y) : y = Option.map π x := by
  have hdeg := fanin_preserved G τ π hτ (.term e x)
  rw [he, term_fanin, term_fanin] at hdeg
  cases x with
  | none => cases y <;> simp_all
  | some x =>
    obtain ⟨f', hf'⟩ := inputVar_image_exists G τ π hτ e x
    have hw := preserves_wire G τ π hτ (.term e (some x)) (.inputVar e x)
    rw [he, hf'] at hw
    cases y with
    | none => simp [wire] at hw
    | some y =>
      have hy : y = π x := by by_contra hn; simp [wire, hn] at hw
      simp [hy]

theorem coeff_image {e f : Edge G} {x y : Option V}
    (he : τ (.term e x) = .term f y) :
    τ (.coeff e x) = .coeff f y ∧ coefficient G f y = coefficient G e x := by
  have hl : label G (τ (.coeff e x)) = .const (coefficient G e x) := hτ.1 (.coeff e x)
  have hw := preserves_wire G τ π hτ (.term e x) (.coeff e x)
  rw [he] at hw
  cases hc : τ (.coeff e x) with
  | vertex _ => simp [hc, label] at hl
  | term _ _ => simp [hc, label] at hl
  | inputVar _ _ => simp [hc, label] at hl
  | sourceOne => simp [hc, wire] at hw
  | coeff f' y' =>
    have hidx : f = f' ∧ y = y' := by
      by_contra hn
      simp [hc, wire, hn] at hw
    rcases hidx with ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    simpa [hc, label] using hl

/-- The recovered edge permutation is determined by its two endpoints. -/
def recoveredEdges : Edge G ≃ Edge G :=
  edgeEquiv G (recoverVertices G τ π hτ) (recover_edges G τ π hτ)

theorem term_image (e : Edge G) (x : Option V) :
    τ (.term e x) = .term (recoveredEdges G τ π hτ e) (Option.map π x) := by
  obtain ⟨f, y, he, hu, hv⟩ := term_image_exists G τ π hτ e x
  have hf : f = recoveredEdges G τ π hτ e := by
    apply Subtype.ext
    exact Prod.ext hu hv
  rw [he, hf, term_slot_image G τ π hτ he]

theorem recovered_coefficient (e : Edge G) (x : Option V) :
    coefficient G (recoveredEdges G τ π hτ e) (Option.map π x) = coefficient G e x :=
  (coeff_image G τ π hτ (term_image G τ π hτ e x)).2

/-- Every extending circuit automorphism induces an extending ABP automorphism. -/
theorem recover_extends : G.Extends (recoverVertices G τ π hτ) π := by
  refine ⟨recover_source G τ π hτ, ?_, recover_edges G τ π hτ, ?_⟩
  · have hh := PatternsSupportBasic.extends_fixes_out hτ
    change τ (.vertex G.sink) = .vertex G.sink at hh
    rw [recoverVertex_spec G τ π hτ] at hh
    exact Gate.vertex.inj hh
  · intro u v huv
    let e : Edge G := ⟨(u, v), huv⟩
    have hc := recovered_coefficient G τ π hτ e none
    have hx := fun x : V => recovered_coefficient G τ π hτ e (some x)
    change (G.label ((recoverVertices G τ π hτ) u) ((recoverVertices G τ π hτ) v)).constant =
      (G.label u v).constant at hc
    have hx' (x : V) :
        (G.label ((recoverVertices G τ π hτ) u) ((recoverVertices G τ π hτ) v)).coeff (π x) =
          (G.label u v).coeff x := hx x
    simp only [AffineForm.polynomial, map_add, map_sum, map_mul,
      MvPolynomial.rename_C, MvPolynomial.rename_X, hc]
    congr 1
    exact (Fintype.sum_equiv π _ _ (fun x => by rw [hx'])).symm

end
end Lax461425Proofs.Section6ABPToSkew
