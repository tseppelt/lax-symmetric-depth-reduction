import Lax461425Proofs.Section6ABPToSkew

/-! Extending every ABP automorphism to the concrete skew circuit. -/

namespace Lax461425Proofs.Section6ABPToSkew

open Lax461425.Circuits Lax461425.SymmetricABPs Lax461425.MatrixSymmetry
open Lax461425.SymmetricFamilies
open scoped Classical

noncomputable section

variable {V : Type} {K : Type*} [Fintype V] [CommSemiring K]

theorem affine_constant (a : AffineForm V K) :
    MvPolynomial.constantCoeff a.polynomial = a.constant := by
  simp [AffineForm.polynomial]

theorem affine_coeff (a : AffineForm V K) (x : V) :
    MvPolynomial.coeff (Finsupp.single x 1) a.polynomial = a.coeff x := by
  classical
  simp [AffineForm.polynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_X,
    MvPolynomial.coeff_C, Finsupp.single_eq_single_iff, eq_comm]

/-- An edge permutation induced by a graph automorphism. -/
def edgeEquiv (G : ABP V K) (σ : G.Vertex ≃ G.Vertex)
    (he : ∀ u v, G.edge (σ u) (σ v) ↔ G.edge u v) : Edge G ≃ Edge G where
  toFun e := ⟨(σ e.1.1, σ e.1.2), (he _ _).2 e.2⟩
  invFun e := ⟨(σ.symm e.1.1, σ.symm e.1.2),
    (he _ _).1 (by simpa using e.2)⟩
  left_inv := by intro e; apply Subtype.ext; simp
  right_inv := by intro e; apply Subtype.ext; simp

theorem coefficient_equivariant (G : ABP V K) (σ : G.Vertex ≃ G.Vertex)
    (π : Equiv.Perm V) (hσ : G.Extends σ π) (e : Edge G) (x : Option V) :
    coefficient G (edgeEquiv G σ hσ.2.2.1 e) (Option.map π x) = coefficient G e x := by
  have heq := hσ.2.2.2 e.1.1 e.1.2 e.2
  cases x with
  | none =>
    have h := congrArg MvPolynomial.constantCoeff heq
    change (G.label (σ e.1.1) (σ e.1.2)).constant = (G.label e.1.1 e.1.2).constant
    simpa only [affine_constant, MvPolynomial.constantCoeff_rename] using h
  | some x =>
    have h := congrArg (MvPolynomial.coeff (Finsupp.single (π x) 1)) heq
    have hr := MvPolynomial.coeff_rename_mapDomain π π.injective
      (G.label e.1.1 e.1.2).polynomial (Finsupp.single x 1)
    rw [Finsupp.mapDomain_single] at hr
    change (G.label (σ e.1.1) (σ e.1.2)).coeff (π x) = (G.label e.1.1 e.1.2).coeff x
    exact (affine_coeff _ _).symm.trans (h.trans (hr.trans (affine_coeff _ _)))

/-- The permutation of the five gate kinds induced by an ABP extension. -/
def mapGate (G : ABP V K) (σ : G.Vertex ≃ G.Vertex) (ε : Edge G ≃ Edge G)
    (π : Equiv.Perm V) : Gate G → Gate G
  | .vertex v => .vertex (σ v)
  | .term e x => .term (ε e) (Option.map π x)
  | .coeff e x => .coeff (ε e) (Option.map π x)
  | .inputVar e x => .inputVar (ε e) (π x)
  | .sourceOne => .sourceOne

def lift (G : ABP V K) (σ : G.Vertex ≃ G.Vertex) (π : Equiv.Perm V)
    (hσ : G.Extends σ π) : Gate G ≃ Gate G where
  toFun := mapGate G σ (edgeEquiv G σ hσ.2.2.1) π
  invFun := mapGate G σ.symm (edgeEquiv G σ hσ.2.2.1).symm π.symm
  left_inv := by
    intro g; cases g <;> simp [mapGate, Option.map_map, Function.comp_def]
  right_inv := by
    intro g; cases g <;> simp [mapGate, Option.map_map, Function.comp_def]

theorem lift_label (G : ABP V K) (σ : G.Vertex ≃ G.Vertex) (π : Equiv.Perm V)
    (hσ : G.Extends σ π) (g : Gate G) :
    label G (lift G σ π hσ g) = (label G g).map π := by
  cases g with
  | vertex _ => rfl
  | term _ _ => rfl
  | coeff e x =>
    change GateLabel.const (coefficient G (edgeEquiv G σ hσ.2.2.1 e) (Option.map π x)) = _
    rw [coefficient_equivariant G σ π hσ]
    rfl
  | inputVar _ _ => rfl
  | sourceOne => rfl

theorem lift_wire (G : ABP V K) (σ : G.Vertex ≃ G.Vertex) (π : Equiv.Perm V)
    (hσ : G.Extends σ π) (g h : Gate G) :
    wire G (lift G σ π hσ g) (lift G σ π hσ h) = wire G g h := by
  have hs (v : G.Vertex) : σ v = G.source ↔ v = G.source := by
    calc
      σ v = G.source ↔ σ v = σ G.source := by rw [hσ.1]
      _ ↔ v = G.source := σ.injective.eq_iff
  cases g <;> cases h <;>
    simp [lift, mapGate, edgeEquiv, wire, hs, σ.injective.eq_iff, π.injective.eq_iff,
      Subtype.ext_iff, Prod.ext_iff]
  case term.coeff e x f y =>
    have hi : Option.map π x = Option.map π y ↔ x = y :=
      (Equiv.optionCongr π).injective.eq_iff
    simp only [hi]
  case term.inputVar e x f y =>
    cases x <;> simp [lift, mapGate, edgeEquiv, wire,
    σ.injective.eq_iff, π.injective.eq_iff, Subtype.ext_iff, Prod.ext_iff]

/-- The lifted gate permutation is an extending circuit automorphism. -/
theorem lift_extends (G : ABP V K) (σ : G.Vertex ≃ G.Vertex) (π : Equiv.Perm V)
    (hσ : G.Extends σ π) :
    Lax461425.MatrixSymmetry.Extends (circuit G) (lift G σ π hσ) π :=
  ⟨lift_label G σ π hσ, lift_wire G σ π hσ⟩

set_option maxHeartbeats 1000000 in
/-- The ABP-to-skew-circuit construction preserves matrix symmetry. -/
theorem circuit_isMatrixSymmetric {n : ℕ} (G : ABP (Fin n × Fin n) K)
    (hG : G.IsMatrixSymmetric) : IsMatrixSymmetric (circuit G) := by
  intro γ
  obtain ⟨σ, hσ⟩ := hG γ
  let π : Equiv.Perm (Fin n × Fin n) := Equiv.prodCongr γ.1 γ.2
  have hσ' : G.Extends σ π := hσ
  refine ⟨lift G σ π hσ', ?_⟩
  exact lift_extends G σ π hσ'

end
end Lax461425Proofs.Section6ABPToSkew
