import Lax461425Proofs.Section6ABPToSkew
import Lax461425Proofs.SymmetricABPPaths
import Lax461425Proofs.CircuitFacts

/-! Correctness of the concrete ABP-to-skew-circuit translation. -/

namespace Lax461425Proofs.Section6ABPToSkew

open Lax461425.Circuits Lax461425.SymmetricABPs
open scoped Classical

noncomputable section

variable {V : Type} {K : Type*} [Fintype V] [CommSemiring K]

/-- Values of all gates, expressed in terms of literal ABP prefix-path sums. -/
def value (G : ABP V K) : Gate G → MvPolynomial V K
  | .vertex v => G.polynomialAt v
  | .term e none => G.polynomialAt e.1.1 * MvPolynomial.C (coefficient G e none)
  | .term e (some x) =>
      G.polynomialAt e.1.1 * MvPolynomial.C (coefficient G e (some x)) * MvPolynomial.X x
  | .coeff e x => MvPolynomial.C (coefficient G e x)
  | .inputVar _ x => MvPolynomial.X x
  | .sourceOne => 1

/-- Sums may be split into the five disjoint gate kinds. -/
theorem sum_gates {R : Type*} [AddCommMonoid R] (G : ABP V K) (f : Gate G → R) :
    (∑ g, f g) = (∑ v, f (.vertex v)) + ((∑ e, ∑ x, f (.term e x)) +
      ((∑ e, ∑ x, f (.coeff e x)) + ((∑ e, ∑ x, f (.inputVar e x)) + f .sourceOne))) := by
  rw [← (gateEquiv G).symm.sum_comp f]
  simp [gateEquiv, Fintype.sum_sum_type, Fintype.sum_prod_type]

/-- Products may be split into the five disjoint gate kinds. -/
theorem prod_gates {R : Type*} [CommMonoid R] (G : ABP V K) (f : Gate G → R) :
    (∏ g, f g) = (∏ v, f (.vertex v)) * ((∏ e, ∏ x, f (.term e x)) *
      ((∏ e, ∏ x, f (.coeff e x)) * ((∏ e, ∏ x, f (.inputVar e x)) * f .sourceOne))) := by
  rw [← (gateEquiv G).symm.prod_comp f]
  simp [gateEquiv, Fintype.prod_sum_type, Fintype.prod_prod_type]

theorem term_local (G : ABP V K) (e : Edge G) (x : Option V) :
    value G (.term e x) = ∏ h, value G h ^ wire G (.term e x) h := by
  rw [prod_gates]
  cases x <;> simp [value, wire, Fintype.prod_option, eq_comm, ite_and, mul_assoc]

/-- Grouping all product gates belonging to an edge recovers its affine label. -/
theorem sum_edge_terms (G : ABP V K) (e : Edge G) :
    (∑ x, value G (.term e x)) =
      G.polynomialAt e.1.1 * (G.label e.1.1 e.1.2).polynomial := by
  rw [Fintype.sum_option]
  simp only [value, coefficient, AffineForm.polynomial, mul_add, Finset.mul_sum, mul_assoc]

theorem vertex_source_local (G : ABP V K) :
    value G (.vertex G.source) = ∑ h, wire G (.vertex G.source) h • value G h := by
  rw [sum_gates]
  have hedge : ∀ e : Edge G, e.1.2 ≠ G.source := by
    intro e he
    exact G.source_no_incoming e.1.1 (he ▸ e.2)
  simp [value, wire, hedge, SymmetricABPPaths.polynomialAt_source]

/-- Incoming edges identified by their first endpoint. -/
def incomingEdgeEquiv (G : ABP V K) (v : G.Vertex) :
    {e : Edge G // e.1.2 = v} ≃ {u : G.Vertex // G.edge u v} where
  toFun e := ⟨e.1.1.1, by simpa [e.2] using e.1.2⟩
  invFun u := ⟨⟨(u.1, v), u.2⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨⟨u, w⟩, huw⟩, hw⟩
    cases hw
    rfl
  right_inv := by intro u; rfl

theorem vertex_local (G : ABP V K) (v : G.Vertex) :
    value G (.vertex v) = ∑ h, wire G (.vertex v) h • value G h := by
  by_cases hv : v = G.source
  · subst v; exact vertex_source_local G
  rw [sum_gates]
  simp only [wire, zero_nsmul, Finset.sum_const_zero, zero_add, add_zero, hv,
    ↓reduceIte, one_nsmul]
  change G.polynomialAt v = ∑ e : Edge G, ∑ x : Option V,
    (if e.1.2 = v then 1 else 0) • value G (.term e x)
  rw [SymmetricABPPaths.polynomialAt_eq_sum_predecessors G hv]
  have hsum : (∑ e : Edge G, ∑ x : Option V,
      (if e.1.2 = v then 1 else 0) • value G (.term e x)) =
      ∑ e : {e : Edge G // e.1.2 = v},
        G.polynomialAt e.1.1.1 * (G.label e.1.1.1 v).polynomial := by
    calc
      _ = ∑ e : Edge G, if e.1.2 = v then ∑ x : Option V, value G (.term e x) else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        split_ifs <;> simp
      _ = ∑ e : {e : Edge G // e.1.2 = v}, ∑ x : Option V, value G (.term e.1 x) := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype _ (by simp) _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e _
        rw [sum_edge_terms]
        simp only [e.2]
  rw [hsum]
  exact ((incomingEdgeEquiv G v).sum_comp
    (fun u => G.polynomialAt u.1 * (G.label u.1 v).polynomial)).symm

/-- Every gate computes its prescribed path-sum value. -/
theorem computesAt_value (G : ABP V K) (g : Gate G) :
    (circuit G).ComputesAt g (value G g) := by
  apply CircuitFacts.computesAt_of_local_values (circuit G) (value G)
  · intro g x hg
    cases g <;> simp_all [circuit, label, value]
  · intro g c hg
    cases g <;> simp_all [circuit, label, value, MvPolynomial.C_1]
    simpa only [map_one] using congrArg (MvPolynomial.C : K → MvPolynomial V K) hg
  · intro g hg
    cases g <;> simp only [circuit, label] at hg
    all_goals try contradiction
    exact vertex_local G _
  · intro g hg
    cases g <;> simp only [circuit, label] at hg
    all_goals try contradiction
    exact term_local G _ _

/-- The output computes exactly the sum over all source-to-sink ABP paths. -/
theorem circuit_computes (G : ABP V K) : (circuit G).Computes G.polynomial :=
  computesAt_value G (.vertex G.sink)

end
end Lax461425Proofs.Section6ABPToSkew
