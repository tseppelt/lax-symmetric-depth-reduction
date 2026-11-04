import Lax461425Proofs.SymmetricABPPaths
import Lax461425.SymmetricABPs

/-!
A two-vertex constant ABP, including the zero polynomial and zero-dimensional matrix
index. Both vertices are fixed by every extending automorphism.
-/

namespace Lax461425Proofs.Section6ConstantABP

open Lax461425.SymmetricABPs Lax461425.MatrixSymmetry

def Edge (u v : Bool) : Prop := u = false ∧ v = true

instance : DecidableRel Edge := fun u v =>
  inferInstanceAs (Decidable (u = false ∧ v = true))

theorem transGen_ends {u v : Bool} (h : Relation.TransGen Edge u v) :
    u = false ∧ v = true := by
  induction h with
  | single h => exact h
  | tail h h' ih => exact ⟨ih.1, h'.2⟩

abbrev constant (V : Type*) {K : Type*} [Zero K] (c : K) : ABP V K where
  Vertex := Bool
  edge := Edge
  decEdge := inferInstance
  label _ _ := ⟨c, fun _ => 0⟩
  source := false
  sink := true
  source_no_incoming _ h := Bool.false_ne_true h.2
  sink_no_outgoing _ h := Bool.false_ne_true h.1.symm
  acyclic v h := by
    have hh := transGen_ends h
    exact Bool.false_ne_true (hh.1.symm.trans hh.2)
  source_reaches v := by
    cases v
    · exact .refl
    · exact .single ⟨rfl, rfl⟩
  reaches_sink v := by
    cases v
    · exact .single ⟨rfl, rfl⟩
    · exact .refl

theorem computes {V K : Type*} [Fintype V] [CommSemiring K] (c : K) :
    (constant V c).Computes (MvPolynomial.C c) := by
  have hv : (constant V c).sink ≠ (constant V c).source :=
    fun h => Bool.false_ne_true h.symm
  change (constant V c).polynomialAt true = MvPolynomial.C c
  rw [SymmetricABPPaths.polynomialAt_eq_sum_predecessors (constant V c) hv]
  rw [Finset.sum_eq_single (⟨false, rfl, rfl⟩ : {u : Bool // (constant V c).edge u true})]
  · change (constant V c).polynomialAt (constant V c).source *
      (⟨c, fun _ : V => 0⟩ : AffineForm V K).polynomial = MvPolynomial.C c
    rw [SymmetricABPPaths.polynomialAt_source]
    simp [AffineForm.polynomial]
  · intro u hu hne
    exact False.elim (hne (Subtype.ext u.2.1))
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem identity_extends {V K : Type*} [Fintype V] [CommSemiring K] (c : K) (π : V → V) :
    (constant V c).Extends (Equiv.refl _) π := by
  refine ⟨rfl, rfl, fun _ _ => Iff.rfl, ?_⟩
  intro u v huv
  simp [constant, AffineForm.polynomial]

theorem isMatrixSymmetric {K : Type*} [CommSemiring K] (n : ℕ) (c : K) :
    (constant (Fin n × Fin n) c).IsMatrixSymmetric := fun γ =>
  ⟨Equiv.refl _, identity_extends c (actVar γ)⟩

theorem orbitSize_le {K : Type*} [CommSemiring K] (n : ℕ) (c : K) :
    (constant (Fin n × Fin n) c).orbitSize ≤ 1 := by
  classical
  apply Finset.sup_le
  intro v hv
  have hsub : (constant (Fin n × Fin n) c).orbit v ⊆ {v} := by
    rintro w ⟨γ, σ, hσ, rfl⟩
    cases v
    · exact hσ.1
    · exact hσ.2.1
  simpa using Set.ncard_le_ncard hsub

/-- At the zero-dimensional index there are no variables, so every polynomial has a
constant ABP with singleton vertex orbits. -/
theorem exists_zero_dimension {K : Type*} [CommSemiring K]
    (p : MvPolynomial (Fin 0 × Fin 0) K) :
    ∃ G : ABP (Fin 0 × Fin 0) K,
      G.Computes p ∧ G.IsMatrixSymmetric ∧ G.orbitSize ≤ 1 := by
  refine ⟨constant (Fin 0 × Fin 0) (p.coeff 0), ?_,
    isMatrixSymmetric 0 _, orbitSize_le 0 _⟩
  exact (computes (V := Fin 0 × Fin 0) (p.coeff 0)).trans p.eq_C_of_isEmpty.symm

end Lax461425Proofs.Section6ConstantABP
