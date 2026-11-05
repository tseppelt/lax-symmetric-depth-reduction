import Lax461425Proofs.Section6ABPSum

/-! Path-sum correctness of the finite linear-combination ABP. -/

namespace Lax461425Proofs.Section6ABPSum

open Lax461425.SymmetricABPs
open scoped Classical BigOperators

noncomputable section

variable {I V : Type} {K : Type*} [Fintype I] [Nonempty I] [Fintype V] [Field K]
variable (G : I → ABP V K) (c : I → K)

lemma constForm_polynomial (a : K) : (constForm a : AffineForm V K).polynomial =
    MvPolynomial.C a := by simp [constForm, AffineForm.polynomial]

def value : Vertex G → MvPolynomial V K
  | .source => 1
  | .entry i => MvPolynomial.C (c i)
  | .branch i v => MvPolynomial.C (c i * tag i) * (G i).polynomialAt v
  | .exit i => MvPolynomial.C (c i * tag i) * (G i).polynomial
  | .sink => ∑ i, MvPolynomial.C (c i) * (G i).polynomial

lemma sum_single_predecessor {S : Type*} [AddCommMonoid S]
    (v w : Vertex G) (hw : edge G w v)
    (hunique : ∀ u, edge G u v → u = w)
    (f : {u : Vertex G // edge G u v} → S) :
    (∑ u, f u) = f ⟨w, hw⟩ := by
  refine Finset.sum_eq_single (s := Finset.univ) (f := f) ⟨w, hw⟩ ?_ ?_
  · intro u _ hne
    exact False.elim (hne (Subtype.ext (hunique u.val u.property)))
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

lemma predecessor_entry (i : I) (u : Vertex G) (hu : edge G u (.entry i)) :
    u = .source := by cases u <;> simp_all [edge]

lemma predecessor_exit (i : I) (u : Vertex G) (hu : edge G u (.exit i)) :
    u = .branch i (G i).sink := by
  cases u <;> simp only [edge] at hu
  all_goals try contradiction
  rcases hu with ⟨rfl, rfl⟩
  rfl

lemma predecessor_branch_source (i : I) (u : Vertex G)
    (hu : edge G u (.branch i (G i).source)) : u = .entry i := by
  cases u <;> simp only [edge] at hu
  all_goals try contradiction
  · rcases hu with ⟨rfl, _⟩; rfl
  · rcases hu with ⟨rfl, hu⟩
    exact ((G _).source_no_incoming _ hu).elim

def incomingBranchEquiv (i : I) (v : (G i).Vertex) (hv : v ≠ (G i).source) :
    {u : Vertex G // edge G u (.branch i v)} ≃
      {u : (G i).Vertex // (G i).edge u v} where
  toFun u := by
    rcases u with ⟨u, hu⟩
    cases u <;> simp only [edge] at hu
    all_goals try contradiction
    · have hij := Classical.choose hu
      have hs := Classical.choose_spec hu
      cases hij
      exact (hv hs).elim
    · have hij := Classical.choose hu
      have he := Classical.choose_spec hu
      cases hij
      exact ⟨_, he⟩
  invFun u := ⟨.branch i u.val, ⟨rfl, u.property⟩⟩
  left_inv u := by
    rcases u with ⟨u, hu⟩
    cases u <;> simp only [edge] at hu
    all_goals try contradiction
    · rcases hu with ⟨rfl, hu⟩
      exact (hv hu).elim
    · rcases hu with ⟨rfl, hu⟩
      rfl
  right_inv u := by rfl

def incomingSinkEquiv : I ≃ {u : Vertex G // edge G u .sink} where
  toFun i := ⟨.exit i, trivial⟩
  invFun u := by
    rcases u with ⟨u, hu⟩
    cases u <;> simp only [edge] at hu
    all_goals try contradiction
    rename_i i
    exact i
  left_inv i := rfl
  right_inv u := by
    rcases u with ⟨u, hu⟩
    cases u <;> simp only [edge] at hu
    all_goals try contradiction
    rfl

lemma local_entry (i : I) :
    value G c (.entry i) = ∑ u : {u : Vertex G // edge G u (.entry i)},
      value G c u.val * (label G c u.val (.entry i)).polynomial := by
  rw [sum_single_predecessor G (.entry i) .source trivial (predecessor_entry G i)]
  simp [value, label, constForm, AffineForm.polynomial]

lemma local_branch_source (i : I) :
    value G c (.branch i (G i).source) =
      ∑ u : {u : Vertex G // edge G u (.branch i (G i).source)},
        value G c u.val * (label G c u.val (.branch i (G i).source)).polynomial := by
  rw [sum_single_predecessor G (.branch i (G i).source) (.entry i) ⟨rfl, rfl⟩
    (predecessor_branch_source G i)]
  simp [value, label, constForm, AffineForm.polynomial,
    SymmetricABPPaths.polynomialAt_source]

lemma local_branch (i : I) (v : (G i).Vertex) (hv : v ≠ (G i).source) :
    value G c (.branch i v) =
      ∑ u : {u : Vertex G // edge G u (.branch i v)},
        value G c u.val * (label G c u.val (.branch i v)).polynomial := by
  rw [← (incomingBranchEquiv G i v hv).symm.sum_comp
    (fun u => value G c u.val * (label G c u.val (.branch i v)).polynomial)]
  change MvPolynomial.C (c i * tag i) * (G i).polynomialAt v =
    ∑ u : {u : (G i).Vertex // (G i).edge u v},
      (MvPolynomial.C (c i * tag i) * (G i).polynomialAt u.val) *
        (label G c (.branch i u.val) (.branch i v)).polynomial
  simp only [label, ↓reduceDIte]
  rw [SymmetricABPPaths.polynomialAt_eq_sum_predecessors (G i) hv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  exact (mul_assoc _ _ _).symm

lemma local_exit (i : I) :
    value G c (.exit i) = ∑ u : {u : Vertex G // edge G u (.exit i)},
      value G c u.val * (label G c u.val (.exit i)).polynomial := by
  rw [sum_single_predecessor G (.exit i) (.branch i (G i).sink) ⟨rfl, rfl⟩
    (predecessor_exit G i)]
  simp [value, label, constForm, AffineForm.polynomial, ABP.polynomial]

variable [CharZero K]

lemma local_sink :
    value G c .sink = ∑ u : {u : Vertex G // edge G u .sink},
      value G c u.val * (label G c u.val .sink).polynomial := by
  rw [← (incomingSinkEquiv G).sum_comp
    (fun u => value G c u.val * (label G c u.val .sink).polynomial)]
  change (∑ i, MvPolynomial.C (c i) * (G i).polynomial) =
    ∑ i, value G c (.exit i) * (label G c (.exit i) .sink).polynomial
  apply Finset.sum_congr rfl
  intro i _
  have ht : (tag i : K) ≠ 0 := Nat.cast_add_one_ne_zero _
  simp only [value, label, constForm_polynomial]
  rw [mul_right_comm, ← MvPolynomial.C_mul, mul_assoc, mul_inv_cancel₀ ht, mul_one]

/-- The path sum is the prescribed linear combination, including zero coefficients. -/
theorem computes :
    (abp G c).Computes (∑ i, MvPolynomial.C (c i) * (G i).polynomial) := by
  have h := SymmetricABPPaths.polynomialAt_eq_of_local (abp G c) (value G c)
    rfl (by
      intro v hv
      cases v with
      | source => exact (hv rfl).elim
      | entry i => exact local_entry G c i
      | branch i v =>
        by_cases he : v = (G i).source
        · subst v; exact local_branch_source G c i
        · exact local_branch G c i v he
      | exit i => exact local_exit G c i
      | sink => exact local_sink G c) .sink
  exact h.symm

end
end Lax461425Proofs.Section6ABPSum
