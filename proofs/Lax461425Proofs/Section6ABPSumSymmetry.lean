import Lax461425Proofs.Section6ABPSum

/-! Extending branch automorphisms to the finite-sum ABP. -/

namespace Lax461425Proofs.Section6ABPSum

open Lax461425.SymmetricABPs Lax461425.MatrixSymmetry
open scoped Classical

noncomputable section

variable {I V : Type} {K : Type*} [Fintype I] [Nonempty I] [Fintype V] [Field K]
variable (G : I → ABP V K) (c : I → K)

/-- Apply an automorphism inside each branch while fixing its two endpoints. -/
def lift (σ : ∀ i, (G i).Vertex ≃ (G i).Vertex) : Vertex G ≃ Vertex G where
  toFun
    | .source => .source
    | .entry i => .entry i
    | .branch i v => .branch i (σ i v)
    | .exit i => .exit i
    | .sink => .sink
  invFun
    | .source => .source
    | .entry i => .entry i
    | .branch i v => .branch i ((σ i).symm v)
    | .exit i => .exit i
    | .sink => .sink
  left_inv v := by cases v <;> simp
  right_inv v := by cases v <;> simp

theorem lift_edge (π : V → V) (σ : ∀ i, (G i).Vertex ≃ (G i).Vertex)
    (hσ : ∀ i, (G i).Extends (σ i) π) (u v : Vertex G) :
    edge G (lift G σ u) (lift G σ v) ↔ edge G u v := by
  cases u <;> cases v <;> simp only [lift, Equiv.coe_fn_mk, edge]
  all_goals try rfl
  · rename_i i j v
    by_cases hij : i = j
    · subst j
      simp only [exists_const]
      simpa only [(hσ i).1] using
        ((σ i).injective.eq_iff : σ i v = σ i (G i).source ↔ v = (G i).source)
    · simp [hij]
  · rename_i i u j v
    by_cases hij : i = j
    · subst j
      simpa using (hσ i).2.2.1 u v
    · simp [hij]
  · rename_i i u j
    by_cases hij : i = j
    · subst j
      simp only [true_and]
      simpa only [(hσ i).2.1] using
        ((σ i).injective.eq_iff : σ i u = σ i (G i).sink ↔ u = (G i).sink)
    · simp [hij]

theorem lift_extends (π : V → V) (σ : ∀ i, (G i).Vertex ≃ (G i).Vertex)
    (hσ : ∀ i, (G i).Extends (σ i) π) :
    (abp G c).Extends (lift G σ) π := by
  refine ⟨rfl, rfl, lift_edge G π σ hσ, ?_⟩
  intro u v huv
  cases u <;> cases v <;> simp only [abp, edge] at huv
  all_goals try contradiction
  · simp [abp, label, lift, constForm, AffineForm.polynomial]
  · rcases huv with ⟨rfl, _⟩
    simp [abp, label, lift, constForm, AffineForm.polynomial]
  · rcases huv with ⟨rfl, huv⟩
    simpa [abp, label, lift] using (hσ _).2.2.2 _ _ huv
  · rcases huv with ⟨rfl, _⟩
    simp [abp, label, lift, constForm, AffineForm.polynomial]
  · simp [abp, label, lift, constForm, AffineForm.polynomial]

/-- Every variable permutation extends to the finite sum whenever it extends to each
summand ABP. Coefficients may be zero. -/
theorem isMatrixSymmetric {n : ℕ} (G : I → ABP (Fin n × Fin n) K) (c : I → K)
    (hG : ∀ i, (G i).IsMatrixSymmetric) : (abp G c).IsMatrixSymmetric := by
  intro γ
  choose σ hσ using fun i => hG i γ
  exact ⟨lift G σ, lift_extends G c (actVar γ) σ hσ⟩

end
end Lax461425Proofs.Section6ABPSum
