import Lax461425.CircuitProperties
import Lax461425.SymmetricFamilies
import Lax461425.SymmetricClasses
import Lax461425.SymmetricVNP
import Lax461425Proofs.CircuitFacts

open Lax461425.CircuitProperties

/-! Cardinality bounds and constant witnesses for the new polynomial-family interfaces. -/

namespace Lax461425Proofs.CircuitFamilyFacts

open Lax461425.Circuits Lax461425Proofs.CircuitConstants Lax461425.SymmetricFamilies
open Lax461425.SymmetricVNP
open Lax461425.SymmetricClasses

variable {G V K : Type*} [Group G]

/-- Every orbit is a subset of the finite gate set, for all extending automorphisms. -/
theorem orbitSize_le_card (ρ : G →* Equiv.Perm V) (C : Circuit V K) :
    orbitSize ρ C ≤ Fintype.card C.Gate := by
  apply Finset.sup_le
  intro g _
  simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card (orbit ρ C g)

/-- Constants are symmetric under every action on the variable type. -/
theorem constant_symmetric (ρ : G →* Equiv.Perm V) (c : K) :
    Symmetric ρ (constant V c) := fun γ => ⟨Equiv.refl _, CircuitFacts.constant_extends c _⟩

/-- The constant-circuit gate orbit has size at most one. -/
theorem constant_orbitSize_le_one (ρ : G →* Equiv.Perm V) (c : K) :
    orbitSize ρ (constant V c) ≤ 1 := by
  have hc : Fintype.card (constant V c).Gate ≤ 1 := by
    change Fintype.card Unit ≤ 1
    decide
  exact (orbitSize_le_card ρ (constant V c)).trans hc

/-- The one-gate constant circuit is a formula, including its wire multiplicities. -/
theorem constant_isFormula (c : K) : (IsFormula (constant V c)) := by
  constructor
  · intro g h; exact Nat.zero_le 1
  · intro g hg; exact (hg trivial).elim

end Lax461425Proofs.CircuitFamilyFacts
