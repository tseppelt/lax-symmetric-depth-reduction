import Lax461425.SupportTheorem
import Lax461425Proofs.ReducedRigid
import Lax461425Proofs.STMinimal
import Lax461425Proofs.STSupports

/-!
Discharging the concept axiom `Lax461425.SupportTheorem.supportSize_le`.
-/

namespace Lax461425Proofs.SupportTheorem

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportBasic

/--
---
conclusion: Lax461425.SupportTheorem.supportSize_le
---
Rigidity (reducedness and matrix-symmetry) makes `Γₙ` act on the gates. The index of a gate
stabiliser is at most the orbit size, so by Dixon and Mortimer the stabiliser of every internal
gate contains the alternating group fixing fewer than `κ` points on each side; reducedness
upgrades it to the symmetric group, giving supports with sides of size `≤ κ - 1` by induction.
The `⊆`-least such support of a gate is mapped equivariantly by `Γₙ`, so its orbit is a lower
bound for the orbit of the gate; a binomial estimate then bounds its total size by `κ - 1`.
-/
theorem supportSize_le {K : Type*} {n κ : ℕ} (hn : 20 ≤ n) (hκ : 3 * κ ≤ n + 2)
    (C : Circuit (Fin n × Fin n) K) (hred : C.IsReduced) (hsym : IsMatrixSymmetric C)
    (horb : orbitSize C < n.choose κ) :
    supportSize C ≤ κ - 1 := by
  have hrig : IsRigid C := ReducedRigid.isRigid hsym hred
  have hidx : ∀ g, (gateStabilizer hrig g).index < n.choose κ := fun g => by
    rw [← orbit_ncard_eq_index_gateStabilizer hrig g]
    exact lt_of_le_of_lt
      (Finset.le_sup (f := fun g => (orbit C g).ncard) (Finset.mem_univ g)) horb
  have hκ1 : 1 ≤ κ := by
    by_contra h0
    have h := hidx C.out
    have : κ = 0 := by omega
    subst this
    have : 0 < (gateStabilizer hrig C.out).index :=
      Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    simp at h
    omega
  have hgood := STSupports.exists_small_support hn hκ hκ1 hrig hred hidx
  apply Nat.sInf_le
  intro g
  obtain ⟨S, hS, hS2⟩ :=
    STMinimal.exists_support_le hn hrig hκ (fun g => hgood g) horb g
  exact ⟨S, hS, by omega⟩

end Lax461425Proofs.SupportTheorem
