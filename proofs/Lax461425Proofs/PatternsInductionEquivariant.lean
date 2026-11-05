import Lax461425.SymmetricFamilies
import Mathlib.Algebra.MvPolynomial.Rename
import Lax461425.MatrixSymmetry
import Lax461425Proofs.RigidHeight
import Lax461425Proofs.PatternsSupportAction

/-!
A **generic `ComputesAt`-equivariance lemma**, for any `Circuit V K` (not specific to the
`Fin n × Fin n`-indexed circuits used elsewhere in this development): if `C.ComputesAt g p` and
`σ` is a circuit automorphism extending a renaming `π` of the variables (`Extends C σ π`), then
`C.ComputesAt (σ g) (MvPolynomial.rename π p)`.

The proof mirrors `RigidComputes.computesAt_unique`'s well-founded induction on the child
relation (`RigidHeight.wellFounded_child`), reindexing the defining sum/product of a sum/product
gate along the bijection `σ` of `C.Gate` and using `Extends`'s wire-multiplicity-preservation
clause to match up the reindexed weights.

Combined with `RigidComputes.computesAt_unique` (a gate computes at most one polynomial), this
gives the paper's equivariance fact `p_{γ g} = γ · p_g` for a rigid, matrix-symmetric circuit.
-/

open Lax461425.SymmetricFamilies (MatrixPolynomial)

namespace Lax461425Proofs.PatternsInductionEquivariant

open Lax461425.Circuits Lax461425.MatrixSymmetry

variable {V K : Type*} [CommSemiring K]

/-- **`ComputesAt` is equivariant under circuit automorphisms.** If `σ` is a circuit automorphism
extending the renaming `π` and `g` computes `p`, then `σ g` computes `MvPolynomial.rename π p`. -/
theorem computesAt_rename (D : Circuit V K) {σ : D.Gate ≃ D.Gate} {π : V → V}
    (hext : Extends D σ π) :
    ∀ {g : D.Gate} {p : MvPolynomial V K}, D.ComputesAt g p →
      D.ComputesAt (σ g) (MvPolynomial.rename π p) := by
  intro g
  induction g using (Lax461425Proofs.RigidHeight.wellFounded_child D).induction with
  | _ g ih =>
    intro p hp
    cases hp with
    | var hl =>
        rw [MvPolynomial.rename_X]
        refine Circuit.ComputesAt.var ?_
        rw [hext.1 g, hl]; rfl
    | const hl =>
        rw [MvPolynomial.rename_C]
        refine Circuit.ComputesAt.const ?_
        rw [hext.1 g, hl]; rfl
    | add q hl hq =>
        have hlabel : D.label (σ g) = GateLabel.add := by
          rw [hext.1 g, hl]; rfl
        have hq' : ∀ h', 0 < D.wire (σ g) h' →
            D.ComputesAt h' (MvPolynomial.rename π (q (σ.symm h'))) := by
          intro h' hpos
          have hwireeq : D.wire (σ g) (σ (σ.symm h')) = D.wire g (σ.symm h') := hext.2 g (σ.symm h')
          rw [Equiv.apply_symm_apply] at hwireeq
          have hposg : 0 < D.wire g (σ.symm h') := hwireeq ▸ hpos
          have hcomp : D.ComputesAt (σ.symm h') (q (σ.symm h')) := hq (σ.symm h') hposg
          have hres := ih (σ.symm h') hposg hcomp
          rwa [Equiv.apply_symm_apply] at hres
        have heq : MvPolynomial.rename π (∑ h, D.wire g h • q h) =
            ∑ h', D.wire (σ g) h' • MvPolynomial.rename π (q (σ.symm h')) := by
          rw [map_sum]
          rw [Finset.sum_congr rfl (fun h (_ : h ∈ Finset.univ) => map_nsmul
            (MvPolynomial.rename π) (D.wire g h) (q h))]
          exact Fintype.sum_equiv σ _ _
            (fun h => by rw [Equiv.symm_apply_apply, hext.2 g h])
        rw [heq]
        exact Circuit.ComputesAt.add _ hlabel hq'
    | mul q hl hq =>
        have hlabel : D.label (σ g) = GateLabel.mul := by
          rw [hext.1 g, hl]; rfl
        have hq' : ∀ h', 0 < D.wire (σ g) h' →
            D.ComputesAt h' (MvPolynomial.rename π (q (σ.symm h'))) := by
          intro h' hpos
          have hwireeq : D.wire (σ g) (σ (σ.symm h')) = D.wire g (σ.symm h') := hext.2 g (σ.symm h')
          rw [Equiv.apply_symm_apply] at hwireeq
          have hposg : 0 < D.wire g (σ.symm h') := hwireeq ▸ hpos
          have hcomp : D.ComputesAt (σ.symm h') (q (σ.symm h')) := hq (σ.symm h') hposg
          have hres := ih (σ.symm h') hposg hcomp
          rwa [Equiv.apply_symm_apply] at hres
        have heq : MvPolynomial.rename π (∏ h, (q h) ^ D.wire g h) =
            ∏ h', (MvPolynomial.rename π (q (σ.symm h'))) ^ D.wire (σ g) h' := by
          rw [map_prod]
          rw [Finset.prod_congr rfl (fun h (_ : h ∈ Finset.univ) => map_pow
            (MvPolynomial.rename π) (q h) (D.wire g h))]
          exact Fintype.prod_equiv σ _ _
            (fun h => by rw [Equiv.symm_apply_apply, hext.2 g h])
        rw [heq]
        exact Circuit.ComputesAt.mul _ hlabel hq'

/-! ### Specialised to the canonical automorphisms `σOf` coming from rigidity -/

open Lax461425Proofs.PatternsSupportAction

variable {n : ℕ}

/-- **The paper's equivariance fact `p_{γ g} = γ · p_g`.** For a rigid circuit `C`, if `g`
computes `p`, then `σOf hrig γ g` computes the renamed polynomial `MvPolynomial.rename
(actVar γ) p`. -/
theorem computesAt_σOf_rename {K : Type*} [Field K] {C : Circuit (Fin n × Fin n) K}
    (hrig : IsRigid C) (γ : Γ n) {g : C.Gate} {p : MatrixPolynomial n K}
    (hp : C.ComputesAt g p) :
    C.ComputesAt (σOf hrig γ g) (MvPolynomial.rename (actVar γ) p) :=
  computesAt_rename C (σOf_extends hrig γ) hp

end Lax461425Proofs.PatternsInductionEquivariant
