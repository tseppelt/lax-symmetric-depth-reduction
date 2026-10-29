import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.Logic.Equiv.Fintype
import Lax461425Proofs.PatternsSupportBasic

/-!
A **transitivity lemma** needed for `lem:induction`'s internal-gate case: the pointwise
stabiliser `fixingSubgroup (Equiv.Perm (Fin n)) S` of a finite set `S : Set (Fin n)` acts
transitively on injective tuples `Fin m → Fin n` whose range avoids `S`.

Construction: work inside `β := {x : Fin n // x ∉ S}` (the complement of `S`, still finite).
Lifting `y, y'` to injective maps `Fin m → β`, `Equiv.ofInjective` gives equivalences of `Fin m`
with their ranges inside `β`, and composing gives an equivalence `e` between those two ranges
(both viewed as subtypes of `β`); `Equiv.extendSubtype e` extends `e` to a full permutation
`eπ` of `β`, agreeing with `e` (hence sending the lift of `y i` to the lift of `y' i`) on the
range of the lift of `y`. Finally, `Equiv.Perm.subtypeCongr` glues the identity on `S` with
`eπ` on `Sᶜ` into a single permutation of `Fin n`, which fixes `S` pointwise by construction and
sends `y` to `y'` pointwise since both avoid `S`.
-/

namespace Lax461425Proofs.PatternsInductionTransitive

open Lax461425.MatrixSymmetry
open Lax461425Proofs.PatternsSupportBasic
open scoped Classical

variable {n : ℕ}

/-- **Transitivity of the pointwise stabiliser on injective tuples avoiding a fixed set.**
Given `S : Set (Fin n)` and two injective tuples `y, y' : Fin m → Fin n` with ranges avoiding
`S`, there is a permutation of `Fin n` fixing `S` pointwise and sending `y` to `y'` pointwise. -/
theorem exists_fixing_perm_of_notMem {m : ℕ} {S : Set (Fin n)} {y y' : Fin m → Fin n}
    (hy : Function.Injective y) (hy' : Function.Injective y')
    (hyS : ∀ i, y i ∉ S) (hy'S : ∀ i, y' i ∉ S) :
    ∃ π : Equiv.Perm (Fin n), π ∈ fixingSubgroup (Equiv.Perm (Fin n)) S ∧ ∀ i, π (y i) = y' i := by
  classical
  set β := {x : Fin n // x ∉ S} with hβ
  set liftedY : Fin m → β := fun i => ⟨y i, hyS i⟩ with hliftedY
  set liftedY' : Fin m → β := fun i => ⟨y' i, hy'S i⟩ with hliftedY'
  have hliftedY_inj : Function.Injective liftedY := fun i j hij => hy (congrArg Subtype.val hij)
  have hliftedY'_inj : Function.Injective liftedY' := fun i j hij => hy' (congrArg Subtype.val hij)
  set e0 : Fin m ≃ Set.range liftedY := Equiv.ofInjective liftedY hliftedY_inj with he0
  set e0' : Fin m ≃ Set.range liftedY' := Equiv.ofInjective liftedY' hliftedY'_inj with he0'
  set e : ↥(Set.range liftedY) ≃ ↥(Set.range liftedY') := e0.symm.trans e0' with he
  set eπ : Equiv.Perm β := Equiv.extendSubtype e with heπ
  set π : Equiv.Perm (Fin n) :=
    Equiv.Perm.subtypeCongr (p := fun x : Fin n => x ∈ S) (Equiv.refl {x : Fin n // x ∈ S}) eπ
    with hπ
  refine ⟨π, ?_, ?_⟩
  · rw [mem_fixingSubgroup_iff]
    intro x hx
    show π x = x
    rw [hπ, Equiv.Perm.subtypeCongr.left_apply _ _ hx]
    rfl
  · intro i
    have hnotS : y i ∉ S := hyS i
    have hπeq : π (y i) = eπ ⟨y i, hnotS⟩ := by
      rw [hπ]; exact Equiv.Perm.subtypeCongr.right_apply _ _ hnotS
    have hmem : (⟨y i, hnotS⟩ : β) ∈ Set.range liftedY := ⟨i, rfl⟩
    have heπeq : eπ (⟨y i, hnotS⟩ : β) = liftedY' i := by
      rw [heπ, Equiv.extendSubtype_apply_of_mem e _ hmem]
      show (e ⟨liftedY i, hmem⟩ : β) = liftedY' i
      have hval : e0.symm ⟨liftedY i, hmem⟩ = i := by
        rw [Equiv.symm_apply_eq]; rfl
      show (e0.symm.trans e0') ⟨liftedY i, hmem⟩ = liftedY' i
      rw [Equiv.trans_apply, hval]
      rfl
    rw [hπeq, heπeq]

/-! ### The `Γ n`-combined version, needed for the `Y_u` transitivity in `lem:induction` -/

/-- **Transitivity of `fixingSubgroup (Γ n) S` on pairs of injective tuples avoiding `S` on each
side.** Combines `exists_fixing_perm_of_notMem` on each of the two sides of `S` independently,
then glues the two resulting permutations into a single `γ : Γ n` fixing `S` pointwise via
`fixingSubgroupΓ_eq_prod`. -/
theorem exists_fixing_Γ_of_notMem {ℓ' r' : ℕ} {S : Set (Fin n ⊕ Fin n)}
    {y y' : Fin ℓ' → Fin n} {z z' : Fin r' → Fin n}
    (hy : Function.Injective y) (hy' : Function.Injective y')
    (hz : Function.Injective z) (hz' : Function.Injective z')
    (hyS : ∀ i, y i ∉ leftPart S) (hy'S : ∀ i, y' i ∉ leftPart S)
    (hzS : ∀ j, z j ∉ rightPart S) (hz'S : ∀ j, z' j ∉ rightPart S) :
    ∃ γ : Γ n, γ ∈ fixingSubgroup (Γ n) S ∧ (∀ i, γ.1 (y i) = y' i) ∧ (∀ j, γ.2 (z j) = z' j) := by
  obtain ⟨π1, hπ1mem, hπ1⟩ := exists_fixing_perm_of_notMem hy hy' hyS hy'S
  obtain ⟨π2, hπ2mem, hπ2⟩ := exists_fixing_perm_of_notMem hz hz' hzS hz'S
  refine ⟨(π1, π2), ?_, hπ1, hπ2⟩
  rw [fixingSubgroupΓ_eq_prod]
  exact Subgroup.mem_prod.mpr ⟨hπ1mem, hπ2mem⟩

end Lax461425Proofs.PatternsInductionTransitive
