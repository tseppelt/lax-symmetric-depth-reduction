import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Choose.Bounds
import Lax461425Proofs.PatternsSupportBasic

/-!
**A general, reusable fact** (the paper's `obs:support-orbit`): a rigid circuit all of whose
gates have a support of size `≤ k` has orbit size `≤ n ^ k`. This is proved here purely in terms
of the generic `Lax461425.Supports`/`Lax461425.MatrixSymmetry` API (`IsSupport`, `orbitSize`,
`IsRigid`) and the generic bridge to group theory already built in `PatternsSupportAction.lean`/
`PatternsSupportBasic.lean` (`σOf`, `gateStabilizer`, `isSupport_iff_fixingSubgroup_le`); nothing
here is specific to the `thm:converse` construction, so it is proved for an arbitrary rigid
`C : Circuit (Fin n × Fin n) K`.

The two ingredients are:

* the orbit-stabiliser theorem (`MulAction.index_stabilizer`), transported from the abstract
  group action `gateMulAction hrig` to the circuit's own `orbit`/`gateStabilizer` API
  (`orbit_ncard_eq_index_gateStabilizer`);
* a direct count of the index of `fixingSubgroup (Γ n) S` for a finite `S : Set (Fin n ⊕ Fin n)`,
  via the multiple-transitivity of `Equiv.Perm (Fin n)` on each side of `S` separately
  (`index_fixingSubgroupΓ_le`).
-/

namespace Lax461425Proofs

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic

section IndexBounds

variable {n : ℕ}

/-- The index of the pointwise stabiliser, in `Equiv.Perm (Fin n)`, of a finite subset `T` of
`Fin n`, is at most `n ^ T.ncard`: the index is exactly the descending factorial
`n (n - 1) ⋯ (n - |T| + 1)`, which is bounded term-by-term by `n ^ |T|`. -/
theorem index_fixingSubgroup_perm_le (T : Set (Fin n)) :
    (fixingSubgroup (Equiv.Perm (Fin n)) T).index ≤ n ^ T.ncard := by
  have hMk : MulAction.IsMultiplyPretransitive (Equiv.Perm (Fin n)) (Fin n) T.ncard :=
    Equiv.Perm.isMultiplyPretransitive (Fin n) T.ncard
  rw [MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq T hMk, Nat.card_fin,
    mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.descFactorial_le_pow n T.ncard

/-- A finite subset `S` of `[n] ⊎ [n]` splits, via its two sides, into a disjoint union, so its
cardinality is the sum of the cardinalities of the two sides. -/
theorem ncard_eq_leftPart_add_rightPart (S : Set (Fin n ⊕ Fin n)) :
    S.ncard = (PatternsSupportBasic.leftPart S).ncard + (PatternsSupportBasic.rightPart S).ncard := by
  have hSeq : S = Sum.inl '' PatternsSupportBasic.leftPart S ∪
      Sum.inr '' PatternsSupportBasic.rightPart S := by
    apply Set.ext
    rintro (i | j) <;> simp [PatternsSupportBasic.leftPart, PatternsSupportBasic.rightPart]
  have hdisj : Disjoint (Sum.inl '' PatternsSupportBasic.leftPart S)
      ((Sum.inr '' PatternsSupportBasic.rightPart S : Set (Fin n ⊕ Fin n))) := by
    rw [Set.disjoint_left]
    rintro x ⟨i, -, rfl⟩ ⟨j, -, hij⟩
    exact absurd hij (by simp)
  calc S.ncard
      = (Sum.inl '' PatternsSupportBasic.leftPart S ∪
          Sum.inr '' PatternsSupportBasic.rightPart S).ncard := congrArg Set.ncard hSeq
    _ = (Sum.inl '' PatternsSupportBasic.leftPart S).ncard +
          (Sum.inr '' PatternsSupportBasic.rightPart S).ncard := Set.ncard_union_eq hdisj
    _ = (PatternsSupportBasic.leftPart S).ncard + (PatternsSupportBasic.rightPart S).ncard := by
        rw [Set.ncard_image_of_injective _ Sum.inl_injective,
          Set.ncard_image_of_injective _ Sum.inr_injective]

/-- The index of the pointwise stabiliser, in `Γ n`, of a finite subset `S` of `[n] ⊎ [n]`, is at
most `n ^ S.ncard`. -/
theorem index_fixingSubgroupΓ_le (S : Set (Fin n ⊕ Fin n)) :
    (fixingSubgroup (Γ n) S).index ≤ n ^ S.ncard := by
  rw [PatternsSupportBasic.fixingSubgroupΓ_eq_prod, Subgroup.index_prod,
    ncard_eq_leftPart_add_rightPart, pow_add]
  exact Nat.mul_le_mul (index_fixingSubgroup_perm_le _) (index_fixingSubgroup_perm_le _)

end IndexBounds

section OrbitBound

variable {n : ℕ} {K : Type*} {C : Circuit (Fin n × Fin n) K}

/-- The orbit of a gate under the circuit automorphisms extending elements of `Γ n` is, for a
rigid circuit, exactly its orbit under the canonical group action `gateMulAction hrig`. -/
theorem orbit_eq_mulActionOrbit (hrig : IsRigid C) (g : C.Gate) :
    letI := gateMulAction hrig
    orbit C g = MulAction.orbit (Γ n) g := by
  let _ := gateMulAction hrig
  apply Set.ext
  intro g'
  constructor
  · rintro ⟨γ, σ, hext, rfl⟩
    refine ⟨γ, ?_⟩
    show σOf hrig γ g = σ g
    rw [σOf_unique hrig hext]
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, σOf hrig γ, σOf_extends hrig γ, ?_⟩
    show σOf hrig γ g = g'
    rw [← hγ]
    rfl

/-- The `Γ n`-pointwise stabiliser of a gate `g`, under the canonical action `gateMulAction
hrig`, is exactly `gateStabilizer hrig g`. -/
theorem stabilizer_eq_gateStabilizer (hrig : IsRigid C) (g : C.Gate) :
    letI := gateMulAction hrig
    MulAction.stabilizer (Γ n) g = gateStabilizer hrig g := by
  let _ := gateMulAction hrig
  apply Subgroup.ext
  intro γ
  show γ • g = g ↔ σOf hrig γ g = g
  rw [gateMulAction_smul_def]

/-- **The orbit-stabiliser bridge.** The cardinality of the orbit of a gate `g`, under the
circuit automorphisms extending elements of `Γ n`, equals the index of its `gateStabilizer`. -/
theorem orbit_ncard_eq_index_gateStabilizer (hrig : IsRigid C) (g : C.Gate) :
    (orbit C g).ncard = (gateStabilizer hrig g).index := by
  let _ := gateMulAction hrig
  rw [orbit_eq_mulActionOrbit hrig g, ← MulAction.index_stabilizer (Γ n) g,
    stabilizer_eq_gateStabilizer hrig g]

/-- **The general support-orbit bound** (the paper's `obs:support-orbit`): for a rigid circuit
all of whose gates have a support of size `≤ k`, the orbit size is at most `n ^ k`. -/
theorem orbitSize_le_pow_of_support (hrig : IsRigid C) (hn0 : 0 < n) {k : ℕ}
    (hk : ∀ g : C.Gate, ∃ S : Set (Fin n ⊕ Fin n), IsSupport C g S ∧ S.ncard ≤ k) :
    orbitSize C ≤ n ^ k := by
  apply Finset.sup_le
  intro g _
  obtain ⟨S, hS, hSc⟩ := hk g
  have h1 : fixingSubgroup (Γ n) S ≤ gateStabilizer hrig g :=
    (PatternsSupportBasic.isSupport_iff_fixingSubgroup_le hrig g S).mp hS
  have h2 : (gateStabilizer hrig g).index ≤ (fixingSubgroup (Γ n) S).index :=
    Subgroup.index_antitone h1
  calc (orbit C g).ncard = (gateStabilizer hrig g).index :=
        orbit_ncard_eq_index_gateStabilizer hrig g
    _ ≤ (fixingSubgroup (Γ n) S).index := h2
    _ ≤ n ^ S.ncard := index_fixingSubgroupΓ_le S
    _ ≤ n ^ k := Nat.pow_le_pow_right hn0 hSc

/-- **Corollary.** A rigid circuit of support size `≤ k` has orbit size `≤ n ^ k`. -/
theorem orbitSize_le_pow_of_supportSize_le (hrig : IsRigid C) (hn0 : 0 < n) {k : ℕ}
    (hsupp : supportSize C ≤ k) : orbitSize C ≤ n ^ k :=
  le_trans
    (orbitSize_le_pow_of_support hrig hn0 (fun g => PatternsSupportBasic.supportSize_spec hrig g))
    (Nat.pow_le_pow_right hn0 hsupp)

end OrbitBound

end Lax461425Proofs
