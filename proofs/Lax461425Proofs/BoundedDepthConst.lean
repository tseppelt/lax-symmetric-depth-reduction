import Lax461425.Supports

/-!
A single-gate "constant circuit" computing `MvPolynomial.C c` for any `c : K`. Used for two
purposes: the degenerate case `p = 0` (take `c = 0`) in the backward direction of
`BoundedDepthCharacterisation.characterisation`, and patterns `F` with no edges in
`CircuitsForPatterns.exists_circuit`, whose homomorphism polynomial `hom K F n` is itself a
constant.
-/

namespace Lax461425Proofs

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open MvPolynomial

variable {K : Type*} [Field K] [CharZero K] {n : ℕ} (c : K)

/-- The single-gate circuit with one `const c` input gate, which is also its own output. -/
@[reducible] noncomputable def constCircuit : Circuit (Fin n × Fin n) K where
  Gate := Unit
  label _ := .const c
  wire _ _ := 0
  out := ()
  wire_eq_zero_of_isInput _ _ _ := rfl
  acyclic g h := by
    cases h with
    | single h' => exact absurd h' (lt_irrefl 0)
    | tail _ h' => exact absurd h' (lt_irrefl 0)
  reaches_out g := by cases g; exact Relation.ReflTransGen.refl

omit [CharZero K] in
theorem constCircuit_computes : (constCircuit c : Circuit (Fin n × Fin n) K).Computes (C c) :=
  Circuit.ComputesAt.const rfl

omit [Field K] [CharZero K] in
theorem constCircuit_isReduced : (constCircuit c : Circuit (Fin n × Fin n) K).IsReduced :=
  ⟨fun g g' _ _ => Subsingleton.elim g g', fun g g' _ _ _ => Subsingleton.elim g g'⟩

omit [Field K] [CharZero K] in
theorem constCircuit_isMatrixSymmetric :
    IsMatrixSymmetric (constCircuit c : Circuit (Fin n × Fin n) K) := by
  intro γ
  refine ⟨Equiv.refl Unit, fun g => ?_, fun g h => rfl⟩
  show (constCircuit c : Circuit (Fin n × Fin n) K).label g =
    ((constCircuit c : Circuit (Fin n × Fin n) K).label g).map (actVar γ)
  rfl

omit [Field K] [CharZero K] in
/-- The empty set trivially supports the unique gate of `constCircuit c`. -/
theorem constCircuit_isSupport_empty :
    IsSupport (constCircuit c : Circuit (Fin n × Fin n) K) ()
      (∅ : Set (Fin n ⊕ Fin n)) :=
  fun _γ σ _hfix _hext => Subsingleton.elim (σ ()) ()

omit [Field K] [CharZero K] in
theorem constCircuit_supportSize :
    supportSize (constCircuit c : Circuit (Fin n × Fin n) K) = 0 := by
  apply le_antisymm _ (Nat.zero_le _)
  apply Nat.sInf_le
  intro g
  cases g
  exact ⟨∅, constCircuit_isSupport_empty c, by simp⟩

omit [Field K] [CharZero K] in
/-- No actual path of `constCircuit c` has positive length: the gate has no children. -/
theorem constCircuit_isPath_length_zero {m : ℕ}
    (p : Fin (m + 1) → (constCircuit c : Circuit (Fin n × Fin n) K).Gate)
    (hp : (constCircuit c : Circuit (Fin n × Fin n) K).IsPath p) : m = 0 := by
  by_contra hne
  have hm : 0 < m := Nat.pos_of_ne_zero hne
  have := hp ⟨0, hm⟩
  exact absurd this (lt_irrefl 0)

omit [Field K] [CharZero K] in
theorem constCircuit_supportDepth (hn0 : 0 < n) :
    supportDepth (constCircuit c : Circuit (Fin n × Fin n) K) = 0 := by
  have hss : supportSize (constCircuit c : Circuit (Fin n × Fin n) K) = 0 :=
    constCircuit_supportSize c
  show (if 2 * supportSize (constCircuit c : Circuit (Fin n × Fin n) K) < n then
      sSup {d | ∃ (m : ℕ) (p : Fin (m + 1) → (constCircuit c : Circuit (Fin n × Fin n) K).Gate),
        (constCircuit c : Circuit (Fin n × Fin n) K).IsPath p ∧
          supportChanges (constCircuit c : Circuit (Fin n × Fin n) K) p = d}
    else (constCircuit c : Circuit (Fin n × Fin n) K).depth) = 0
  rw [if_pos (by rw [hss]; omega)]
  apply le_antisymm _ (Nat.zero_le _)
  apply csSup_le'
  rintro d ⟨m, p, hp, rfl⟩
  have hm0 : m = 0 := constCircuit_isPath_length_zero c p hp
  subst hm0
  show ({i : Fin 0 | _} : Set (Fin 0)).ncard ≤ 0
  rw [Nat.le_zero, Set.ncard_eq_zero (Set.toFinite _)]
  ext i; exact i.elim0

omit [Field K] [CharZero K] in
theorem constCircuit_orbitSize_le :
    orbitSize (constCircuit c : Circuit (Fin n × Fin n) K) ≤ 1 := by
  apply Finset.sup_le
  intro g _
  calc (orbit (constCircuit c : Circuit (Fin n × Fin n) K) g).ncard
      ≤ (Set.univ : Set Unit).ncard := Set.ncard_le_ncard (Set.subset_univ _)
    _ = 1 := by simp [Set.ncard_univ]

omit [Field K] [CharZero K] in
theorem constCircuit_depth : (constCircuit c : Circuit (Fin n × Fin n) K).depth = 0 := by
  apply le_antisymm _ (Nat.zero_le _)
  apply csSup_le'
  rintro m ⟨p, hp⟩
  exact (constCircuit_isPath_length_zero c p hp).le

omit [Field K] [CharZero K] in
theorem constCircuit_size : (constCircuit c : Circuit (Fin n × Fin n) K).size = 1 := by
  simp [Circuit.size]

end Lax461425Proofs
