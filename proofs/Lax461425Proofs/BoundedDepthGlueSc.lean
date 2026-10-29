import Lax461425Proofs.BoundedDepthGlueSupportFormula
import Lax461425Proofs.BoundedDepthScSplit
import Lax461425Proofs.RigidWeight

/-!
**The support-depth bound for the rigidified glue circuit.** We bound `sc (reduced E) (toC' E
x)` for every gate `x` of `E := glueCircuit D f`, by well-founded induction on `E`'s child
relation, against a potential `PhiG` built from each block's own `sc`. Combined with
`supportChanges_le_sc`, this gives `supportDepth (reduced E) ≤ Δ`.
-/

namespace Lax461425Proofs

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.RigidConstruction Lax461425Proofs.RigidHeight Lax461425Proofs.RigidWeight
open Lax461425Proofs.PatternsSupportBasic Lax461425Proofs.PatternsSupportDepth

open scoped Classical

variable {n m : ℕ} {K : Type*} [Field K] [CharZero K] (D : Fin m → Circuit (Fin n × Fin n) K)
  (f : Fin m → K)

/-- The potential: a block gate's potential is its own `sc` within that block; `scaledG i`'s is
`sc (D i) (D i).out` (accounting for the pendant structure below it); `constG i`'s is `0` (a
true leaf); `outGG`'s is the maximum of `sc (D i) (D i).out` over all blocks. -/
noncomputable def PhiG : GGate D → ℕ
  | Sum.inl ⟨i, y⟩ => sc (D i) y
  | Sum.inr (Sum.inl i) => sc (D i) (D i).out
  | Sum.inr (Sum.inr (Sum.inl _i)) => 0
  | Sum.inr (Sum.inr (Sum.inr ())) => Finset.univ.sup (fun i : Fin m => sc (D i) (D i).out)

theorem PhiG_le_of_bound {Δ : ℕ} (hΔ : ∀ i, supportDepth (D i) ≤ Δ) (x : GGate D) :
    PhiG D x ≤ Δ := by
  rcases x with ⟨i, y⟩ | i | i | ⟨⟩
  · exact le_trans (sc_le_supportDepth y) (hΔ i)
  · exact le_trans (sc_le_supportDepth (D i).out) (hΔ i)
  · exact Nat.zero_le _
  · apply Finset.sup_le
    intro i _
    exact le_trans (sc_le_supportDepth (D i).out) (hΔ i)

/-- **The main `sc` bound**, by well-founded induction on `glueCircuit D f`'s child relation. -/
theorem sc_reduced_le_PhiG (hred : ∀ i, (D i).IsReduced) (hsym : ∀ i, IsMatrixSymmetric (D i))
    (hrigRed : IsRigid (reduced (glueCircuit D f))) {k : ℕ}
    (hssE : supportSize (reduced (glueCircuit D f)) ≤ k)
    (hssD : ∀ i, supportSize (D i) ≤ k) (hn : 2 * k < n) :
    ∀ x : GGate D, sc (reduced (glueCircuit D f)) (toC' (glueCircuit D f) x) ≤ PhiG D x := by
  intro x0
  refine (wellFounded_child (glueCircuit D f)).induction
    (C := fun z => sc (reduced (glueCircuit D f)) (toC' (glueCircuit D f) z) ≤ PhiG D z) x0
    (fun x ih => ?_)
  · have hstep := sc_le_of_first_step (C := reduced (glueCircuit D f)) (toC' (glueCircuit D f) x)
    apply le_trans hstep
    apply Finset.sup_le
    intro b' _
    by_cases hwpos : 0 < (reduced (glueCircuit D f)).wire (toC' (glueCircuit D f) x) b'
    swap
    · rw [if_neg hwpos]; exact Nat.zero_le _
    rw [if_pos hwpos]
    have hWpos : 0 < W (glueCircuit D f) x b'.1 := by
      have heq : (reduced (glueCircuit D f)).wire (toC' (glueCircuit D f) x) b' =
          W (glueCircuit D f) (RigidRep.rep (glueCircuit D f) x) b'.1 := rfl
      rw [heq, ← W_eq_of_equiv (glueCircuit D f) (RigidRep.rep_equiv (glueCircuit D f) x)] at hwpos
      -- `hwpos` is already in terms of `x`
      exact hwpos
    obtain ⟨h', hequiv, hwirepos⟩ := exists_of_W_pos (glueCircuit D f) hWpos
    have htoC' : toC' (glueCircuit D f) h' = b' :=
      (RigidSymmetric.toC'_eq_of_equiv (glueCircuit D f) hequiv).trans
        (toC'_self (glueCircuit D f) b')
    have hih := ih h' hwirepos
    rw [htoC'] at hih
    -- Now case on `x`'s shape (and the constrained shape of `h'`) to compare potentials.
    rcases x with ⟨i, y⟩ | i | i | ⟨⟩
    · -- x = blk i y: h' is confined to block i, i.e. h' = blk i y' for some D i-child y'.
      show sc (reduced (glueCircuit D f)) b' +
          (if ¬ minSupport (reduced (glueCircuit D f)) b' ⊆
              minSupport (reduced (glueCircuit D f)) (toC' (glueCircuit D f) (blk D i y))
            then 1 else 0) ≤ PhiG D (blk D i y)
      have hwirepos2 : 0 < (glueCircuit D f).wire (blk D i y) h' := hwirepos
      obtain ⟨y', rfl⟩ : ∃ y', h' = blk D i y' := by
        by_contra hc
        push Not at hc
        rw [glueCircuit_wire] at hwirepos2
        have hz : gwire D (blk D i y) h' = 0 := blk_wire_eq_zero_of_not_blk D hc
        omega
      have hypos : 0 < (D i).wire y y' := by
        rwa [glueCircuit_wire, gwire_blk_blk_self] at hwirepos2
      have hmA : minSupport (reduced (glueCircuit D f)) (toC' (glueCircuit D f) (blk D i y)) =
          minSupport (D i) y :=
        minSupport_reduced_blk_eq D f hred hsym i hrigRed hssE (hssD i) hn y
      have hmB : minSupport (reduced (glueCircuit D f)) (toC' (glueCircuit D f) (blk D i y')) =
          minSupport (D i) y' :=
        minSupport_reduced_blk_eq D f hred hsym i hrigRed hssE (hssD i) hn y'
      have hmB' : minSupport (reduced (glueCircuit D f)) b' = minSupport (D i) y' := by
        rw [← htoC']; exact hmB
      rw [hmA, hmB'] at *
      simp only [PhiG] at hih ⊢
      by_cases hchg : ¬ minSupport (D i) y' ⊆ minSupport (D i) y
      · have := sc_succ_le_of_changing hypos hchg
        rw [if_pos hchg]
        omega
      · have := sc_mono hypos
        rw [if_neg hchg]
        omega
    · -- x = scaledG i: h' is either `blk i (D i).out` or `constG i`.
      show sc (reduced (glueCircuit D f)) b' +
          (if ¬ minSupport (reduced (glueCircuit D f)) b' ⊆
              minSupport (reduced (glueCircuit D f)) (toC' (glueCircuit D f) (scaledG D i))
            then 1 else 0) ≤ PhiG D (scaledG D i)
      have hwirepos' : 0 < gwire D (scaledG D i) h' := by
        have : 0 < (glueCircuit D f).wire (scaledG D i) h' := hwirepos
        rwa [glueCircuit_wire] at this
      have hmA : minSupport (reduced (glueCircuit D f)) (toC' (glueCircuit D f) (scaledG D i)) =
          (∅ : Set (Fin n ⊕ Fin n)) :=
        minSupport_reduced_glue_eq D f hred hsym hrigRed (fun j y hc => by cases hc)
      rw [hmA] at *
      rcases h' with ⟨i', y'⟩ | i' | i' | ⟨⟩
      · -- h' = blk i' y'
        rw [gwire_scaled_blk] at hwirepos'
        by_cases heq : i = i'
        · subst heq
          by_cases hy : y' = (D i).out
          · subst hy
            have hmB : minSupport (reduced (glueCircuit D f))
                (toC' (glueCircuit D f) (blk D i (D i).out)) = minSupport (D i) (D i).out :=
              minSupport_reduced_blk_eq D f hred hsym i hrigRed hssE (hssD i) hn (D i).out
            rw [minSupport_out (D i)] at hmB
            have hmB' : minSupport (reduced (glueCircuit D f)) b' = (∅ : Set (Fin n ⊕ Fin n)) := by
              rw [← htoC']; exact hmB
            rw [hmB'] at *
            simp only [PhiG] at hih ⊢
            rw [if_neg (by simp)]
            omega
          · simp [hy] at hwirepos'
        · simp [dif_neg heq] at hwirepos'
      · -- h' = scaledG i': impossible (0 wire)
        rw [gwire_scaled_scaled] at hwirepos'; omega
      · -- h' = constG i'
        have hmB : minSupport (reduced (glueCircuit D f)) (toC' (glueCircuit D f) (constG D i')) =
            (∅ : Set (Fin n ⊕ Fin n)) :=
          minSupport_reduced_glue_eq D f hred hsym hrigRed (fun j y hc => by cases hc)
        have hmB' : minSupport (reduced (glueCircuit D f)) b' = (∅ : Set (Fin n ⊕ Fin n)) := by
          rw [← htoC']; exact hmB
        rw [hmB'] at *
        simp only [PhiG] at hih ⊢
        rw [if_neg (by simp)]
        omega
      · -- h' = outGG: impossible (0 wire)
        rw [gwire_scaled_out] at hwirepos'; omega
    · -- x = constG i: no actual children.
      have : 0 < (glueCircuit D f).wire (constG D i) h' := hwirepos
      rw [glueCircuit_wire, gwire_const_any] at this
      omega
    · -- x = outGG: h' = scaledG i' for some i'.
      show sc (reduced (glueCircuit D f)) b' +
          (if ¬ minSupport (reduced (glueCircuit D f)) b' ⊆
              minSupport (reduced (glueCircuit D f)) (toC' (glueCircuit D f) (outGG D))
            then 1 else 0) ≤ PhiG D (outGG D)
      have hwirepos' : 0 < gwire D (outGG D) h' := by
        have : 0 < (glueCircuit D f).wire (outGG D) h' := hwirepos
        rwa [glueCircuit_wire] at this
      have hmA : minSupport (reduced (glueCircuit D f)) (toC' (glueCircuit D f) (outGG D)) =
          (∅ : Set (Fin n ⊕ Fin n)) :=
        minSupport_reduced_glue_eq D f hred hsym hrigRed (fun j y hc => by cases hc)
      rw [hmA] at *
      rcases h' with ⟨i', y'⟩ | i' | i' | ⟨⟩
      · rw [gwire_out_blk] at hwirepos'; omega
      · have hmB : minSupport (reduced (glueCircuit D f)) (toC' (glueCircuit D f) (scaledG D i')) =
            (∅ : Set (Fin n ⊕ Fin n)) :=
          minSupport_reduced_glue_eq D f hred hsym hrigRed (fun j y hc => by cases hc)
        have hmB' : minSupport (reduced (glueCircuit D f)) b' = (∅ : Set (Fin n ⊕ Fin n)) := by
          rw [← htoC']; exact hmB
        rw [hmB'] at *
        have hle : sc (D i') (D i').out ≤ Finset.univ.sup (fun j : Fin m => sc (D j) (D j).out) :=
          Finset.le_sup (f := fun j : Fin m => sc (D j) (D j).out) (Finset.mem_univ i')
        simp only [PhiG] at hih ⊢
        rw [if_neg (by simp)]
        omega
      · rw [gwire_out_const] at hwirepos'; omega
      · rw [gwire_out_out] at hwirepos'; omega

/-- **Item: `supportDepth (reduced (glueCircuit D f)) ≤ Δ`.** -/
theorem glueCircuit_reduced_supportDepth_le (hred : ∀ i, (D i).IsReduced)
    (hsym : ∀ i, IsMatrixSymmetric (D i)) (hrigRed : IsRigid (reduced (glueCircuit D f)))
    {k Δ : ℕ} (hssE : supportSize (reduced (glueCircuit D f)) ≤ k) (hssD : ∀ i, supportSize (D i) ≤ k)
    (hn : 2 * k < n) (hΔ : ∀ i, supportDepth (D i) ≤ Δ) :
    supportDepth (reduced (glueCircuit D f)) ≤ Δ := by
  show (if 2 * supportSize (reduced (glueCircuit D f)) < n then
      sSup {c | ∃ (m' : ℕ) (p : Fin (m' + 1) → (reduced (glueCircuit D f)).Gate),
        (reduced (glueCircuit D f)).IsPath p ∧
          supportChanges (reduced (glueCircuit D f)) p = c}
    else (reduced (glueCircuit D f)).depth) ≤ Δ
  rw [if_pos (by omega)]
  apply csSup_le'
  rintro c ⟨m', p, hp, rfl⟩
  refine le_trans (supportChanges_le_sc rfl hp) ?_
  have hp0 := toC'_self (glueCircuit D f) (p 0)
  calc sc (reduced (glueCircuit D f)) (p 0)
      = sc (reduced (glueCircuit D f)) (toC' (glueCircuit D f) (p 0).1) := by rw [hp0]
    _ ≤ PhiG D (p 0).1 := sc_reduced_le_PhiG D f hred hsym hrigRed hssE hssD hn (p 0).1
    _ ≤ Δ := PhiG_le_of_bound D hΔ (p 0).1

end Lax461425Proofs
