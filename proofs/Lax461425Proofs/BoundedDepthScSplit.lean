import Lax461425Proofs.PatternsSupportDepth

/-!
A generic upper bound for `PatternsSupportDepth.sc`, complementing the lower bounds
(`sc_mono`, `sc_succ_le_of_changing`) already available: `sc C g` is bounded by the maximum,
over the actual children `h` of `g`, of `sc C h` plus one more if the wire `g → h` is itself
support-changing. This is obtained by splitting an arbitrary witnessing path for `g` at its
first step.
-/

namespace Lax461425Proofs

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportBasic Lax461425Proofs.PatternsSupportDepth

open scoped Classical

variable {n : ℕ} {K : Type*} {C : Circuit (Fin n × Fin n) K}

/-- The `Fin`-arithmetic identity needed to match up the "tail" of a path's indexing with a
path one shorter. -/
theorem succ_castSucc_eq_castSucc_succ {M : ℕ} (j : Fin M) :
    (j.succ).castSucc = (j.castSucc).succ := by
  apply Fin.ext; simp

/-- **The upper bound for `sc`.** -/
theorem sc_le_of_first_step (g : C.Gate) :
    sc C g ≤ Finset.univ.sup (fun h : C.Gate => if 0 < C.wire g h then
      sc C h + (if ¬ minSupport C h ⊆ minSupport C g then 1 else 0) else 0) := by
  apply csSup_le'
  rintro c ⟨m, p, hp0, hp, rfl⟩
  match m, p, hp0, hp with
  | 0, p, _hp0, _hp =>
      have hz : supportChanges C p = 0 := by
        rw [show supportChanges C p = ({i : Fin 0 | ¬ minSupport C (p i.succ) ⊆
          minSupport C (p i.castSucc)} : Set (Fin 0)).ncard from rfl,
          Set.ncard_eq_zero (Set.toFinite _)]
        ext i; exact i.elim0
      rw [hz]; exact Nat.zero_le _
  | (M + 1), p, hp0, hp =>
      set h : C.Gate := p (1 : Fin (M + 2)) with hhdef
      set q : Fin (M + 1) → C.Gate := fun i => p i.succ with hqdef
      have hq0 : q (0 : Fin (M + 1)) = h := by
        rw [hqdef]; congr 1
      have hgh : 0 < C.wire g h := by
        have hstep := hp (0 : Fin (M + 1))
        have e1 : (0 : Fin (M + 1)).castSucc = (0 : Fin (M + 2)) := rfl
        have e2 : (0 : Fin (M + 1)).succ = (1 : Fin (M + 2)) := rfl
        rw [e1, e2, hp0] at hstep
        exact hstep
      have hqpath : C.IsPath q := by
        intro j
        show 0 < C.wire (p j.castSucc.succ) (p j.succ.succ)
        have hstep := hp j.succ
        rwa [succ_castSucc_eq_castSucc_succ j] at hstep
      -- Relating `supportChanges C p` to `supportChanges C q` and the first step.
      set A : Set (Fin (M + 1)) :=
        {i : Fin (M + 1) | ¬ minSupport C (p i.succ) ⊆ minSupport C (p i.castSucc)} with hAdef
      set B : Set (Fin M) :=
        {j : Fin M | ¬ minSupport C (q j.succ) ⊆ minSupport C (q j.castSucc)} with hBdef
      have hqc : B.ncard ≤ sc C h := supportChanges_le_sc hq0 hqpath
      have hAB : A \ {(0 : Fin (M + 1))} = Fin.succ '' B := by
        ext i
        simp only [Set.mem_sdiff, Set.mem_singleton_iff, hAdef, Set.mem_setOf_eq,
          Set.mem_image, hBdef]
        constructor
        · rintro ⟨hiA, hine⟩
          obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hine
          refine ⟨j, ?_, rfl⟩
          have e1 : (j.succ).castSucc = (j.castSucc).succ := succ_castSucc_eq_castSucc_succ j
          show ¬ minSupport C (p (j.succ).succ) ⊆ minSupport C (p (j.castSucc).succ)
          rwa [← e1]
        · rintro ⟨j, hj, rfl⟩
          refine ⟨?_, Fin.succ_ne_zero j⟩
          have e1 : (j.succ).castSucc = (j.castSucc).succ := succ_castSucc_eq_castSucc_succ j
          show ¬ minSupport C (p (j.succ).succ) ⊆ minSupport C (p (j.succ).castSucc)
          rwa [e1]
      have hAeq : A ⊆ insert (0 : Fin (M + 1)) (Fin.succ '' B) := by
        intro i hi
        by_cases hi0 : i = (0 : Fin (M + 1))
        · exact Set.mem_insert_iff.mpr (Or.inl hi0)
        · refine Set.mem_insert_iff.mpr (Or.inr ?_)
          rw [← hAB]
          exact ⟨hi, hi0⟩
      have hBcard : (Fin.succ '' B).ncard = B.ncard :=
        Set.ncard_image_of_injective B (Fin.succ_injective M)
      have hAcard : A.ncard ≤ (Fin.succ '' B).ncard + 1 :=
        le_trans (Set.ncard_le_ncard hAeq (Set.toFinite _))
          (Set.ncard_insert_le _ _)
      have hgoal_changing : (0 : Fin (M + 1)) ∈ A ↔ ¬ minSupport C h ⊆ minSupport C g := by
        show (¬ minSupport C (p (0 : Fin (M + 1)).succ) ⊆
          minSupport C (p (0 : Fin (M + 1)).castSucc)) ↔ _
        have e1 : (0 : Fin (M + 1)).castSucc = (0 : Fin (M + 2)) := rfl
        have e2 : (0 : Fin (M + 1)).succ = (1 : Fin (M + 2)) := rfl
        rw [e1, e2, hp0]
      have hAcard' : A.ncard ≤ B.ncard + 1 := by rw [← hBcard]; exact hAcard
      have hfinal : supportChanges C p ≤ sc C h +
          (if ¬ minSupport C h ⊆ minSupport C g then 1 else 0) := by
        show A.ncard ≤ sc C h + (if ¬ minSupport C h ⊆ minSupport C g then 1 else 0)
        by_cases hchg : ¬ minSupport C h ⊆ minSupport C g
        · rw [if_pos hchg]
          omega
        · rw [if_neg hchg]
          have hA0 : (0 : Fin (M + 1)) ∉ A := fun hc => hchg (hgoal_changing.mp hc)
          have hAeq' : A = Fin.succ '' B := by
            apply Set.Subset.antisymm
            · intro i hi
              have hine : i ≠ 0 := fun hc => hA0 (hc ▸ hi)
              have hmem : i ∈ A \ {(0 : Fin (M + 1))} := ⟨hi, hine⟩
              rw [hAB] at hmem
              exact hmem
            · intro i hi
              have hmem : i ∈ A \ {(0 : Fin (M + 1))} := by rw [hAB]; exact hi
              exact hmem.1
          rw [hAeq', hBcard]
          omega
      calc supportChanges C p ≤ sc C h + (if ¬ minSupport C h ⊆ minSupport C g then 1 else 0) :=
            hfinal
        _ ≤ Finset.univ.sup (fun h' : C.Gate => if 0 < C.wire g h' then
              sc C h' + (if ¬ minSupport C h' ⊆ minSupport C g then 1 else 0) else 0) := by
            have hmem : (if 0 < C.wire g h then
                sc C h + (if ¬ minSupport C h ⊆ minSupport C g then 1 else 0) else 0) ≤
              Finset.univ.sup (fun h' : C.Gate => if 0 < C.wire g h' then
                sc C h' + (if ¬ minSupport C h' ⊆ minSupport C g then 1 else 0) else 0) :=
              Finset.le_sup (f := fun h' : C.Gate => if 0 < C.wire g h' then
                sc C h' + (if ¬ minSupport C h' ⊆ minSupport C g then 1 else 0) else 0)
                (Finset.mem_univ h)
            rwa [if_pos hgh] at hmem

end Lax461425Proofs
