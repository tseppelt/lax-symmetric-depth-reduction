import Lax461425Proofs.BoundedDepthGlue
import Lax461425Proofs.RigidHeight

/-!
Acyclicity of the glue circuit: a measure `gmu` into `ℕ`, strictly decreasing along every
positive wire, built from each block's own `RigidHeight.height`, shifted by a uniform bound
`HBOUND` (the maximum height occurring in any block) so that the glue layer (`constG`,
`scaledG`, `outGG`) sits strictly above every block gate.
-/

namespace Lax461425Proofs

open Lax461425.Circuits RigidHeight

open scoped Classical

variable {n m : ℕ} {K : Type*} [Field K] [CharZero K] (D : Fin m → Circuit (Fin n × Fin n) K)

/-- A uniform bound on the height of any gate of any block. -/
noncomputable def HBOUND : ℕ :=
  Finset.univ.sup (fun i : Fin m => Finset.univ.sup (fun y : (D i).Gate => height (D i) y))

theorem height_le_HBOUND (i : Fin m) (y : (D i).Gate) : height (D i) y ≤ HBOUND D := by
  refine le_trans ?_ (Finset.le_sup (f := fun i : Fin m =>
    Finset.univ.sup (fun y : (D i).Gate => height (D i) y)) (Finset.mem_univ i))
  exact Finset.le_sup (f := fun y : (D i).Gate => height (D i) y) (Finset.mem_univ y)

/-- The acyclicity measure: a block gate's measure is its own height within that block; the
glue gates sit strictly above every block gate, ordered `constG < scaledG < outGG`. -/
noncomputable def gmu : GGate D → ℕ
  | Sum.inl ⟨i, y⟩ => height (D i) y
  | Sum.inr (Sum.inl _i) => HBOUND D + 2
  | Sum.inr (Sum.inr (Sum.inl _i)) => HBOUND D + 1
  | Sum.inr (Sum.inr (Sum.inr ())) => HBOUND D + 3

theorem gwire_pos_lt {g h : GGate D} (hgh : 0 < gwire D g h) : gmu D h < gmu D g := by
  rcases g with ⟨i, y⟩ | i | i | ⟨⟩ <;> rcases h with ⟨i', y'⟩ | i' | i' | ⟨⟩
  · -- blk → blk
    rw [gwire_blk_blk] at hgh
    by_cases heq : i = i'
    · subst heq
      simp only [dif_pos rfl] at hgh
      show height (D i) y' < height (D i) y
      exact height_child_lt (D i) hgh
    · simp [dif_neg heq] at hgh
  · rw [gwire_blk_scaled] at hgh; simp at hgh
  · rw [gwire_blk_const] at hgh; simp at hgh
  · rw [gwire_blk_out] at hgh; simp at hgh
  · -- scaled → blk
    rw [gwire_scaled_blk] at hgh
    by_cases heq : i = i'
    · subst heq
      simp only [dif_pos rfl] at hgh
      show height (D i) y' < HBOUND D + 2
      have := height_le_HBOUND D i y'
      omega
    · simp [dif_neg heq] at hgh
  · -- scaled → scaled
    rw [gwire_scaled_scaled] at hgh; simp at hgh
  · -- scaled → const
    show gmu D (constG D i') < gmu D (scaledG D i)
    show HBOUND D + 1 < HBOUND D + 2
    omega
  · rw [gwire_scaled_out] at hgh; simp at hgh
  · -- const → anything
    rw [gwire_const_any] at hgh; simp at hgh
  · rw [gwire_const_any] at hgh; simp at hgh
  · rw [gwire_const_any] at hgh; simp at hgh
  · rw [gwire_const_any] at hgh; simp at hgh
  · -- out → blk
    rw [gwire_out_blk] at hgh; simp at hgh
  · -- out → scaled
    show gmu D (scaledG D i') < gmu D (outGG D)
    show HBOUND D + 2 < HBOUND D + 3
    omega
  · rw [gwire_out_const] at hgh; simp at hgh
  · rw [gwire_out_out] at hgh; simp at hgh

theorem gacyclic (g : GGate D) : ¬ Relation.TransGen (fun h g => 0 < gwire D g h) g g := by
  intro hcycle
  have hmin : Relation.TransGen (fun h g => 0 < gwire D g h) ≤
      (fun a b => gmu D a < gmu D b) :=
    Relation.transGen_minimal (fun a b hab => gwire_pos_lt D hab)
  exact absurd (hmin g g hcycle) (lt_irrefl _)

end Lax461425Proofs
