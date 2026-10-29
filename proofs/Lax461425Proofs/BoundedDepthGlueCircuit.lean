import Lax461425Proofs.BoundedDepthGlueAcyclic

/-!
Assembling the glue circuit: `wire_eq_zero_of_isInput` and `reaches_out`, then the `Circuit`
structure itself.
-/

namespace Lax461425Proofs

open Lax461425.Circuits

open scoped Classical

variable {n m : ℕ} {K : Type*} [Field K] [CharZero K] (D : Fin m → Circuit (Fin n × Fin n) K)
  (f : Fin m → K)

theorem gwire_eq_zero_of_isInput (g h : GGate D) (hg : (glabel D f g).IsInput) :
    gwire D g h = 0 := by
  rcases g with ⟨i, y⟩ | i | i | ⟨⟩
  · have hginput : ((D i).label y).IsInput := hg
    rcases h with ⟨i', y'⟩ | i' | i' | ⟨⟩
    · rw [gwire_blk_blk]
      by_cases heq : i = i'
      · subst heq; simp only [dif_pos rfl]; exact (D i).wire_eq_zero_of_isInput y _ hginput
      · simp [dif_neg heq]
    · exact gwire_blk_scaled D i y i'
    · exact gwire_blk_const D i y i'
    · exact gwire_blk_out D i y
  · exact absurd hg (by simp [glabel, GateLabel.IsInput])
  · rcases h with ⟨i', y'⟩ | i' | i' | ⟨⟩ <;> exact gwire_const_any D i _
  · exact absurd hg (by simp [glabel, GateLabel.IsInput])

theorem greaches_out (g : GGate D) :
    Relation.ReflTransGen (fun h g => 0 < gwire D g h) g (outGG D) := by
  rcases g with ⟨i, y⟩ | i | i | ⟨⟩
  · have hyreach : Relation.ReflTransGen (fun h g => 0 < (D i).wire g h) y (D i).out :=
      (D i).reaches_out y
    have hlift : Relation.ReflTransGen (fun h g => 0 < gwire D g h) (blk D i y)
        (blk D i (D i).out) := by
      apply Relation.ReflTransGen.lift (blk D i) (fun a b hab => ?_) y (D i).out hyreach
      show 0 < gwire D (blk D i b) (blk D i a)
      rw [gwire_blk_blk]
      simpa using hab
    have hstep1 : 0 < gwire D (scaledG D i) (blk D i (D i).out) := by
      rw [gwire_scaled_blk]; simp
    have hstep2 : 0 < gwire D (outGG D) (scaledG D i) := gwire_out_scaled D i ▸ Nat.one_pos
    exact hlift.trans (Relation.ReflTransGen.head hstep1
      (Relation.ReflTransGen.head hstep2 Relation.ReflTransGen.refl))
  · exact Relation.ReflTransGen.head (gwire_out_scaled D i ▸ Nat.one_pos)
      Relation.ReflTransGen.refl
  · have hstep1 : 0 < gwire D (scaledG D i) (constG D i) := by
      rw [gwire_scaled_const]; simp
    have hstep2 : 0 < gwire D (outGG D) (scaledG D i) := gwire_out_scaled D i ▸ Nat.one_pos
    exact Relation.ReflTransGen.head hstep1
      (Relation.ReflTransGen.head hstep2 Relation.ReflTransGen.refl)
  · exact Relation.ReflTransGen.refl

/-- **The glue circuit.** -/
@[reducible] noncomputable def glueCircuit : Circuit (Fin n × Fin n) K where
  Gate := GGate D
  label := glabel D f
  wire := gwire D
  out := outGG D
  wire_eq_zero_of_isInput := gwire_eq_zero_of_isInput D f
  acyclic := gacyclic D
  reaches_out := greaches_out D

end Lax461425Proofs
