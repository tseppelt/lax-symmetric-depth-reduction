import Lax461425.Circuits

/-!
Helper material for the rigidification proof: the "height" of a gate, defined as the maximum
length of a path of the circuit starting at that gate, computed by well-founded recursion on the
(finite, acyclic) child relation.
-/

namespace Lax461425Proofs.RigidHeight

open Lax461425.Circuits

variable {V K : Type*}

/-- The relation "`h` is a child of `g`", i.e. there is a wire from `h` into `g`. -/
def Child (C : Circuit V K) (g h : C.Gate) : Prop := 0 < C.wire g h

variable (C : Circuit V K)

instance Child.decidable (g h : C.Gate) : Decidable (Child C g h) :=
  inferInstanceAs (Decidable (0 < C.wire g h))

private instance : Std.Irrefl (Relation.TransGen fun (h g : C.Gate) => Child C g h) :=
  ⟨C.acyclic⟩

/-- The relation "`h` is a child of `g`", read backwards, is well-founded: a finite acyclic
relation has no infinite descending chain. -/
theorem wellFounded_child : WellFounded fun (h g : C.Gate) => Child C g h := by
  have hsub : Subrelation (fun (h g : C.Gate) => Child C g h)
      (Relation.TransGen fun (h g : C.Gate) => Child C g h) :=
    fun hc => Relation.TransGen.single hc
  exact Subrelation.wf hsub (Finite.wellFounded_of_trans_of_irrefl _)

/-- The height of a gate: the maximum length of a path of `C` starting at that gate. Defined by
well-founded recursion on the child relation: a gate without children has height `0`, and
otherwise the height is one more than the maximum height of a child. -/
noncomputable def height : C.Gate → ℕ :=
  (wellFounded_child C).fix
    (fun g ih => Finset.univ.sup (fun h => if hc : Child C g h then ih h hc + 1 else 0))

/-- The defining equation for `height`. -/
theorem height_eq (g : C.Gate) :
    height C g = Finset.univ.sup
      (fun h => if _hc : Child C g h then height C h + 1 else 0) :=
  WellFounded.fix_eq _ _ _

/-- A child has strictly smaller height than its parent. -/
theorem height_child_lt {g h : C.Gate} (hc : Child C g h) : height C h < height C g := by
  have hmem : (if hc' : Child C g h then height C h + 1 else 0) ≤
      Finset.univ.sup (fun h' => if hc' : Child C g h' then height C h' + 1 else 0) :=
    Finset.le_sup (f := fun h' => if hc' : Child C g h' then height C h' + 1 else 0)
      (Finset.mem_univ h)
  rw [dif_pos hc] at hmem
  rw [height_eq C g]
  omega

/-- If `wire g h > 0` then `h` has strictly smaller height than `g`. -/
theorem height_lt_of_wire_pos {g h : C.Gate} (hw : 0 < C.wire g h) :
    height C h < height C g :=
  height_child_lt C hw

end Lax461425Proofs.RigidHeight
