import Lax461425.ReducedRigid

namespace Lax461425Proofs.ReducedRigid

open Lax461425.Circuits Lax461425.MatrixSymmetry

variable {K : Type*} {n : ℕ} {C : Circuit (Fin n × Fin n) K}

/-- The relation "`h` is a child of `g`", i.e. there is a wire from `h` into `g`. -/
private def Child (g h : C.Gate) : Prop := 0 < C.wire g h

private instance : Std.Irrefl (Relation.TransGen fun (h g : C.Gate) => Child g h) :=
  ⟨C.acyclic⟩

/-- The direct child relation is well-founded: a finite acyclic relation has no infinite
descending chain. -/
private theorem wellFounded_child : WellFounded fun (h g : C.Gate) => Child g h := by
  have hsub : Subrelation (fun (h g : C.Gate) => Child g h)
      (Relation.TransGen fun (h g : C.Gate) => Child g h) :=
    fun hc => Relation.TransGen.single hc
  exact Subrelation.wf hsub (Finite.wellFounded_of_trans_of_irrefl _)

/-- If `σ₁` and `σ₂` both extend the same renaming `π`, their "difference"
`σ₂.symm.trans σ₁` preserves every gate's label and every wire multiplicity literally
(not merely up to `π`). -/
private theorem label_and_wire_eq {π : Fin n × Fin n → Fin n × Fin n} {σ₁ σ₂ : C.Gate ≃ C.Gate}
    (h₁ : Extends C σ₁ π) (h₂ : Extends C σ₂ π) (g' h' : C.Gate) :
    C.label ((σ₂.symm.trans σ₁) g') = C.label g' ∧
      C.wire ((σ₂.symm.trans σ₁) g') ((σ₂.symm.trans σ₁) h') = C.wire g' h' := by
  obtain ⟨g, rfl⟩ := σ₂.surjective g'
  obtain ⟨h, rfl⟩ := σ₂.surjective h'
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  exact ⟨(h₁.1 g).trans (h₂.1 g).symm, (h₁.2 g h).trans (h₂.2 g h).symm⟩

/-- The circuit automorphism "connecting" two automorphisms that extend the same renaming
fixes every gate, by induction on the child relation. -/
private theorem eq_of_extends_same (hred : C.IsReduced) {π : Fin n × Fin n → Fin n × Fin n}
    {σ₁ σ₂ : C.Gate ≃ C.Gate} (h₁ : Extends C σ₁ π) (h₂ : Extends C σ₂ π) (g' : C.Gate) :
    (σ₂.symm.trans σ₁) g' = g' := by
  induction g' using wellFounded_child.induction with
  | _ g' ih =>
    set ρ : C.Gate ≃ C.Gate := σ₂.symm.trans σ₁ with hρ
    have hlabel : ∀ x, C.label (ρ x) = C.label x := fun x => (label_and_wire_eq h₁ h₂ x x).1
    have hwire : ∀ x y, C.wire (ρ x) (ρ y) = C.wire x y := fun x y =>
      (label_and_wire_eq h₁ h₂ x y).2
    by_cases hinput : (C.label g').IsInput
    · exact hred.1 (ρ g') g' (hlabel g' ▸ hinput) (hlabel g')
    · refine (hred.2 g' (ρ g') hinput (hlabel g').symm ?_).symm
      funext h'
      have hstep : C.wire (ρ g') h' = C.wire g' (ρ.symm h') := by
        have := hwire g' (ρ.symm h')
        rwa [Equiv.apply_symm_apply] at this
      rw [hstep]
      by_cases hchild : Child g' h'
      · have hfix : ρ h' = h' := ih h' hchild
        have hsymm : ρ.symm h' = h' := by
          conv_lhs => rw [← hfix]
          exact ρ.symm_apply_apply h'
        rw [hsymm]
      · have hw0 : C.wire g' h' = 0 := Nat.eq_zero_of_not_pos hchild
        rw [hw0]
        by_contra hcontra
        have hpos : Child g' (ρ.symm h') := Nat.pos_of_ne_zero (Ne.symm hcontra)
        have hfix : ρ (ρ.symm h') = ρ.symm h' := ih (ρ.symm h') hpos
        rw [Equiv.apply_symm_apply] at hfix
        rw [← hfix] at hpos
        exact hchild hpos

/--
---
conclusion: Lax461425.ReducedRigid.isRigid
---
Two circuit automorphisms extending the same element of `Γₙ` differ by an automorphism fixing
every input gate, since input labels are distinct; by induction on the child relation this
automorphism fixes every gate, using that `C` is reduced.
-/
theorem isRigid (hsym : IsMatrixSymmetric C) (hred : C.IsReduced) : IsRigid C := by
  intro γ
  obtain ⟨σ, hσ⟩ := hsym γ
  refine ⟨σ, hσ, fun σ' hσ' => ?_⟩
  have h := eq_of_extends_same hred hσ' hσ
  exact Equiv.ext fun x => by
    have hx := h (σ x)
    simpa using hx

end Lax461425Proofs.ReducedRigid
