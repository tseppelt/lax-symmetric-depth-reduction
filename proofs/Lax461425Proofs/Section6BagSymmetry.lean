import Lax461425Proofs.Section6BagProgram

/-!
The assignment-state ABP is matrix symmetric. The orbit bound is established separately
for all automorphisms in `Section6BagProgram`, rather than inferred from this action.
-/

namespace Lax461425Proofs.Section6BagSymmetry

open Lax461425.SymmetricABPs Lax461425.HomomorphismPolynomials Lax461425.MatrixSymmetry
open Section6BagProgram

variable {F : Pattern} {k : ℕ} (D : Schedule F k) (n : ℕ) (hn : 1 ≤ n)
variable (K : Type*) [CommSemiring K]

def imagePerm (γ : Γ n) : F.A ⊕ F.B → Equiv.Perm (Fin n)
  | .inl _ => γ.1
  | .inr _ => γ.2

def statePerm (γ : Γ n) : Equiv.Perm (State (F := F) n) :=
  Equiv.piCongrRight fun v => Equiv.optionCongr (imagePerm (F := F) n γ v)

@[simp] theorem statePerm_apply (γ : Γ n) (s : State (F := F) n) (v : F.A ⊕ F.B) :
    statePerm (F := F) n γ s v = (s v).map (imagePerm (F := F) n γ v) := by
  unfold statePerm; rfl

theorem valid_statePerm (γ : Γ n) (i : Fin (D.length + 1)) (s : State (F := F) n) :
    Valid D n i (statePerm (F := F) n γ s) ↔ Valid D n i s := by
  simp only [Valid, statePerm_apply, Option.isSome_map]

theorem step_statePerm (γ : Γ n) (i : Fin (D.length + 1)) (s t : State (F := F) n) :
    Step D n i (statePerm (F := F) n γ s) (statePerm (F := F) n γ t) ↔ Step D n i s t := by
  unfold Step
  cases he : D.process i with
  | some e => exact (statePerm (F := F) n γ).injective.eq_iff
  | none =>
    constructor
    · intro h v hi hj
      have hv := h v hi hj
      have hinj := (Equiv.optionCongr (imagePerm (F := F) n γ v)).injective
      exact hinj hv
    · intro h v hi hj
      simp only [statePerm_apply, h v hi hj]

noncomputable def vertexPerm (γ : Γ n) :
    Equiv.Perm (abp D n hn K).Vertex where
  toFun v := ⟨(v.1.1, statePerm (F := F) n γ v.1.2),
    (valid_statePerm D n γ v.1.1 v.1.2).2 v.2⟩
  invFun v := ⟨(v.1.1, (statePerm (F := F) n γ).symm v.1.2), by
    have h := valid_statePerm D n γ v.1.1 ((statePerm (F := F) n γ).symm v.1.2)
    apply h.mp
    rw [(statePerm (F := F) n γ).apply_symm_apply]
    exact v.2⟩
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Equiv.symm_apply_apply _ _
  right_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Equiv.apply_symm_apply _ _

theorem edgeLabel_none {i : Fin (D.length + 1)} {s : State (F := F) n}
    (he : D.process i = none) : (edgeLabel D n hn K i s).polynomial = 1 := by
  classical
  simp [edgeLabel, he, AffineForm.polynomial]

theorem edgeLabel_some {i : Fin (D.length + 1)} {s : State (F := F) n} {a : F.A} {b : F.B}
    (he : D.process i = some (a, b)) :
    (edgeLabel D n hn K i s).polynomial =
      MvPolynomial.X ((s (Sum.inl a)).getD (defaultValue n hn),
        (s (Sum.inr b)).getD (defaultValue n hn)) := by
  classical
  simp [edgeLabel, he, AffineForm.polynomial]

theorem label_rename (γ : Γ n) (i : Fin (D.length + 1)) (s : State (F := F) n)
    (hs : Valid D n i s) :
    (edgeLabel D n hn K i (statePerm (F := F) n γ s)).polynomial =
      MvPolynomial.rename (actVar γ) (edgeLabel D n hn K i s).polynomial := by
  cases he : D.process i with
  | none => rw [edgeLabel_none D n hn K he, edgeLabel_none D n hn K he, map_one]
  | some e =>
    obtain ⟨a, b⟩ := e
    have hbag := D.process_bag i a b he
    have ha := (hs (Sum.inl a)).mpr hbag.2.1
    have hb := (hs (Sum.inr b)).mpr hbag.2.2
    rw [edgeLabel_some D n hn K he, edgeLabel_some D n hn K he, MvPolynomial.rename_X]
    cases hA : s (Sum.inl a) <;> cases hB : s (Sum.inr b) <;>
      simp_all [statePerm_apply, imagePerm, actVar]

/-- The natural action on remembered images extends each matrix permutation. -/
theorem vertexPerm_extends (γ : Γ n) :
    (abp D n hn K).Extends (vertexPerm D n hn K γ) (actVar γ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext v
      simp [vertexPerm, Section6LayeredABP.source, statePerm_apply]
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext v
      simp [vertexPerm, Section6LayeredABP.sink, statePerm_apply]
  · intro u v
    change (u.1.1.val + 1 = v.1.1.val ∧
      Step D n u.1.1 (statePerm (F := F) n γ u.1.2) (statePerm (F := F) n γ v.1.2)) ↔
      (u.1.1.val + 1 = v.1.1.val ∧ Step D n u.1.1 u.1.2 v.1.2)
    exact and_congr Iff.rfl (step_statePerm D n γ u.1.1 u.1.2 v.1.2)
  · intro u v huv
    exact label_rename D n hn K γ u.1.1 u.1.2 u.2

theorem isMatrixSymmetric : (abp D n hn K).IsMatrixSymmetric :=
  fun γ => ⟨vertexPerm D n hn K γ, vertexPerm_extends D n hn K γ⟩

end Lax461425Proofs.Section6BagSymmetry
