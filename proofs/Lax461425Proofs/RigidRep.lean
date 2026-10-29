import Lax461425Proofs.RigidEquiv

/-!
Helper material for the rigidification proof: a canonical representative gate within each
equivalence class, chosen deterministically (but non-computably) via a bijection with `Fin n`.
-/

namespace Lax461425Proofs.RigidRep

open Lax461425.Circuits RigidHeight RigidEquiv

open scoped Classical

variable {V K : Type*} (C : Circuit V K)

/-- A fixed bijection of the (finite) gate set with `Fin n`, used only to pick out a canonical
representative inside each equivalence class. -/
noncomputable def indexEquiv : C.Gate ≃ Fin (Fintype.card C.Gate) := Fintype.equivFin C.Gate

/-- The canonical representative of the equivalence class of `g`: among all gates equivalent to
`g`, the one with least index under `indexEquiv`. -/
noncomputable def rep (g : C.Gate) : C.Gate :=
  (indexEquiv C).symm
    (((Finset.univ.filter (Equiv C g)).image (indexEquiv C)).min'
      (Finset.Nonempty.image ⟨g, by simp [equiv_refl C g]⟩ _))

/-- `rep g` is equivalent to `g`. -/
theorem rep_equiv (g : C.Gate) : Equiv C g (rep C g) := by
  set S := Finset.univ.filter (Equiv C g) with hS
  have hne : S.Nonempty := ⟨g, by simp [hS, equiv_refl C g]⟩
  have hmem : (S.image (indexEquiv C)).min' (hne.image _) ∈ S.image (indexEquiv C) :=
    Finset.min'_mem _ (hne.image _)
  obtain ⟨g', hg', hge⟩ := Finset.mem_image.mp hmem
  have : rep C g = g' := by
    unfold rep
    rw [← hge]
    simp
  rw [this]
  simpa [hS] using hg'

/-- Gates in the same equivalence class have the same representative. -/
theorem rep_eq_of_equiv {g g' : C.Gate} (h : Equiv C g g') : rep C g = rep C g' := by
  have hset : Finset.univ.filter (Equiv C g) = Finset.univ.filter (Equiv C g') := by
    apply Finset.filter_congr
    intro x _
    constructor
    · intro hx; exact equiv_trans C (equiv_symm C h) hx
    · intro hx; exact equiv_trans C h hx
  simp only [rep, hset]

/-- Conversely, gates with the same representative are equivalent. -/
theorem equiv_of_rep_eq {g g' : C.Gate} (h : rep C g = rep C g') : Equiv C g g' := by
  have h1 : Equiv C g (rep C g) := rep_equiv C g
  have h2 : Equiv C g' (rep C g') := rep_equiv C g'
  rw [h] at h1
  exact equiv_trans C h1 (equiv_symm C h2)

/-- `rep` is idempotent. -/
theorem rep_rep (g : C.Gate) : rep C (rep C g) = rep C g :=
  rep_eq_of_equiv C (equiv_symm C (rep_equiv C g))

end Lax461425Proofs.RigidRep
