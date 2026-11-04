import Lax461425.CircuitProperties
import Lax461425.CircuitReindex
import Lax461425.InputSharing
import Mathlib.Algebra.MvPolynomial.Rename

open Lax461425.CircuitProperties

/-! Semantics, formula shape and all-automorphism orbits under variable reindexing. -/

namespace Lax461425Proofs.CircuitReindex

open Lax461425.CircuitReindex Lax461425.Circuits Lax461425.MatrixSymmetry
open Lax461425.SymmetricFamilies
open scoped Classical

variable {G V W K : Type*} [Group G]

@[simp] theorem mapLabel_isInput (e : V ≃ W) (l : GateLabel V K) :
    (mapLabel e l).IsInput ↔ l.IsInput := by cases l <;> rfl

theorem mapLabel_injective (e : V ≃ W) :
    Function.Injective (mapLabel (K := K) e) := by
  intro l m h
  cases l <;> cases m <;> simp_all [mapLabel, e.injective.eq_iff]

theorem mapLabel_action (e : V ≃ W) (ρ : G →* Equiv.Perm V) (γ : G)
    (l : GateLabel V K) :
    mapLabel e (l.map (ρ γ)) = (mapLabel e l).map (action e ρ γ) := by
  cases l <;> simp [mapLabel, GateLabel.map, action]

theorem computesAt [CommSemiring K] (e : V ≃ W) (C : Circuit V K)
    {g : C.Gate} {p : MvPolynomial V K} (hp : C.ComputesAt g p) :
    (rename e C).ComputesAt g (MvPolynomial.rename e p) := by
  induction hp with
  | var hl =>
    rw [MvPolynomial.rename_X]
    apply Circuit.ComputesAt.var
    change mapLabel e (C.label _) = _
    rw [hl]
    rfl
  | const hl =>
    rw [MvPolynomial.rename_C]
    apply Circuit.ComputesAt.const
    change mapLabel e (C.label _) = _
    rw [hl]
    rfl
  | add q hl hq ih =>
    simp only [map_sum, map_nsmul]
    apply Circuit.ComputesAt.add
    · change mapLabel e (C.label _) = _
      rw [hl]
      rfl
    · exact ih
  | mul q hl hq ih =>
    simp only [map_prod, map_pow]
    apply Circuit.ComputesAt.mul
    · change mapLabel e (C.label _) = _
      rw [hl]
      rfl
    · exact ih

theorem computes [CommSemiring K] (e : V ≃ W) (C : Circuit V K)
    {p : MvPolynomial V K} (hp : C.Computes p) :
    (rename e C).Computes (MvPolynomial.rename e p) := computesAt e C hp

theorem isFormula (e : V ≃ W) (C : Circuit V K) (hC : (IsFormula C)) :
    (IsFormula (rename e C)) := by
  refine ⟨hC.1, ?_⟩
  intro g hg
  apply hC.2 g
  simpa only [rename, mapLabel_isInput] using hg

theorem inputsIdentified (e : V ≃ W) (C : Circuit V K) (hC : (InputsIdentified C)) :
    (InputsIdentified (rename e C)) := by
  intro g h hg he
  apply hC g h
  · exact (mapLabel_isInput e (C.label g)).mp hg
  · exact mapLabel_injective e he

theorem isSkew (e : V ≃ W) (C : Circuit V K) (hC : (IsSkew C)) :
    (IsSkew (rename e C)) := by
  intro g hg
  have hm : C.label g = .mul := by
    apply mapLabel_injective e
    exact hg
  have hs : (∑ h, if ((rename e C).label h).IsInput then 0 else
      (rename e C).wire g h) =
      ∑ h, if (C.label h).IsInput then 0 else C.wire g h := by
    apply Finset.sum_congr rfl
    intro h _
    by_cases hi : (C.label h).IsInput <;> simp [rename, mapLabel_isInput, hi]
  rw [hs]
  exact hC g hm

/-- Reindexing gives a correspondence of every extending automorphism, in both directions. -/
theorem extends_iff (e : V ≃ W) (ρ : G →* Equiv.Perm V) (C : Circuit V K)
    (γ : G) (σ : C.Gate ≃ C.Gate) :
    Extends (rename e C) σ (action e ρ γ) ↔ Extends C σ (ρ γ) := by
  constructor
  · rintro ⟨hl, hw⟩
    refine ⟨?_, hw⟩
    intro g
    apply mapLabel_injective e
    exact (hl g).trans (mapLabel_action e ρ γ (C.label g)).symm
  · rintro ⟨hl, hw⟩
    refine ⟨?_, hw⟩
    intro g
    change mapLabel e (C.label (σ g)) = _
    rw [hl g]
    exact mapLabel_action e ρ γ (C.label g)

theorem symmetric (e : V ≃ W) (ρ : G →* Equiv.Perm V) (C : Circuit V K)
    (hC : Symmetric ρ C) : Symmetric (action e ρ) (rename e C) := by
  intro γ
  obtain ⟨σ, hσ⟩ := hC γ
  exact ⟨σ, (extends_iff e ρ C γ σ).2 hσ⟩

theorem orbit_eq (e : V ≃ W) (ρ : G →* Equiv.Perm V) (C : Circuit V K) (g : C.Gate) :
    orbit (action e ρ) (rename e C) g = orbit ρ C g := by
  ext h
  constructor
  · rintro ⟨γ, σ, hσ, he⟩
    exact ⟨γ, σ, (extends_iff e ρ C γ σ).1 hσ, he⟩
  · rintro ⟨γ, σ, hσ, he⟩
    exact ⟨γ, σ, (extends_iff e ρ C γ σ).2 hσ, he⟩

theorem orbitSize_eq (e : V ≃ W) (ρ : G →* Equiv.Perm V) (C : Circuit V K) :
    orbitSize (action e ρ) (rename e C) = orbitSize ρ C := by
  unfold Lax461425.SymmetricFamilies.orbitSize
  congr 1
  funext g
  exact congrArg Set.ncard (orbit_eq e ρ C g)

/-- Transporting only the auxiliary names conjugates only the auxiliary action. -/
theorem action_joint {n : ℕ} {Y Z : Type*} (e : Y ≃ Z) (ρ : Γ n →* Equiv.Perm Y) :
    action (Equiv.sumCongr (Equiv.refl (Fin n × Fin n)) e) (jointAction ρ) =
      jointAction (action e ρ) := by
  ext γ v
  cases v <;> simp [action, jointAction, matrixAction]

end Lax461425Proofs.CircuitReindex
