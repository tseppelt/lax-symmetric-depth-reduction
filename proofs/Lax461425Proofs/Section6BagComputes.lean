import Lax461425Proofs.Section6BagSymmetry
import Lax461425Proofs.Section6LayeredPaths

/-!
Computation of the path-decomposition ABP: its paths are global vertex assignments,
and its edge-processing counts reproduce the multiplicities of the pattern.
-/

namespace Lax461425Proofs.Section6BagComputes

open Lax461425.SymmetricABPs Lax461425.HomomorphismPolynomials
open Section6BagProgram Section6BagSymmetry SymmetricPathAssignments
open scoped Classical

variable {F : Pattern} {k : ℕ} (D : Schedule F k) (n : ℕ) (hn : 1 ≤ n)
variable (K : Type*) [CommSemiring K]

theorem next_castSucc (i : Fin D.length) : next i.castSucc = i.succ := by
  apply Fin.ext
  dsimp [next]
  have := i.isLt
  omega

/-- A global vertex map determines a compatible trajectory of remembered bag images. -/
noncomputable def globalTrajectory (h : F.A ⊕ F.B → Fin n) :
    Section6LayeredPaths.Trajectory (program D n hn K) := by
  refine ⟨fun i => ⟨stateOfGlobal D n i h, stateOfGlobal_valid D n i h⟩, ?_⟩
  intro i
  have he := step_global D n i.castSucc h
  rw [next_castSucc] at he
  exact he

/-- Forget the option encoding and read the bag assignments of a trajectory. -/
noncomputable def trajectoryAssignments
    (a : Section6LayeredPaths.Trajectory (program D n hn K)) :
    CompatibleAssignments D.toPaddedPathDecomposition n := by
  refine ⟨fun i => assignmentOfState D n hn i (a.1 i), ?_⟩
  intro i v hi hj
  have he := a.2 i
  change Step D n i.castSucc (a.1 i.castSucc).val (a.1 i.succ).val at he
  unfold Step at he
  cases hh : D.process i.castSucc with
  | none =>
    rw [hh] at he
    have he' := he v hi (by simpa [next_castSucc] using hj)
    exact congrArg (fun s : Option (Fin n) => s.getD (defaultValue n hn)) he'
  | some e =>
    rw [hh] at he
    exact congrArg (fun s : State (F := F) n => (s v).getD (defaultValue n hn)) he

noncomputable def globalOfTrajectory
    (a : Section6LayeredPaths.Trajectory (program D n hn K)) : F.A ⊕ F.B → Fin n :=
  extend D.toPaddedPathDecomposition n (trajectoryAssignments D n hn K a)

theorem globalOf_globalTrajectory (h : F.A ⊕ F.B → Fin n) :
    globalOfTrajectory D n hn K (globalTrajectory D n hn K h) = h := by
  funext v
  obtain ⟨i, hi⟩ := D.covers_vertex v
  rw [globalOfTrajectory, extend_apply D.toPaddedPathDecomposition n _ i v hi]
  change (stateOfGlobal D n i h v).getD (defaultValue n hn) = h v
  simp [stateOfGlobal, hi]

theorem globalTrajectory_globalOf
    (a : Section6LayeredPaths.Trajectory (program D n hn K)) :
    globalTrajectory D n hn K (globalOfTrajectory D n hn K a) = a := by
  apply Subtype.ext
  funext i
  apply assignmentOfState_injective D n hn i
  funext v
  change (stateOfGlobal D n i (globalOfTrajectory D n hn K a) v.val).getD
      (defaultValue n hn) = ((a.1 i).val v.val).getD (defaultValue n hn)
  simp only [stateOfGlobal, v.property, ↓reduceIte, Option.getD_some]
  exact extend_apply D.toPaddedPathDecomposition n (trajectoryAssignments D n hn K a) i v.val v.property

/-- The literal paths of the bag ABP are in bijection with global vertex assignments. -/
noncomputable def globalPathEquiv : (F.A ⊕ F.B → Fin n) ≃ (abp D n hn K).Path :=
  ({ toFun := globalTrajectory D n hn K
     invFun := globalOfTrajectory D n hn K
     left_inv := globalOf_globalTrajectory D n hn K
     right_inv := globalTrajectory_globalOf D n hn K } :
    (F.A ⊕ F.B → Fin n) ≃ Section6LayeredPaths.Trajectory (program D n hn K)).trans
      (Section6LayeredPaths.trajectoryEquiv (program D n hn K))

noncomputable def localWeight (h : F.A ⊕ F.B → Fin n) (i : Fin (D.length + 1)) :
    MvPolynomial (Fin n × Fin n) K :=
  match D.process i with
  | none => 1
  | some (a, b) => MvPolynomial.X (h (Sum.inl a), h (Sum.inr b))

theorem edgeLabel_global (h : F.A ⊕ F.B → Fin n) (i : Fin (D.length + 1)) :
    (edgeLabel D n hn K i (stateOfGlobal D n i h)).polynomial = localWeight D n K h i := by
  cases he : D.process i with
  | none => simpa [localWeight, he] using edgeLabel_none D n hn K (s := stateOfGlobal D n i h) he
  | some e =>
    obtain ⟨a, b⟩ := e
    rw [edgeLabel_some D n hn K he]
    have hb := D.process_bag i a b he
    simp [localWeight, he, stateOfGlobal, hb.2.1, hb.2.2]

theorem pathWeight_global (h : F.A ⊕ F.B → Fin n) :
    (abp D n hn K).pathWeight (globalPathEquiv D n hn K h) =
      ∏ i : Fin D.length, localWeight D n K h i.castSucc := by
  change (∏ i : Fin D.length,
    (edgeLabel D n hn K i.castSucc (stateOfGlobal D n i.castSucc h)).polynomial) = _
  apply Finset.prod_congr rfl
  intro i hi
  exact edgeLabel_global D n hn K h i.castSucc

theorem product_localWeight (h : F.A ⊕ F.B → Fin n) :
    (∏ i : Fin D.length, localWeight D n K h i.castSucc) =
      ∏ a : F.A, ∏ b : F.B, MvPolynomial.X (h (Sum.inl a), h (Sum.inr b)) ^ F.mult a b := by
  let w : Option (F.A × F.B) → MvPolynomial (Fin n × Fin n) K :=
    fun e => match e with
      | none => 1
      | some (a, b) => MvPolynomial.X (h (Sum.inl a), h (Sum.inr b))
  have hprod : (∏ i : Fin D.length, localWeight D n K h i.castSucc) =
      ∏ i : Fin (D.length + 1), w (D.process i) := by
    rw [Fin.prod_univ_castSucc]
    simp [w, D.process_last, localWeight]
  rw [hprod, ← Finset.prod_fiberwise' Finset.univ D.process w]
  simp only [Finset.prod_const]
  rw [Fintype.prod_option]
  simp only [w, one_pow, one_mul]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro a ha
  apply Finset.prod_congr rfl
  intro b hb
  rw [D.process_count]

/-- The path-sum polynomial of the constructed ABP is the homomorphism polynomial. -/
theorem computes_hom : (abp D n hn K).Computes (hom K F n) := by
  classical
  have hsum : (∑ h : F.A ⊕ F.B → Fin n,
      ∏ a : F.A, ∏ b : F.B,
        MvPolynomial.X (h (Sum.inl a), h (Sum.inr b)) ^ F.mult a b) = hom K F n := by
    unfold hom
    calc
      _ = ∑ h : (F.A → Fin n) × (F.B → Fin n),
          ∏ a : F.A, ∏ b : F.B, MvPolynomial.X (h.1 a, h.2 b) ^ F.mult a b :=
        (Equiv.sumArrowEquivProdArrow F.A F.B (Fin n)).sum_comp
          (fun h => ∏ a : F.A, ∏ b : F.B, MvPolynomial.X (h.1 a, h.2 b) ^ F.mult a b)
      _ = _ := Fintype.sum_prod_type _
  rw [← hsum]
  apply SymmetricABPPaths.computes_of_pathEquiv (abp D n hn K) (globalPathEquiv D n hn K)
  intro h
  exact (pathWeight_global D n hn K h).trans (product_localWeight D n K h)

end Lax461425Proofs.Section6BagComputes
