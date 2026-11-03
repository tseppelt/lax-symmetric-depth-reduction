import Lax461425Proofs.Section6LayeredABP
import Lax461425Proofs.SymmetricABPPaths

/-!
Paths in a consecutive-layer ABP are exactly compatible state trajectories. This is a
theorem about the existing finite path-sum semantics, rather than a replacement semantics.
-/

namespace Lax461425Proofs.Section6LayeredPaths

open Lax461425.SymmetricABPs
open Section6LayeredABP SymmetricABPPaths

variable {V K : Type*} (P : Program V K)

def Compatible (a : ∀ i : Fin (P.length + 1), {s // P.valid i s}) : Prop :=
  ∀ i : Fin P.length, P.step i.castSucc (a i.castSucc).val (a i.succ).val

abbrev Trajectory := {a : ∀ i : Fin (P.length + 1), {s // P.valid i s} // Compatible P a}

def vertexAt (a : Trajectory P) (i : Fin (P.length + 1)) : (abp P).Vertex :=
  ⟨(i, (a.1 i).val), (a.1 i).property⟩

theorem vertexAt_source (a : Trajectory P) : vertexAt P a 0 = (abp P).source :=
  eq_source_of_zero P _ rfl

theorem vertexAt_sink (a : Trajectory P) :
    vertexAt P a (Fin.last P.length) = (abp P).sink := eq_sink_of_last P _ rfl

theorem vertexAt_edge (a : Trajectory P) (i : Fin P.length) :
    (abp P).edge (vertexAt P a i.castSucc) (vertexAt P a i.succ) :=
  ⟨rfl, a.2 i⟩

/-- A compatible trajectory gives an actual directed source-to-sink path. -/
def pathOfTrajectory (a : Trajectory P) : (abp P).Path :=
  ⟨⟨⟨P.length, walk_length_lt_card (abp P) (vertexAt P a) (vertexAt_edge P a)⟩,
    vertexAt P a⟩, vertexAt_source P a, vertexAt_sink P a, vertexAt_edge P a⟩

/-- A path's position equals the layer of its vertex. -/
theorem path_layer (p : (abp P).Path) (i : Fin (p.1.1.val + 1)) :
    (p.1.2 i).1.1.val = i.val := by
  refine Fin.induction ?_ (fun j ih => ?_) i
  · rw [p.2.1]
    rfl
  · have he := (p.2.2.2 j).1
    change (p.1.2 j.castSucc).1.1.val + 1 = (p.1.2 j.succ).1.1.val at he
    change (p.1.2 j.castSucc).1.1.val = j.val at ih
    change (p.1.2 j.succ).1.1.val = j.val + 1
    omega

theorem path_length (p : (abp P).Path) : p.1.1.val = P.length := by
  have h := path_layer P p (Fin.last p.1.1.val)
  rw [p.2.2.1] at h
  exact h.symm

/-- Read the state of a path at a specified layer. -/
def pathVertex (p : (abp P).Path) (i : Fin (P.length + 1)) : (abp P).Vertex :=
  p.1.2 ⟨i.val, by have hi := i.isLt; have hl := path_length P p; omega⟩

theorem pathVertex_layer (p : (abp P).Path) (i : Fin (P.length + 1)) :
    (pathVertex P p i).1.1 = i := by
  apply Fin.ext
  exact path_layer P p _

/-- Every source-to-sink path determines a compatible state trajectory. -/
def trajectoryOfPath (p : (abp P).Path) : Trajectory P := by
  let a : ∀ i : Fin (P.length + 1), {s // P.valid i s} :=
    fun i => ⟨(pathVertex P p i).1.2, by
      have h := (pathVertex P p i).2
      rwa [pathVertex_layer P p i] at h⟩
  refine ⟨a, ?_⟩
  intro i
  have hl := path_length P p
  have he := (p.2.2.2 ⟨i.val, by have := i.isLt; omega⟩).2
  change P.step (pathVertex P p i.castSucc).1.1
    (pathVertex P p i.castSucc).1.2 (pathVertex P p i.succ).1.2 at he
  rw [pathVertex_layer] at he
  exact he

theorem pathOf_trajectoryOf (p : (abp P).Path) :
    pathOfTrajectory P (trajectoryOfPath P p) = p := by
  apply path_ext (abp P) (path_length P p).symm
  intro i j hij
  apply Subtype.ext
  apply Prod.ext
  · change i = (p.1.2 j).1.1
    apply Fin.ext
    have h := path_layer P p j
    exact hij.trans h.symm
  · change (p.1.2 ⟨i.val, _⟩).1.2 = (p.1.2 j).1.2
    exact congrArg (fun r => (p.1.2 r).1.2) (Fin.ext hij)

theorem trajectoryOf_pathOf (a : Trajectory P) :
    trajectoryOfPath P (pathOfTrajectory P a) = a := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  rfl

/-- The precise path/trajectory bijection used by the bag ABP computation proof. -/
def trajectoryEquiv : Trajectory P ≃ (abp P).Path where
  toFun := pathOfTrajectory P
  invFun := trajectoryOfPath P
  left_inv := trajectoryOf_pathOf P
  right_inv := pathOf_trajectoryOf P

end Lax461425Proofs.Section6LayeredPaths
