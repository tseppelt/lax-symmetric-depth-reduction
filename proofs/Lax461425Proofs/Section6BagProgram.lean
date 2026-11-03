import Lax461425Proofs.Section6LayeredABP
import Lax461425Proofs.SymmetricPathAssignments

/-!
The actual assignment-state ABP associated to a path decomposition with edge-processing
layers. Transitions may introduce and forget several vertices at once: agreement on the
bag intersection suffices, and never increases the state bound.
-/

namespace Lax461425Proofs.Section6BagProgram

open Lax461425.SymmetricABPs Lax461425.HomomorphismPolynomials
open SymmetricPathAssignments
open scoped Classical

def next {l : ℕ} (i : Fin (l + 1)) : Fin (l + 1) :=
  ⟨min (i.val + 1) l, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- A path decomposition augmented by single-edge processing steps. The count condition
records parallel edges separately; a step without an edge only joins assignments. -/
structure Schedule (F : Pattern) (k : ℕ) extends PathDecomposition F k where
  process : Fin (length + 1) → Option (F.A × F.B)
  process_last : process (Fin.last length) = none
  process_bag : ∀ i a b, process i = some (a, b) →
    bag i = bag (next i) ∧ Sum.inl a ∈ bag i ∧ Sum.inr b ∈ bag i
  process_count : ∀ a b, (Finset.univ.filter fun i => process i = some (a, b)).card = F.mult a b

variable {F : Pattern} {k : ℕ} (D : Schedule F k) (n : ℕ)

abbrev State := F.A ⊕ F.B → Option (Fin n)

def Valid (i : Fin (D.length + 1)) (s : State (F := F) n) : Prop :=
  ∀ v, (s v).isSome = true ↔ v ∈ D.bag i

noncomputable def stateOfGlobal (i : Fin (D.length + 1)) (h : F.A ⊕ F.B → Fin n) :
    State (F := F) n := fun v => if v ∈ D.bag i then some (h v) else none

theorem stateOfGlobal_valid (i : Fin (D.length + 1)) (h : F.A ⊕ F.B → Fin n) :
    Valid D n i (stateOfGlobal D n i h) := by
  classical
  intro v
  simp [stateOfGlobal]

variable (hn : 1 ≤ n)

def defaultValue : Fin n := ⟨0, by omega⟩

def globalOfState (s : State (F := F) n) : F.A ⊕ F.B → Fin n :=
  fun v => (s v).getD (defaultValue n hn)

theorem stateOfGlobal_globalOfState (i : Fin (D.length + 1)) (s : State (F := F) n)
    (hs : Valid D n i s) : stateOfGlobal D n i (globalOfState n hn s) = s := by
  classical
  funext v
  have hv := hs v
  unfold stateOfGlobal globalOfState
  cases h : s v with
  | none => simp [h] at hv; simp [hv, h]
  | some a => simp [h] at hv; simp [hv, h]

def Step (i : Fin (D.length + 1)) (s t : State (F := F) n) : Prop :=
  match D.process i with
  | some _ => s = t
  | none => ∀ v, v ∈ D.bag i → v ∈ D.bag (next i) → s v = t v

theorem step_global (i : Fin (D.length + 1)) (h : F.A ⊕ F.B → Fin n) :
    Step D n i (stateOfGlobal D n i h) (stateOfGlobal D n (next i) h) := by
  classical
  unfold Step
  cases he : D.process i with
  | none =>
    intro v hi hj
    simp [stateOfGlobal, hi, hj]
  | some e =>
    obtain ⟨a, b⟩ := e
    have hb := (D.process_bag i a b he).1
    funext v
    simp [stateOfGlobal, hb]

noncomputable def edgeLabel (K : Type*) [CommSemiring K]
    (i : Fin (D.length + 1)) (s : State (F := F) n) :
    AffineForm (Fin n × Fin n) K := by
  classical
  exact match D.process i with
    | none => ⟨1, fun _ => 0⟩
    | some (a, b) => ⟨0, fun x =>
        if x = ((s (Sum.inl a)).getD (defaultValue n hn),
          (s (Sum.inr b)).getD (defaultValue n hn)) then 1 else 0⟩

/-- The path-decomposition states and transitions define a literal affine ABP. -/
noncomputable abbrev program (K : Type*) [CommSemiring K] :
    Section6LayeredABP.Program (Fin n × Fin n) K := by
  classical
  refine {
    length := D.length
    State := State (F := F) n
    valid := Valid D n
    start := fun _ => none
    finish := fun _ => none
    valid_start := ?_
    valid_finish := ?_
    first_unique := ?_
    last_unique := ?_
    step := Step D n
    label := fun i s _ => edgeLabel D n hn K i s
    predecessor := ?_
    successor := ?_ }
  · intro v; simp [Valid, D.bag_first]
  · intro v; simp [Valid, D.bag_last]
  · intro s hs
    funext v
    have hv := hs v
    rw [D.bag_first] at hv
    cases h : s v <;> simp_all
  · intro s hs
    funext v
    have hv := hs v
    rw [D.bag_last] at hv
    cases h : s v <;> simp_all
  · intro i s hs hi
    let j : Fin (D.length + 1) := ⟨i.val - 1, by omega⟩
    have hj : j.val + 1 = i.val := by dsimp [j]; omega
    have hnext : next j = i := by apply Fin.ext; dsimp [next, j]; have := i.isLt; omega
    let h := globalOfState n hn s
    refine ⟨j, stateOfGlobal D n j h, hj, stateOfGlobal_valid D n j h, ?_⟩
    have he := step_global D n j h
    rw [hnext, stateOfGlobal_globalOfState D n hn i s hs] at he
    exact he
  · intro i s hs hi
    let j : Fin (D.length + 1) := ⟨i.val + 1, by omega⟩
    have hj : i.val + 1 = j.val := rfl
    have hnext : next i = j := by apply Fin.ext; dsimp [next, j]; omega
    let h := globalOfState n hn s
    refine ⟨j, stateOfGlobal D n j h, hj, stateOfGlobal_valid D n j h, ?_⟩
    have he := step_global D n i h
    rw [hnext, stateOfGlobal_globalOfState D n hn i s hs] at he
    exact he

noncomputable abbrev abp (K : Type*) [CommSemiring K] : ABP (Fin n × Fin n) K :=
  Section6LayeredABP.abp (program D n hn K)

/-- Read the images remembered by an admissible state on its bag. -/
def assignmentOfState (i : Fin (D.length + 1)) (s : {s // Valid D n i s}) :
    BagAssignment D.toPathDecomposition n i :=
  fun v => (s.1 v.val).getD (defaultValue n hn)

theorem assignmentOfState_injective (i : Fin (D.length + 1)) :
    Function.Injective (assignmentOfState D n hn i) := by
  intro s t hst
  apply Subtype.ext
  funext v
  have hs := s.2 v
  have ht := t.2 v
  by_cases hv : v ∈ D.bag i
  · have hs' := hs.mpr hv
    have ht' := ht.mpr hv
    have hval := congrFun hst ⟨v, hv⟩
    change (s.1 v).getD (defaultValue n hn) = (t.1 v).getD (defaultValue n hn) at hval
    cases hS : s.1 v <;> cases hT : t.1 v <;> simp_all
  · cases hS : s.1 v <;> cases hT : t.1 v <;> simp_all

/-- The precise state bound of Section 6, independent of the number of layers. -/
theorem card_valid_le (hn : 1 ≤ n) (i : Fin (D.length + 1)) :
    Fintype.card {s // Valid D n i s} ≤ n ^ (k + 1) := by
  classical
  exact (Fintype.card_le_of_injective _ (assignmentOfState_injective D n hn i)).trans
    (card_bagAssignment_le D.toPathDecomposition n hn i)

/-- The orbit bound quantifies over every extending automorphism, including those not
provided by the obvious row/column action on assignments. -/
theorem orbitSize_le (K : Type*) [CommSemiring K] :
    (abp D n hn K).orbitSize ≤ n ^ (k + 1) :=
  Section6LayeredABP.orbitSize_le (program D n hn K) _ (card_valid_le D n hn)

end Lax461425Proofs.Section6BagProgram
