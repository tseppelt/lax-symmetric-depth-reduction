import Lax461425.CircuitProperties
import Lax461425Proofs.TreeInputProperties
import Lax461425Proofs.TaggedPatternFormula

open Lax461425.CircuitProperties

/-!
The concrete Boolean-witness formulas have private input occurrences and no equal-labelled
input siblings. Identifying inputs therefore keeps every wire simple and preserves the
formula structure required by the paper.
-/

namespace Lax461425Proofs.PatternFormulaInputs

open Lax461425.Circuits TreeFormulaCircuit TreeFormulaOperations ComputedFormula
open TreeInputProperties PatternFormulaBlocks TaggedPatternFormula
open scoped Classical

variable {K : Type*} [Field K]

theorem term_siblings (n : ℕ) (a b i j : Fin n) :
    (InputSiblingsDistinct (circuit (term (K := K) n a b i j).tree)) := by
  unfold term
  apply siblings_mul
  · apply siblings_mul _ _ (siblings_var _) (siblings_var _)
    intro h₁ h₂ heq
    simp [ComputedFormula.var, varInput] at heq
  · exact siblings_var _
  · intro h₁ h₂
    exact False.elim (root_noninput_mul _ _ h₁)

theorem edge_siblings (n : ℕ) (a b : Fin n) :
    (InputSiblingsDistinct (circuit (edge (K := K) n a b).tree)) := by
  unfold edge
  apply siblings_op_of_noninput
  · intro p
    exact term_siblings n a b p.1 p.2
  · intro p
    exact root_noninput_mul _ _

theorem pairFactor_siblings (n : ℕ) (v : Vertex n) (p : ImagePair n) :
    (InputSiblingsDistinct (circuit (pairFactor (K := K) n v p).tree)) := by
  unfold pairFactor
  apply siblings_add _ _ (siblings_const 1)
  · apply siblings_mul_const _ _
    · apply siblings_mul _ _ (siblings_var _) (siblings_var _)
      intro h₁ h₂ heq
      apply p.property.ne
      have hv : (Sum.inr (v, p.val.1) : Variables n) = Sum.inr (v, p.val.2) :=
        GateLabel.var.inj heq
      exact congrArg Prod.snd (Sum.inr.inj hv)
    · exact root_noninput_mul _ _
  · intro h₁ h₂
    exact False.elim (root_noninput_mul _ _ h₂)

theorem selector_siblings (n : ℕ) (v : Vertex n) :
    (InputSiblingsDistinct (circuit (selector (K := K) n v).tree)) := by
  unfold selector
  apply siblings_mul
  · apply siblings_join
    · intro i
      exact siblings_var _
    · intro i j hi hj heq
      have hv : (Sum.inr (v, i) : Variables n) = Sum.inr (v, j) := GateLabel.var.inj heq
      exact congrArg Prod.snd (Sum.inr.inj hv)
  · apply siblings_op_of_noninput
    · intro p
      exact pairFactor_siblings n v p
    · intro p
      exact root_noninput_add _ _
  · intro h₁ h₂
    exact False.elim (root_noninput_op false _ h₁)

theorem block_siblings {n : ℕ} (m : Fin n → Fin n → ℕ) (b : BlockIndex m) :
    (InputSiblingsDistinct (circuit (block (K := K) m b).tree)) := by
  cases b with
  | inl v => exact selector_siblings n v
  | inr e => exact edge_siblings n e.1 e.2.1

theorem block_root_noninput {n : ℕ} (m : Fin n → Fin n → ℕ) (b : BlockIndex m) :
    ¬ ((block (K := K) m b).tree.label (block m b).tree.out).IsInput := by
  cases b with
  | inl v => exact root_noninput_mul _ _
  | inr e => exact root_noninput_op false _

theorem pattern_siblings {n : ℕ} (m : Fin n → Fin n → ℕ) (t : BlockIndex m → K) :
    (InputSiblingsDistinct (circuit (patternFormula m t).tree)) := by
  unfold patternFormula
  apply siblings_op_of_noninput
  · intro b
    exact siblings_tag (t b) (block m b) (block_siblings m b) (block_root_noninput m b)
  · intro b
    exact root_noninput_tag _ _

theorem combination_siblings {n : ℕ} {R : Type} [Fintype R]
    (c : R → K) (m : R → Fin n → Fin n → ℕ) (t : ∀ r, BlockIndex (m r) → K) (s : R → K) :
    (InputSiblingsDistinct (circuit (combinationFormula c m t s).tree)) := by
  unfold combinationFormula
  apply siblings_op_of_noninput
  · intro r
    apply siblings_tag
    · exact siblings_mul_const (c r) (patternFormula (m r) (t r))
        (pattern_siblings _ _) (root_noninput_op true _)
    · exact root_noninput_mul _ _
  · intro r
    exact root_noninput_tag _ _

theorem combination_privateInputs {n : ℕ} {R : Type} [Fintype R]
    (c : R → K) (m : R → Fin n → Fin n → ℕ) (t : ∀ r, BlockIndex (m r) → K) (s : R → K) :
    (PrivateInputs (circuit (combinationFormula c m t s).tree)) :=
  privateInputs _ (root_noninput_op false _)

end Lax461425Proofs.PatternFormulaInputs
