import Lax461425Proofs.PatternFormulaBlocks

/-!
Explicit formula-tree automorphisms for the edge and selector blocks. Image pairs are
sorted after permutation, exchanging the two variable leaves when their order reverses.
-/

namespace Lax461425Proofs.PatternFormulaSymmetry

open Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies
open TreeFormulaCircuit TreeFormulaOperations TreeFormulaIsomorphism ComputedFormula PatternFormulaBlocks
open scoped Classical

variable {K : Type*} [Field K] {n : ℕ}

/-- The joint action carries a triple-product term to its reindexed term. -/
noncomputable def termIso (γ : Γ n) (a b i j : Fin n) :
    Iso (jointAction (auxAction n) γ) (term (K := K) n a b i j).tree
      (term n a b (γ.1 i) (γ.2 j)).tree := by
  unfold term
  exact mulIso _ _ _ _ _
    (mulIso _ _ _ _ _ (varIso _ _) (varIso _ _)) (varIso _ _)

/-- Reindexing both matrix coordinates extends to an edge-factor automorphism. -/
noncomputable def edgeIso (γ : Γ n) (a b : Fin n) :
    Iso (jointAction (auxAction n) γ) (edge (K := K) n a b).tree (edge n a b).tree :=
  joinIso _ (fun p : Fin n × Fin n => (term n a b p.1 p.2).tree)
    (fun p : Fin n × Fin n => (term n a b p.1 p.2).tree)
    (Equiv.prodCongr γ.1 γ.2) (fun p => termIso γ a b p.1 p.2) false

/-- Pair factors transform with the corresponding unordered pair of images. -/
noncomputable def pairFactorIso (γ : Γ n) (v : Vertex n) (p : ImagePair n) :
    Iso (jointAction (auxAction n) γ) (pairFactor (K := K) n v p).tree
      (pairFactor n v (pairPerm (indexPerm γ v) p)).tree := by
  unfold pairFactor
  refine addIso _ _ _ _ _ (constIso _ _) (mulIso _ _ _ _ _ (constIso _ _) ?_)
  change Iso (jointAction (auxAction n) γ) _ (mul
    (var (K := K) (V := Variables n)
      (Sum.inr (v, min (indexPerm γ v p.val.1) (indexPerm γ v p.val.2))))
    (var (Sum.inr (v, max (indexPerm γ v p.val.1) (indexPerm γ v p.val.2))))).tree
  by_cases h : indexPerm γ v p.val.1 ≤ indexPerm γ v p.val.2
  · simp only [min_eq_left h, max_eq_right h]
    exact mulIso _ _ _ _ _ (varIso _ _) (varIso _ _)
  · simp only [min_eq_right (le_of_not_ge h), max_eq_left (le_of_not_ge h)]
    unfold ComputedFormula.mul
    apply joinIso _ _ _ (Equiv.swap true false) ?_ true
    intro b
    cases b <;> exact varIso _ _

/-- Image reindexing extends to an exactly-one selector automorphism. -/
noncomputable def selectorIso (γ : Γ n) (v : Vertex n) :
    Iso (jointAction (auxAction n) γ) (selector (K := K) n v).tree (selector n v).tree := by
  unfold selector
  apply mulIso
  · exact joinIso (jointAction (auxAction n) γ)
      (fun i : Fin n => (var (K := K) (V := Variables n) (.inr (v, i))).tree)
      (fun i : Fin n => (var (K := K) (V := Variables n) (.inr (v, i))).tree)
      (indexPerm γ v) (fun i => varIso _ _) false
  · exact joinIso _ (fun p : ImagePair n => (pairFactor n v p).tree)
      (fun p : ImagePair n => (pairFactor n v p).tree)
      (pairPerm (indexPerm γ v)) (fun p => pairFactorIso γ v p) true

/-- Inverse tags are compatible with every variable renaming. -/
noncomputable def tagIso {V : Type*} (π : V → V) (t : K) (F F' : Formula V K)
    (h : Iso π F.tree F'.tree) : Iso π (tag t F).tree (tag t F').tree := by
  unfold tag
  exact mulIso _ _ _ _ _ (constIso _ _)
    (mulIso _ _ _ _ _ (constIso _ _) h)

end Lax461425Proofs.PatternFormulaSymmetry
