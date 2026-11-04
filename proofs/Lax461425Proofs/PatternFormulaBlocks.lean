import Lax461425Proofs.ComputedFormula
import Lax461425Proofs.TreeFormulaIsomorphism
import Lax461425Proofs.PatternBooleanWitness

/-!
Concrete finite private-leaf formula blocks for Section 7.1. The exactly-one selector
uses precisely the paper's pairs `i < j`, each occurring once.
-/

namespace Lax461425Proofs.PatternFormulaBlocks

open Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies
open TreeFormulaCircuit TreeFormulaOperations TreeFormulaIsomorphism ComputedFormula
open scoped Classical

variable {K : Type*} [Field K]

abbrev Vertex (n : ℕ) := Fin n ⊕ Fin n
abbrev Aux (n : ℕ) := Vertex n × Fin n
abbrev Variables (n : ℕ) := (Fin n × Fin n) ⊕ Aux n
abbrev ImagePair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- Matrix row or column permutation at a fixed pattern vertex. -/
def indexPerm {n : ℕ} (γ : Γ n) (v : Vertex n) : Equiv.Perm (Fin n) :=
  v.elim (fun _ => γ.1) (fun _ => γ.2)

/-- The auxiliary action fixes the pattern vertex and permutes its potential images. -/
def auxAction (n : ℕ) : Γ n →* Equiv.Perm (Aux n) where
  toFun γ :=
    { toFun := fun p => (p.1, indexPerm γ p.1 p.2)
      invFun := fun p => (p.1, (indexPerm γ p.1).symm p.2)
      left_inv := by intro p; rcases p with ⟨v, i⟩; simp
      right_inv := by intro p; rcases p with ⟨v, i⟩; simp }
  map_one' := by
    apply Equiv.ext
    intro p
    rcases p with ⟨v, i⟩
    cases v <;> rfl
  map_mul' γ δ := by
    apply Equiv.ext
    intro p
    rcases p with ⟨v, i⟩
    cases v <;> rfl

/-- A triple-product term of one edge factor. -/
noncomputable def term (n : ℕ) (a b i j : Fin n) : Formula (Variables n) K :=
  mul (mul (var (.inr (.inl a, i))) (var (.inr (.inr b, j)))) (var (.inl (i, j)))

/-- One edge factor, with private occurrences for every summand. -/
noncomputable def edge (n : ℕ) (a b : Fin n) : Formula (Variables n) K :=
  op false (fun p : Fin n × Fin n => term n a b p.1 p.2)

/-- A single factor excluding a pair of simultaneously chosen images. -/
noncomputable def pairFactor (n : ℕ) (v : Vertex n) (p : ImagePair n) : Formula (Variables n) K :=
  add (const 1) (mul (const (-1)) (mul (var (.inr (v, p.val.1))) (var (.inr (v, p.val.2)))))

/-- The exactly-one formula at a pattern vertex. -/
noncomputable def selector (n : ℕ) (v : Vertex n) : Formula (Variables n) K :=
  mul (op false (fun i : Fin n => var (.inr (v, i))))
    (op true (fun p : ImagePair n => pairFactor n v p))

@[simp] theorem polynomial_term (n : ℕ) (a b i j : Fin n) :
    polynomial (term (K := K) n a b i j) =
      MvPolynomial.X (.inr (.inl a, i)) * MvPolynomial.X (.inr (.inr b, j)) *
        MvPolynomial.X (.inl (i, j)) := by
  simp [term]

@[simp] theorem polynomial_edge (n : ℕ) (a b : Fin n) :
    polynomial (edge (K := K) n a b) =
      ∑ i, ∑ j, MvPolynomial.X (.inr (.inl a, i)) * MvPolynomial.X (.inr (.inr b, j)) *
        MvPolynomial.X (.inl (i, j)) := by
  simp [edge, Fintype.sum_prod_type]

@[simp] theorem polynomial_pairFactor (n : ℕ) (v : Vertex n) (p : ImagePair n) :
    polynomial (pairFactor (K := K) n v p) =
      1 - MvPolynomial.X (.inr (v, p.val.1)) * MvPolynomial.X (.inr (v, p.val.2)) := by
  simp [pairFactor, sub_eq_add_neg]

@[simp] theorem polynomial_selector (n : ℕ) (v : Vertex n) :
    polynomial (selector (K := K) n v) =
      (∑ i, MvPolynomial.X (.inr (v, i))) *
        ∏ i, ∏ j ∈ Finset.univ.filter (i < ·),
          (1 - MvPolynomial.X (.inr (v, i)) * MvPolynomial.X (.inr (v, j))) := by
  simp only [selector, polynomial_mul, polynomial_op, polynomial_var, polynomial_pairFactor,
    ↓reduceIte]
  congr 1
  let f (p : Fin n × Fin n) : MvPolynomial (Variables n) K :=
    1 - MvPolynomial.X (.inr (v, p.1)) * MvPolynomial.X (.inr (v, p.2))
  have h := Finset.prod_subtype (p := fun p : Fin n × Fin n => p.1 < p.2) (F := inferInstance)
    (Finset.univ.filter (fun p => p.1 < p.2)) (by simp) f
  exact h.symm.trans (by simp only [Finset.prod_filter, Fintype.prod_prod_type, f])

/-- Isomorphic children give isomorphic binary products. -/
noncomputable def mulIso {V : Type*} (π : V → V) (F F' G G' : Formula V K)
    (hF : Iso π F.tree F'.tree) (hG : Iso π G.tree G'.tree) :
    Iso π (mul F G).tree (mul F' G').tree :=
  joinIso π (fun b : Bool => (if b then F else G).tree)
    (fun b : Bool => (if b then F' else G').tree) (Equiv.refl _)
    (fun b => by cases b; exact hG; exact hF) true

/-- Isomorphic children give isomorphic binary sums. -/
noncomputable def addIso {V : Type*} (π : V → V) (F F' G G' : Formula V K)
    (hF : Iso π F.tree F'.tree) (hG : Iso π G.tree G'.tree) :
    Iso π (add F G).tree (add F' G').tree :=
  joinIso π (fun b : Bool => (if b then F else G).tree)
    (fun b : Bool => (if b then F' else G').tree) (Equiv.refl _)
    (fun b => by cases b; exact hG; exact hF) false

/-- Permute the images and sort the two endpoints back into increasing order. -/
def pairMap {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : ImagePair n) : ImagePair n :=
  ⟨(min (σ p.val.1) (σ p.val.2), max (σ p.val.1) (σ p.val.2)),
    min_lt_max.mpr (σ.injective.ne p.property.ne)⟩

theorem pairMap_symm_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : ImagePair n) :
    pairMap σ.symm (pairMap σ p) = p := by
  apply Subtype.ext
  by_cases h : σ p.val.1 ≤ σ p.val.2
  · simp [pairMap, min_eq_left h, max_eq_right h, le_of_lt p.property]
  · simp [pairMap, min_eq_right (le_of_not_ge h), max_eq_left (le_of_not_ge h),
      le_of_lt p.property]

/-- The induced permutation on the paper's unordered image pairs. -/
def pairPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (ImagePair n) where
  toFun := pairMap σ
  invFun := pairMap σ.symm
  left_inv := pairMap_symm_apply σ
  right_inv p := by simpa using pairMap_symm_apply σ.symm p

end Lax461425Proofs.PatternFormulaBlocks
