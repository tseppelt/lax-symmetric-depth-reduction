import Lax461425.CircuitProperties
import Lax461425Proofs.TreeFormulaSemantics

open Lax461425.CircuitProperties

/-!
Concrete formula trees packaged with their checked bottom-up polynomial values. Sum and
product constructors retain private occurrences of all child gates.
-/

namespace Lax461425Proofs.ComputedFormula

open Lax461425.Circuits TreeFormulaCircuit TreeFormulaOperations TreeFormulaSemantics
open scoped Classical

variable {V K : Type*}

section Semiring

variable [CommSemiring K]

/-- A private-leaf formula with values satisfying the circuit computation rules. -/
structure Formula (V K : Type*) [CommSemiring K] where
  tree : Tree V K
  values : Values tree

/-- The polynomial computed at the root. -/
noncomputable def polynomial (F : Formula V K) : MvPolynomial V K := F.values.val F.tree.out

theorem computes (F : Formula V K) : (circuit F.tree).Computes (polynomial F) :=
  TreeFormulaSemantics.computes F.values

theorem isFormula (F : Formula V K) : (IsFormula (circuit F.tree)) :=
  TreeFormulaCircuit.isFormula F.tree

/-- A private occurrence of a variable. -/
noncomputable def var (x : V) : Formula V K where
  tree := varInput x
  values :=
    { val := fun _ => MvPolynomial.X x
      var_eq := by intros g y h; cases h; rfl
      const_eq := by intros g c h; cases h
      add_eq := by intros g h; cases h
      mul_eq := by intros g h; cases h }

/-- A private occurrence of a field constant. -/
noncomputable def const (c : K) : Formula V K where
  tree := constant c
  values :=
    { val := fun _ => MvPolynomial.C c
      var_eq := by intros g y h; cases h
      const_eq := by intros g d h; cases h; rfl
      add_eq := by intros g h; cases h
      mul_eq := by intros g h; cases h }

@[simp] theorem polynomial_var (x : V) : polynomial (var (K := K) x) = MvPolynomial.X x := rfl

@[simp] theorem polynomial_const (c : K) : polynomial (const (V := V) c) = MvPolynomial.C c := rfl

/-- An unbounded sum or product of distinct formula occurrences. -/
noncomputable def op {I : Type} [Fintype I] (mul : Bool) (F : I → Formula V K) : Formula V K where
  tree := join (fun i => (F i).tree) mul
  values := joinValues (fun i => (F i).tree) mul (fun i => (F i).values)

@[simp] theorem polynomial_op {I : Type} [Fintype I] (mul : Bool) (F : I → Formula V K) :
    polynomial (op mul F) = if mul then ∏ i, polynomial (F i) else ∑ i, polynomial (F i) := rfl

/-- Binary multiplication, with two private child occurrences. -/
noncomputable def mul (F G : Formula V K) : Formula V K := op true (fun b : Bool => if b then F else G)

/-- Binary addition, with two private child occurrences. -/
noncomputable def add (F G : Formula V K) : Formula V K := op false (fun b : Bool => if b then F else G)

@[simp] theorem polynomial_mul (F G : Formula V K) : polynomial (mul F G) = polynomial F * polynomial G := by
  simp [mul, Fintype.prod_bool]

@[simp] theorem polynomial_add (F G : Formula V K) : polynomial (add F G) = polynomial F + polynomial G := by
  simp [add, Fintype.sum_bool]

end Semiring

section Field

variable [Field K]

/-- Value-preserving inverse tagging of a formula occurrence. -/
noncomputable def tag (t : K) (F : Formula V K) : Formula V K :=
  mul (const t⁻¹) (mul (const t) F)

@[simp] theorem polynomial_tag (t : K) (ht : t ≠ 0) (F : Formula V K) :
    polynomial (tag t F) = polynomial F := by
  simp [tag, ← mul_assoc, ← map_mul, ht]

end Field

end Lax461425Proofs.ComputedFormula
