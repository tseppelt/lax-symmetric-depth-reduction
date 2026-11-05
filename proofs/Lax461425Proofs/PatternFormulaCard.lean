import Lax461425Proofs.PatternFormulaBlocks
import Lax461425Proofs.TreeFormulaOrbit
import Mathlib.Tactic

/-!
Gate counts by label kind for the concrete primitive formulas in Section 7.1. Private
occurrences are counted separately. Bounds therefore control all extending automorphisms,
not just the natural action used to establish symmetry.
-/

namespace Lax461425Proofs.PatternFormulaCard

open Lax461425.Circuits
open TreeFormulaCircuit TreeFormulaOperations TreeFormulaOrbit ComputedFormula PatternFormulaBlocks
open scoped Classical

variable {V K : Type*}

section Semiring

variable [CommSemiring K]

/-- Count occurrences of a given label kind. -/
noncomputable def count (F : Formula V K) (q : Fin 4) : ℕ :=
  ∑ g : F.tree.Gate, if labelKind (F.tree.label g) = q then 1 else 0

theorem count_eq_ncard (F : Formula V K) (q : Fin 4) :
    count F q = ({g | labelKind (F.tree.label g) = q} : Set F.tree.Gate).ncard := by
  rw [← Set.fintypeCard_eq_ncard, Fintype.card_subtype]
  simp only [count, Finset.sum_boole, Set.mem_ofPred_eq, Nat.cast_id]

@[simp] theorem count_var (x : V) (q : Fin 4) :
    count (var (K := K) x) q = if (0 : Fin 4) = q then 1 else 0 := by
  change (∑ _ : Unit, if (0 : Fin 4) = q then 1 else 0) = _
  simp

@[simp] theorem count_const (c : K) (q : Fin 4) :
    count (const (V := V) c) q = if (1 : Fin 4) = q then 1 else 0 := by
  change (∑ _ : Unit, if (1 : Fin 4) = q then 1 else 0) = _
  simp

theorem count_op {I : Type} [Fintype I] (mul : Bool) (F : I → Formula V K) (q : Fin 4) :
    count (op mul F) q = (if (if mul then (3 : Fin 4) else 2) = q then 1 else 0) +
      ∑ i, count (F i) q := by
  change (∑ g : Unit ⊕ (Σ i : I, (F i).tree.Gate),
      if labelKind ((join (fun i => (F i).tree) mul).label g) = q then 1 else 0) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [Fintype.sum_unique, join, labelKind]
  cases mul <;> rfl

theorem count_mul (F G : Formula V K) (q : Fin 4) :
    count (ComputedFormula.mul F G) q =
      (if (3 : Fin 4) = q then 1 else 0) + count F q + count G q := by
  simp [ComputedFormula.mul, count_op, Fintype.sum_bool,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem count_add (F G : Formula V K) (q : Fin 4) :
    count (ComputedFormula.add F G) q =
      (if (2 : Fin 4) = q then 1 else 0) + count F q + count G q := by
  simp [ComputedFormula.add, count_op, Fintype.sum_bool,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Semiring

section Field

variable [Field K]

theorem count_tag (t : K) (F : Formula V K) (q : Fin 4) :
    count (tag t F) q = count F q +
      (if (1 : Fin 4) = q then 2 else 0) + (if (3 : Fin 4) = q then 2 else 0) := by
  fin_cases q <;> simp [tag, count_mul] <;> omega

theorem count_term (n : ℕ) (a b i j : Fin n) (q : Fin 4) :
    count (term (K := K) n a b i j) q =
      if (0 : Fin 4) = q then 3 else if (3 : Fin 4) = q then 2 else 0 := by
  fin_cases q <;> simp [term, count_mul]

theorem count_edge (n : ℕ) (a b : Fin n) (q : Fin 4) :
    count (edge (K := K) n a b) q =
      if (0 : Fin 4) = q then 3 * n ^ 2 else
      if (2 : Fin 4) = q then 1 else if (3 : Fin 4) = q then 2 * n ^ 2 else 0 := by
  fin_cases q <;> simp [edge, count_op, count_term, pow_two] <;> ring

theorem count_pairFactor (n : ℕ) (v : Vertex n) (p : ImagePair n) (q : Fin 4) :
    count (pairFactor (K := K) n v p) q = if (2 : Fin 4) = q then 1 else 2 := by
  fin_cases q <;> simp [pairFactor, count_add, count_mul]

theorem count_selector (n : ℕ) (v : Vertex n) (q : Fin 4) :
    count (selector (K := K) n v) q =
      if (0 : Fin 4) = q then 2 * Fintype.card (ImagePair n) + n else
      if (1 : Fin 4) = q then 2 * Fintype.card (ImagePair n) else
      if (2 : Fin 4) = q then Fintype.card (ImagePair n) + 1 else
        2 * Fintype.card (ImagePair n) + 2 := by
  fin_cases q <;> simp [selector, count_mul, count_op, count_pairFactor] <;> omega

theorem imagePair_card_le (n : ℕ) : Fintype.card (ImagePair n) ≤ n ^ 2 := by
  simpa [pow_two] using Fintype.card_subtype_le (fun p : Fin n × Fin n => p.1 < p.2)

theorem imagePair_card_one : Fintype.card (ImagePair 1) = 0 := by
  letI : IsEmpty (ImagePair 1) := ⟨fun p => p.2.ne (Subsingleton.elim _ _)⟩
  exact Fintype.card_eq_zero

/-- Every kind of gate in a tagged edge block has at most `4*n²` occurrences. -/
theorem tagged_edge_count_le (n : ℕ) (hn : 1 ≤ n) (a b : Fin n) (t : K) (q : Fin 4) :
    count (tag t (edge (K := K) n a b)) q ≤ 4 * n ^ 2 := by
  have hsq : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  fin_cases q <;> simp [count_tag, count_edge] <;> omega

/-- Every kind of gate in a tagged selector block has at most `4*n²` occurrences.
The `n=1` case has no pair factors and is checked explicitly. -/
theorem tagged_selector_count_le (n : ℕ) (hn : 1 ≤ n) (v : Vertex n) (t : K) (q : Fin 4) :
    count (tag t (selector (K := K) n v)) q ≤ 4 * n ^ 2 := by
  have hd := imagePair_card_le n
  by_cases h1 : n = 1
  · subst n
    fin_cases q <;> simp [count_tag, count_selector, imagePair_card_one, -Fintype.card_subtype_compl]
  · have hn2 : 2 ≤ n := by omega
    have hsq : 4 ≤ n ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hn2 hn2
    have hn_sq : n ≤ n ^ 2 := by simpa [pow_two] using Nat.le_mul_of_pos_left n hn
    fin_cases q <;> simp [count_tag, count_selector, -Fintype.card_subtype_compl] <;> omega

theorem tagged_edge_kind_bound (n : ℕ) (hn : 1 ≤ n) (a b : Fin n) (t : K) (q : Fin 4) :
    ({g | labelKind ((tag t (edge (K := K) n a b)).tree.label g) = q} :
      Set (tag t (edge (K := K) n a b)).tree.Gate).ncard ≤ 4 * n ^ 2 := by
  rw [← count_eq_ncard]
  exact tagged_edge_count_le n hn a b t q

theorem tagged_selector_kind_bound (n : ℕ) (hn : 1 ≤ n) (v : Vertex n) (t : K) (q : Fin 4) :
    ({g | labelKind ((tag t (selector (K := K) n v)).tree.label g) = q} :
      Set (tag t (selector (K := K) n v)).tree.Gate).ncard ≤ 4 * n ^ 2 := by
  rw [← count_eq_ncard]
  exact tagged_selector_count_le n hn v t q

end Field
end Lax461425Proofs.PatternFormulaCard
