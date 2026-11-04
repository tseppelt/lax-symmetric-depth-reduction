import Lax461425Proofs.BooleanSelectors
import Lax461425.HomomorphismPolynomials

/-!
The algebraic witness of Section 7.1: Boolean variables encode the image of each pattern
vertex, and the selector removes every assignment which is not a vertex map. This file
proves the polynomial identity, separately from construction of its formula circuit.
-/

namespace Lax461425Proofs.PatternBooleanWitness

open Lax461425.HomomorphismPolynomials Lax461425.SymmetricFamilies BooleanSelectors
open scoped Classical BigOperators

variable {K : Type*} [CommRing K]

/-- One Boolean variable for each possible image of each pattern vertex. -/
abbrev Aux (F : Pattern) (n : ℕ) := (F.A ⊕ F.B) × Fin n

/-- A variable referring to a possible image of a vertex. -/
noncomputable def auxVar (F : Pattern) (n : ℕ) (a : F.A ⊕ F.B) (i : Fin n) :
    MvPolynomial ((Fin n × Fin n) ⊕ Aux F n) K := MvPolynomial.X (.inr (a, i))

/-- The exactly-one polynomial at a pattern vertex. -/
noncomputable def vertexSelector (F : Pattern) (n : ℕ) (a : F.A ⊕ F.B) :
    MvPolynomial ((Fin n × Fin n) ⊕ Aux F n) K :=
  (∑ i, auxVar F n a i) * ∏ i, ∏ j ∈ Finset.univ.filter (i < ·),
    (1 - auxVar F n a i * auxVar F n a j)

/-- A factor for one occurrence of a pattern edge. -/
noncomputable def edgeFactor (F : Pattern) (n : ℕ) (a : F.A) (b : F.B) :
    MvPolynomial ((Fin n × Fin n) ⊕ Aux F n) K :=
  ∑ i, ∑ j, auxVar F n (.inl a) i * auxVar F n (.inr b) j * MvPolynomial.X (.inl (i, j))

/-- The polynomial `g_F` displayed in Section 7.1. Edge multiplicities are retained. -/
noncomputable def witness (F : Pattern) (n : ℕ) :
    MvPolynomial ((Fin n × Fin n) ⊕ Aux F n) K :=
  (∏ v : F.A ⊕ F.B, vertexSelector F n v) *
    ∏ a, ∏ b, (edgeFactor F n a b) ^ F.mult a b

/-- Edge-factor value after a Boolean assignment. -/
noncomputable def edgeValue (F : Pattern) (n : ℕ) (e : Aux F n → Bool)
    (a : F.A) (b : F.B) : MvPolynomial (Fin n × Fin n) K :=
  ∑ i, ∑ j, bit (e (.inl a, i)) * bit (e (.inr b, j)) * MvPolynomial.X (i, j)

theorem eval_witness (F : Pattern) (n : ℕ) (e : Aux F n → Bool) :
    MvPolynomial.eval₂ MvPolynomial.C
      (Sum.elim MvPolynomial.X (fun y => MvPolynomial.C (if e y then 1 else 0)))
        (witness (K := K) F n) =
      allSelectors (K := MvPolynomial (Fin n × Fin n) K) e *
        ∏ a, ∏ b, (edgeValue F n e a b) ^ F.mult a b := by
  have hbit (y : Aux F n) :
      (MvPolynomial.C (if e y then 1 else 0) : MvPolynomial (Fin n × Fin n) K) = bit (e y) := by
    cases e y <;> simp [bit]
  change (MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim MvPolynomial.X (fun y => MvPolynomial.C (if e y then 1 else 0))))
      (witness (K := K) F n) = _
  simp only [witness, vertexSelector, auxVar, edgeFactor, allSelectors, exactlyOne, edgeValue,
    map_mul, map_prod, map_sum, map_pow, map_sub, map_one, MvPolynomial.eval₂Hom_X',
    Sum.elim_inl, Sum.elim_inr, hbit]

/-- On the assignment encoding `h`, an edge factor selects the corresponding matrix
variable. -/
theorem edgeValue_encodeMaps (F : Pattern) (n : ℕ) (h : (F.A ⊕ F.B) → Fin n)
    (a : F.A) (b : F.B) :
    edgeValue (K := K) F n (encodeMaps h) a b = MvPolynomial.X (h (.inl a), h (.inr b)) := by
  simp [edgeValue, encodeMaps, encode, bit]

/-- A function on a disjoint union is a pair of functions. -/
def mapsEquiv (F : Pattern) (n : ℕ) : ((F.A ⊕ F.B) → Fin n) ≃
    ((F.A → Fin n) × (F.B → Fin n)) where
  toFun h := (fun a => h (.inl a), fun b => h (.inr b))
  invFun h := Sum.elim h.1 h.2
  left_inv h := by funext v; cases v <;> rfl
  right_inv h := rfl

/-- The Boolean-cube sum of the explicit pattern witness is its homomorphism polynomial.
This handles isolated vertices, parallel edges, empty sides, and `n = 0`. -/
theorem boolSum_witness (F : Pattern) (n : ℕ) :
    boolSum (witness (K := K) F n) = hom K F n := by
  letI : DecidableEq (F.A ⊕ F.B) := Classical.decEq _
  simp only [boolSum, eval_witness]
  have hs := sum_allSelectors (K := MvPolynomial (Fin n × Fin n) K)
    (A := F.A ⊕ F.B) (n := n)
    (fun e => ∏ a, ∏ b, (edgeValue (K := K) F n e a b) ^ F.mult a b)
  convert hs.trans (show (∑ h : (F.A ⊕ F.B) → Fin n,
    ∏ a, ∏ b, (edgeValue (K := K) F n (encodeMaps h) a b) ^ F.mult a b) = hom K F n from ?_) using 1
  all_goals try (apply Finset.sum_congr (by ext e; simp); intro e he; rfl)
  simp_rw [edgeValue_encodeMaps]
  change (∑ h : (F.A ⊕ F.B) → Fin n,
    ∏ a, ∏ b, (MvPolynomial.X (h (.inl a), h (.inr b)) : MvPolynomial (Fin n × Fin n) K) ^
      F.mult a b) = hom K F n
  rw [Fintype.sum_equiv (mapsEquiv F n)
    (fun h => ∏ a, ∏ b, (MvPolynomial.X (h (.inl a), h (.inr b)) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a b)
    (fun h => ∏ a, ∏ b, (MvPolynomial.X (h.1 a, h.2 b) : MvPolynomial (Fin n × Fin n) K) ^ F.mult a b) (fun h => rfl)]
  rw [Fintype.sum_prod_type]
  rfl

end Lax461425Proofs.PatternBooleanWitness
