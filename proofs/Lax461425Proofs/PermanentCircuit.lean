import Lax461425Proofs.PermanentRyser
import Lax461425.SymmetricFamilies
import Lax461425.SymmetricClasses
import Lax461425.SymmetricVNP
import Lax461425Proofs.CircuitFacts

/-! The explicit polynomial-size symmetric circuit for Ryser's Boolean witness. -/

namespace Lax461425Proofs.PermanentCircuit

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies Lax461425.SymmetricVNP
open Lax461425.SymmetricClasses
open Lax461425.Permanent
open Lax461425Proofs.Permanent (ryserWitness)
open scoped BigOperators Classical

inductive Gate (n : ℕ) where
  | x (i j : Fin n)
  | y (j : Fin n)
  | xy (i j : Fin n)
  | row (i : Fin n)
  | sign (j : Fin n)
  | negone
  | signprod
  | rowprod
  | out
  deriving DecidableEq, Fintype

variable {n : ℕ} {K : Type*} [CommRing K]

def label : Gate n → GateLabel ((Fin n × Fin n) ⊕ Fin n) K
  | .x i j => .var (Sum.inl (i, j))
  | .y j => .var (Sum.inr j)
  | .xy _ _ => .mul
  | .row _ => .add
  | .sign _ => .add
  | .negone => .const (-1)
  | .signprod | .rowprod | .out => .mul

def wire : Gate n → Gate n → ℕ
  | .xy i j, .x i' j' => if i = i' ∧ j = j' then 1 else 0
  | .xy _ j, .y j' => if j = j' then 1 else 0
  | .row i, .xy i' _ => if i = i' then 1 else 0
  | .sign j, .y j' => if j = j' then 2 else 0
  | .sign _, .negone => 1
  | .signprod, .sign _ => 1
  | .rowprod, .row _ => 1
  | .out, .signprod => 1
  | .out, .rowprod => 1
  | _, _ => 0

def rank : Gate n → ℕ
  | .x _ _ | .y _ | .negone => 0
  | .xy _ _ | .sign _ => 1
  | .row _ => 2
  | .signprod => 3
  | .rowprod => 3
  | .out => 4

lemma rank_lt {g h : Gate n} (hw : 0 < wire g h) : rank h < rank g := by
  cases g <;> cases h <;> simp_all [wire, rank] <;> split_ifs at hw <;> simp_all

lemma acyclic (g : Gate n) : ¬ Relation.TransGen (fun h g => 0 < wire g h) g g := by
  intro hp
  have hlt : ∀ {a b : Gate n}, Relation.TransGen (fun h g => 0 < wire g h) a b →
      rank a < rank b := by
    intro a b h
    induction h with
    | single h => exact rank_lt h
    | tail _ h ih => exact ih.trans (rank_lt h)
  exact (lt_irrefl _ (hlt hp))

lemma reaches_out (hn : 0 < n) (g : Gate n) :
    Relation.ReflTransGen (fun h g => 0 < wire g h) g .out := by
  have hs : Relation.ReflTransGen (fun h g : Gate n => 0 < wire g h) .signprod .out :=
    .single (by simp [wire])
  have hr : Relation.ReflTransGen (fun h g : Gate n => 0 < wire g h) .rowprod .out :=
    .single (by simp [wire])
  have hsg (j : Fin n) :
      Relation.ReflTransGen (fun h g : Gate n => 0 < wire g h) (.sign j) .out :=
    (Relation.ReflTransGen.single (by simp [wire])).trans hs
  have hrw (i : Fin n) :
      Relation.ReflTransGen (fun h g : Gate n => 0 < wire g h) (.row i) .out :=
    (Relation.ReflTransGen.single (by simp [wire])).trans hr
  have hxy (i j : Fin n) :
      Relation.ReflTransGen (fun h g : Gate n => 0 < wire g h) (.xy i j) .out :=
    (Relation.ReflTransGen.single (by simp [wire])).trans (hrw i)
  cases g with
  | x i j => exact (Relation.ReflTransGen.single (by simp [wire])).trans (hxy i j)
  | y j => exact (Relation.ReflTransGen.single (by simp [wire])).trans (hsg j)
  | xy i j => exact hxy i j
  | row i => exact hrw i
  | sign j => exact hsg j
  | negone => exact (Relation.ReflTransGen.single (by simp [wire])).trans (hsg ⟨0, hn⟩)
  | signprod => exact hs
  | rowprod => exact hr
  | out => exact .refl

/-- The Ryser circuit; positive matrix order ensures every input is used. -/
noncomputable def circuit (hn : 0 < n) : Circuit ((Fin n × Fin n) ⊕ Fin n) K where
  Gate := Gate n
  label := label
  wire := wire
  out := .out
  wire_eq_zero_of_isInput g h hg := by
    cases g <;> cases h <;> simp_all [label, GateLabel.IsInput, wire]
  acyclic := acyclic
  reaches_out := reaches_out hn

/-- The column-permutation action on the auxiliary Boolean variables. -/
def auxAction (n : ℕ) : Γ n →* Equiv.Perm (Fin n) := MonoidHom.snd _ _

def act (γ : Γ n) : Gate n → Gate n
  | .x i j => .x (γ.1 i) (γ.2 j)
  | .y j => .y (γ.2 j)
  | .xy i j => .xy (γ.1 i) (γ.2 j)
  | .row i => .row (γ.1 i)
  | .sign j => .sign (γ.2 j)
  | .negone => .negone
  | .signprod => .signprod
  | .rowprod => .rowprod
  | .out => .out

def actEquiv (γ : Γ n) : Equiv.Perm (Gate n) where
  toFun := act γ
  invFun := act γ⁻¹
  left_inv g := by cases g <;> simp [act]
  right_inv g := by cases g <;> simp [act]

theorem symmetric (hn : 0 < n) :
    Symmetric (jointAction (auxAction n)) (circuit (K := K) hn) := by
  intro γ
  refine ⟨actEquiv γ, ?_, ?_⟩
  · intro g
    cases g <;> rfl
  · intro g h
    change wire (act γ g) (act γ h) = wire g h
    cases g <;> cases h <;> simp [act, wire]

def gateEquiv : Gate n ≃
    (Fin n × Fin n) ⊕ Fin n ⊕ (Fin n × Fin n) ⊕ Fin n ⊕ Fin n ⊕ Fin 4 where
  toFun
    | .x i j => .inl (i, j)
    | .y j => .inr (.inl j)
    | .xy i j => .inr (.inr (.inl (i, j)))
    | .row i => .inr (.inr (.inr (.inl i)))
    | .sign j => .inr (.inr (.inr (.inr (.inl j))))
    | .negone => .inr (.inr (.inr (.inr (.inr 0))))
    | .signprod => .inr (.inr (.inr (.inr (.inr 1))))
    | .rowprod => .inr (.inr (.inr (.inr (.inr 2))))
    | .out => .inr (.inr (.inr (.inr (.inr 3))))
  invFun
    | .inl (i, j) => .x i j
    | .inr (.inl j) => .y j
    | .inr (.inr (.inl (i, j))) => .xy i j
    | .inr (.inr (.inr (.inl i))) => .row i
    | .inr (.inr (.inr (.inr (.inl j)))) => .sign j
    | .inr (.inr (.inr (.inr (.inr k)))) =>
      if k = 0 then .negone else if k = 1 then .signprod else if k = 2 then .rowprod else .out
  left_inv g := by cases g <;> rfl
  right_inv z := by
    rcases z with ⟨i, j⟩ | j | ⟨i, j⟩ | i | j | k <;> try rfl
    fin_cases k <;> rfl

theorem card_gate : Fintype.card (Gate n) = 2 * n ^ 2 + 3 * n + 4 := by
  rw [Fintype.card_congr gateEquiv]
  simp
  ring

lemma sum_gate {S : Type*} [AddCommMonoid S] (f : Gate n → S) :
    (∑ g, f g) =
      (∑ i, ∑ j, f (.x i j)) + (∑ j, f (.y j)) +
      (∑ i, ∑ j, f (.xy i j)) + (∑ i, f (.row i)) +
      (∑ j, f (.sign j)) + f .negone + f .signprod + f .rowprod + f .out := by
  rw [← gateEquiv.symm.sum_comp f]
  simp [gateEquiv, Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_succ,
    add_assoc]

lemma prod_gate {S : Type*} [CommMonoid S] (f : Gate n → S) :
    (∏ g, f g) =
      (∏ i, ∏ j, f (.x i j)) * (∏ j, f (.y j)) *
      (∏ i, ∏ j, f (.xy i j)) * (∏ i, f (.row i)) *
      (∏ j, f (.sign j)) * f .negone * f .signprod * f .rowprod * f .out := by
  rw [← gateEquiv.symm.prod_comp f]
  simp [gateEquiv, Fintype.prod_sum_type, Fintype.prod_prod_type, Fin.prod_univ_succ,
    mul_assoc]

/-- The intended polynomial at each gate of the Ryser circuit. -/
noncomputable def value : Gate n → MvPolynomial ((Fin n × Fin n) ⊕ Fin n) K
  | .x i j => MvPolynomial.X (Sum.inl (i, j))
  | .y j => MvPolynomial.X (Sum.inr j)
  | .xy i j => MvPolynomial.X (Sum.inl (i, j)) * MvPolynomial.X (Sum.inr j)
  | .row i => ∑ j, MvPolynomial.X (Sum.inl (i, j)) * MvPolynomial.X (Sum.inr j)
  | .sign j => 2 * MvPolynomial.X (Sum.inr j) - 1
  | .negone => MvPolynomial.C (-1)
  | .signprod => ∏ j : Fin n, (2 * MvPolynomial.X (Sum.inr j) - 1)
  | .rowprod => ∏ i : Fin n, ∑ j : Fin n,
      MvPolynomial.X (Sum.inl (i, j)) * MvPolynomial.X (Sum.inr j)
  | .out => ryserWitness K n

set_option backward.isDefEq.respectTransparency false in
/-- Correctness of the explicitly constructed Ryser circuit. -/
theorem computes (hn : 0 < n) : (circuit (K := K) hn).Computes (ryserWitness K n) := by
  change (circuit hn).ComputesAt .out (value (K := K) .out)
  apply CircuitFacts.computesAt_of_local_values (circuit hn) value
  · intro g x hx
    cases g <;> simp_all [circuit, label, value]
  · intro g c hc
    cases g <;> simp_all [circuit, label, value]
  · intro g hg
    cases g <;> simp only [circuit, label, reduceCtorEq] at hg
    all_goals simp only [circuit]; rw [sum_gate]; simp [wire, value] <;> ring
  · intro g hg
    cases g <;> simp only [circuit, label, reduceCtorEq] at hg
    all_goals simp only [circuit]; rw [prod_gate]; simp [wire, value, ryserWitness, ite_and]

/-- The orbit bound is valid for all extending automorphisms because total gate count is
already quadratic. -/
theorem orbitSize_le (hn : 0 < n) :
    orbitSize (jointAction (auxAction n)) (circuit (K := K) hn) ≤
      2 * n ^ 2 + 3 * n + 4 := by
  apply Finset.sup_le
  intro g _
  exact (Set.ncard_le_card _).trans_eq (by
    simpa [Nat.card_eq_fintype_card, circuit] using card_gate (n := n))

end Lax461425Proofs.PermanentCircuit
