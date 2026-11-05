import Lax461425Proofs.TreeFormulaOperations

/-!
Bottom-up semantics for the private-input tree constructors. The values at old child gates
are retained when an addition or multiplication root is attached.
-/

namespace Lax461425Proofs.TreeFormulaSemantics

open Lax461425.Circuits TreeFormulaCircuit TreeFormulaOperations
open scoped Classical

variable {V K : Type*} [CommSemiring K]

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A polynomial value at every gate with the actual circuit evaluation equations. -/
structure Values (T : Tree V K) where
  val : T.Gate → MvPolynomial V K
  var_eq : ∀ g x, T.label g = .var x → val g = MvPolynomial.X x
  const_eq : ∀ g c, T.label g = .const c → val g = MvPolynomial.C c
  add_eq : ∀ g, T.label g = .add → val g = ∑ h, (circuit T).wire g h • val h
  mul_eq : ∀ g, T.label g = .mul → val g = ∏ h, val h ^ (circuit T).wire g h

theorem computes {T : Tree V K} (q : Values T) : (circuit T).Computes (q.val T.out) :=
  computes_of_values T q.val q.var_eq q.const_eq q.add_eq q.mul_eq

theorem parent_eq_none_iff (T : Tree V K) (g : T.Gate) : T.parent g = none ↔ g = T.out := by
  constructor
  · intro hp
    by_contra hg
    obtain ⟨p, h⟩ := T.parent_exists g hg
    rw [hp] at h
    cases h
  · rintro rfl
    exact T.parent_out

private theorem option_cases {A : Type*} (x : Option A) : x = none ∨ ∃ a, x = some a := by
  cases x <;> simp

variable {I : Type} [Fintype I] (T : I → Tree V K) (mul : Bool)

theorem sum_wire_root (q : JoinGate T → MvPolynomial V K) :
    (∑ h, (circuit (join T mul)).wire (.inl ()) h • q h) =
      ∑ i, q (.inr ⟨i, (T i).out⟩) := by
  suffices H : (∑ h : JoinGate T, (if joinParent T h = some (.inl ()) then (1 : ℕ) else 0) • q h) =
      ∑ i, q (.inr ⟨i, (T i).out⟩) by
    convert H using 1
    apply Finset.sum_congr
    · ext h
      exact ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩
    · intro h hh
      simp only [circuit, join]
      split <;> simp_all
  rw [Fintype.sum_sum_type]
  simp only [joinParent, reduceCtorEq, ↓reduceIte, zero_smul, Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (T i).out]
  · simp [joinParent, (T i).parent_out]
  · intro h hh hne
    have hp : (T i).parent h ≠ none := (parent_eq_none_iff (T i) h).not.mpr hne
    rcases option_cases ((T i).parent h) with heq | ⟨p, heq⟩
    · exact False.elim (hp heq)
    · simp [heq]
  · simp

theorem prod_wire_root (q : JoinGate T → MvPolynomial V K) :
    (∏ h, q h ^ (circuit (join T mul)).wire (.inl ()) h) =
      ∏ i, q (.inr ⟨i, (T i).out⟩) := by
  suffices H : (∏ h : JoinGate T, q h ^ (if joinParent T h = some (.inl ()) then (1 : ℕ) else 0)) =
      ∏ i, q (.inr ⟨i, (T i).out⟩) by
    convert H using 1
    apply Finset.prod_congr
    · ext h
      exact ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩
    · intro h hh
      simp only [circuit, join]
      split <;> simp_all
  rw [Fintype.prod_sum_type]
  simp only [joinParent, reduceCtorEq, ↓reduceIte, pow_zero, Finset.prod_const_one, one_mul]
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.prod_eq_single (T i).out]
  · simp [(T i).parent_out]
  · intro h hh hne
    have hp : (T i).parent h ≠ none := (parent_eq_none_iff (T i) h).not.mpr hne
    rcases option_cases ((T i).parent h) with heq | ⟨p, heq⟩
    · exact False.elim (hp heq)
    · simp [heq]
  · simp

theorem sum_wire_child (q : JoinGate T → MvPolynomial V K)
    (i : I) (g : (T i).Gate) :
    (∑ h, (circuit (join T mul)).wire (.inr ⟨i, g⟩) h • q h) =
      ∑ h, (circuit (T i)).wire g h • q (.inr ⟨i, h⟩) := by
  suffices H : (∑ h : JoinGate T, (if joinParent T h = some (.inr ⟨i, g⟩) then (1 : ℕ) else 0) • q h) =
      ∑ h : (T i).Gate, (if (T i).parent h = some g then (1 : ℕ) else 0) • q (.inr ⟨i, h⟩) by
    convert H using 1 <;> apply Finset.sum_congr
    all_goals
      first
      | (ext h; exact ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩)
      | (intro h hh; simp only [circuit, join]; split <;> simp_all)
  rw [Fintype.sum_sum_type]
  simp only [joinParent, reduceCtorEq, ↓reduceIte, zero_smul, Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro h hh
    rcases option_cases ((T i).parent h) with hp | ⟨p, hp⟩ <;> simp [hp]
  · intro j hj hji
    apply Finset.sum_eq_zero
    intro h hh
    rcases option_cases ((T j).parent h) with hp | ⟨p, hp⟩ <;> simp [hp, hji]
  · simp

theorem prod_wire_child (q : JoinGate T → MvPolynomial V K)
    (i : I) (g : (T i).Gate) :
    (∏ h, q h ^ (circuit (join T mul)).wire (.inr ⟨i, g⟩) h) =
      ∏ h, q (.inr ⟨i, h⟩) ^ (circuit (T i)).wire g h := by
  suffices H : (∏ h : JoinGate T, q h ^ (if joinParent T h = some (.inr ⟨i, g⟩) then (1 : ℕ) else 0)) =
      ∏ h : (T i).Gate, q (.inr ⟨i, h⟩) ^ (if (T i).parent h = some g then (1 : ℕ) else 0) by
    convert H using 1 <;> apply Finset.prod_congr
    all_goals
      first
      | (ext h; exact ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩)
      | (intro h hh; simp only [circuit, join]; split <;> simp_all)
  rw [Fintype.prod_sum_type]
  simp only [joinParent, reduceCtorEq, ↓reduceIte, pow_zero, Finset.prod_const_one, one_mul]
  rw [Fintype.prod_sigma]
  rw [Finset.prod_eq_single i]
  · apply Finset.prod_congr rfl
    intro h hh
    rcases option_cases ((T i).parent h) with hp | ⟨p, hp⟩ <;> simp [hp]
  · intro j hj hji
    apply Finset.prod_eq_one
    intro h hh
    rcases option_cases ((T j).parent h) with hp | ⟨p, hp⟩ <;> simp [hp, hji]
  · simp

/-- The value function of a joined tree. -/
noncomputable def joinVal (q : ∀ i, Values (T i)) : JoinGate T → MvPolynomial V K
    | .inl _ => if mul then ∏ i, (q i).val (T i).out else ∑ i, (q i).val (T i).out
    | .inr ⟨i, g⟩ => (q i).val g

/-- Evaluation values for a new operation root and its private child occurrences. -/
noncomputable def joinValues (q : ∀ i, Values (T i)) : Values (join T mul) where
  val := joinVal T mul q
  var_eq g x hg := by
    cases g with
    | inl u => cases mul <;> cases hg
    | inr p => exact (q p.1).var_eq p.2 x hg
  const_eq g c hg := by
    cases g with
    | inl u => cases mul <;> cases hg
    | inr p => exact (q p.1).const_eq p.2 c hg
  add_eq g hg := by
    cases g with
    | inl u =>
      cases u
      cases mul with
      | true => cases hg
      | false => exact (sum_wire_root T false (joinVal T false q)).symm
    | inr p =>
      rcases p with ⟨i, g⟩
      change (q i).val g = ∑ h, (circuit (join T mul)).wire (.inr ⟨i, g⟩) h • joinVal T mul q h
      exact ((q i).add_eq g hg).trans (sum_wire_child T mul (joinVal T mul q) i g).symm
  mul_eq g hg := by
    cases g with
    | inl u =>
      cases u
      cases mul with
      | false => cases hg
      | true => exact (prod_wire_root T true (joinVal T true q)).symm
    | inr p =>
      rcases p with ⟨i, g⟩
      change (q i).val g = ∏ h, (joinVal T mul q h) ^ (circuit (join T mul)).wire (.inr ⟨i, g⟩) h
      exact ((q i).mul_eq g hg).trans (prod_wire_child T mul (joinVal T mul q) i g).symm

end Lax461425Proofs.TreeFormulaSemantics

