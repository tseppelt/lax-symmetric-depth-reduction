import Lax461425Proofs.RigidConstruction
import Mathlib.Algebra.MvPolynomial.Basic

/-!
Helper material for the rigidification proof: the reduced circuit `C'` computes the same
polynomial as `C`.
-/

namespace Lax461425Proofs.RigidComputes

open Lax461425.Circuits RigidHeight RigidEquiv RigidWeight RigidRep RigidConstruction

open scoped Classical

variable {V K : Type*} [CommSemiring K]

/-- A gate of a circuit computes at most one polynomial. -/
theorem computesAt_unique (D : Circuit V K) (g : D.Gate) :
    ∀ {q q' : MvPolynomial V K}, D.ComputesAt g q → D.ComputesAt g q' → q = q' := by
  induction g using (wellFounded_child D).induction with
  | _ g ih =>
    intro q q' hq hq'
    cases hq with
    | var hl =>
      cases hq' with
      | var hl' => rw [hl] at hl'; injection hl' with h; rw [h]
      | const hl' => rw [hl] at hl'; cases hl'
      | add _ hl' _ => rw [hl] at hl'; cases hl'
      | mul _ hl' _ => rw [hl] at hl'; cases hl'
    | const hl =>
      cases hq' with
      | var hl' => rw [hl] at hl'; cases hl'
      | const hl' => rw [hl] at hl'; injection hl' with h; rw [h]
      | add _ hl' _ => rw [hl] at hl'; cases hl'
      | mul _ hl' _ => rw [hl] at hl'; cases hl'
    | add qf hl hqf =>
      cases hq' with
      | var hl' => rw [hl] at hl'; cases hl'
      | const hl' => rw [hl] at hl'; cases hl'
      | add qf' hl' hqf' =>
        apply Finset.sum_congr rfl
        intro h _
        by_cases hw : 0 < D.wire g h
        · rw [ih h hw (hqf h hw) (hqf' h hw)]
        · simp [Nat.le_zero.mp (Nat.not_lt.mp hw)]
      | mul _ hl' _ => rw [hl] at hl'; cases hl'
    | mul qf hl hqf =>
      cases hq' with
      | var hl' => rw [hl] at hl'; cases hl'
      | const hl' => rw [hl] at hl'; cases hl'
      | add _ hl' _ => rw [hl] at hl'; cases hl'
      | mul qf' hl' hqf' =>
        apply Finset.prod_congr rfl
        intro h _
        by_cases hw : 0 < D.wire g h
        · rw [ih h hw (hqf h hw) (hqf' h hw)]
        · simp [Nat.le_zero.mp (Nat.not_lt.mp hw)]

/-- Auxiliary step for the transfer of `ComputesAt` to the reduced circuit: given values `qf x`
computed by the children `x` of `g`, there is a choice of values `q' b` for the gates `b` of the
reduced circuit that are computed by `b` and agree with `qf x` at `toC' x`. -/
theorem transfer_aux (C : Circuit V K) {g : C.Gate}
    (ih : ∀ y, Child C g y → ∀ {q : MvPolynomial V K}, C.ComputesAt y q →
      (reduced C).ComputesAt (toC' C y) q)
    {qf : C.Gate → MvPolynomial V K} (hqf : ∀ x, 0 < C.wire g x → C.ComputesAt x (qf x)) :
    ∃ q' : (reduced C).Gate → MvPolynomial V K,
      (∀ b, 0 < (reduced C).wire (toC' C g) b → (reduced C).ComputesAt b (q' b)) ∧
        (∀ x, 0 < C.wire g x → q' (toC' C x) = qf x) := by
  refine ⟨fun b => if hex : ∃ x, 0 < C.wire g x ∧ Equiv C x b.1 then qf (Classical.choose hex)
    else 0, ?_, ?_⟩
  · intro b hbpos
    dsimp only
    have hbpos : 0 < W C g b.1 := wire_toC'_eq C g b ▸ hbpos
    have hex : ∃ x, 0 < C.wire g x ∧ Equiv C x b.1 := by
      obtain ⟨x0, hx0e, hx0w⟩ := exists_of_W_pos C hbpos
      exact ⟨x0, hx0w, hx0e⟩
    rw [dif_pos hex]
    have hc0 := Classical.choose_spec hex
    have htoC : toC' C (Classical.choose hex) = b := by
      apply Subtype.ext
      show rep C (Classical.choose hex) = b.1
      rw [rep_eq_of_equiv C hc0.2]
      exact isLive_rep_self C b.2
    have hcomputes := ih _ hc0.1 (hqf _ hc0.1)
    rw [htoC] at hcomputes
    exact hcomputes
  · intro x hxw
    dsimp only
    have hex : ∃ x', 0 < C.wire g x' ∧ Equiv C x' (toC' C x).1 :=
      ⟨x, hxw, rep_equiv C x⟩
    rw [dif_pos hex]
    have hc0 := Classical.choose_spec hex
    have heqrep : Equiv C (Classical.choose hex) x :=
      equiv_trans C hc0.2 (equiv_symm C (rep_equiv C x))
    have hcw : 0 < C.wire g (Classical.choose hex) := hc0.1
    have hA : (reduced C).ComputesAt (toC' C (Classical.choose hex))
        (qf (Classical.choose hex)) := ih _ hcw (hqf _ hcw)
    have hB : (reduced C).ComputesAt (toC' C x) (qf x) := ih _ hxw (hqf _ hxw)
    have htoCeq : toC' C (Classical.choose hex) = toC' C x := by
      apply Subtype.ext
      show rep C (Classical.choose hex) = rep C x
      exact rep_eq_of_equiv C heqrep
    rw [htoCeq] at hA
    exact computesAt_unique (reduced C) (toC' C x) hA hB

omit [CommSemiring K] in
/-- The condition `b = toC' C x` for a gate `b` of the reduced circuit is the same as
`Equiv C x b.1`: both say that `b` is the class of `x`. -/
theorem toC'_eq_iff {C : Circuit V K} {x : C.Gate} {b : (reduced C).Gate} :
    b = toC' C x ↔ Equiv C x b.1 := by
  constructor
  · intro h; subst h; exact rep_equiv C x
  · intro h; exact Subtype.ext (((rep_eq_of_equiv C h).trans (isLive_rep_self C b.2)).symm)

/-- Regrouping a sum over the children of `g` by equivalence class: the sum of weighted values
`qf x` over all children `x` equals the sum of weighted values `q' b` over the classes `b`,
provided `q'` agrees with `qf` on classes of children. -/
theorem regroup_sum (C : Circuit V K) (g : C.Gate) (qf : C.Gate → MvPolynomial V K)
    (q' : (reduced C).Gate → MvPolynomial V K)
    (hagree : ∀ x, 0 < C.wire g x → q' (toC' C x) = qf x) :
    (∑ x, C.wire g x • qf x) = ∑ b : (reduced C).Gate, (reduced C).wire (toC' C g) b • q' b := by
  have hstep1 : ∀ b : (reduced C).Gate, (reduced C).wire (toC' C g) b • q' b =
      ∑ x, if Equiv C x b.1 then C.wire g x • q' b else 0 := by
    intro b
    calc (reduced C).wire (toC' C g) b • q' b = W C g b.1 • q' b := by rw [wire_toC'_eq]
      _ = (∑ x, if Equiv C x b.1 then C.wire g x else 0) • q' b := rfl
      _ = ∑ x, (if Equiv C x b.1 then C.wire g x else 0) • q' b := Finset.sum_smul
      _ = ∑ x, if Equiv C x b.1 then C.wire g x • q' b else 0 := by
          apply Finset.sum_congr rfl; intro x _; split_ifs <;> simp
  calc (∑ x, C.wire g x • qf x)
      = ∑ x, ∑ b : (reduced C).Gate, if b = toC' C x then C.wire g x • q' b else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Fintype.sum_ite_eq' (toC' C x) (fun b => C.wire g x • q' b)]
        by_cases hw : 0 < C.wire g x
        · rw [hagree x hw]
        · simp [Nat.le_zero.mp (Nat.not_lt.mp hw)]
    _ = ∑ x, ∑ b : (reduced C).Gate, if Equiv C x b.1 then C.wire g x • q' b else 0 := by
        apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro b _
        rw [show (b = toC' C x) = Equiv C x b.1 from propext toC'_eq_iff]
    _ = ∑ b : (reduced C).Gate, ∑ x, if Equiv C x b.1 then C.wire g x • q' b else 0 :=
        Finset.sum_comm
    _ = ∑ b : (reduced C).Gate, (reduced C).wire (toC' C g) b • q' b := by
        apply Finset.sum_congr rfl; intro b _; exact (hstep1 b).symm

/-- Regrouping a product over the children of `g` by equivalence class: the product of powers
`(qf x) ^ wire g x` over all children `x` equals the product of powers `(q' b) ^ wire' (toC' g) b`
over the classes `b`, provided `q'` agrees with `qf` on classes of children. -/
theorem regroup_prod (C : Circuit V K) (g : C.Gate) (qf : C.Gate → MvPolynomial V K)
    (q' : (reduced C).Gate → MvPolynomial V K)
    (hagree : ∀ x, 0 < C.wire g x → q' (toC' C x) = qf x) :
    (∏ x, (qf x) ^ C.wire g x) =
      ∏ b : (reduced C).Gate, (q' b) ^ (reduced C).wire (toC' C g) b := by
  have hstep1 : ∀ b : (reduced C).Gate, (q' b) ^ (reduced C).wire (toC' C g) b =
      ∏ x, if Equiv C x b.1 then (q' b) ^ C.wire g x else 1 := by
    intro b
    calc (q' b) ^ (reduced C).wire (toC' C g) b = (q' b) ^ W C g b.1 := by rw [wire_toC'_eq]
      _ = (q' b) ^ (∑ x, if Equiv C x b.1 then C.wire g x else 0) := rfl
      _ = ∏ x, (q' b) ^ (if Equiv C x b.1 then C.wire g x else 0) :=
          (Finset.prod_pow_eq_pow_sum _ _ _).symm
      _ = ∏ x, if Equiv C x b.1 then (q' b) ^ C.wire g x else 1 := by
          apply Finset.prod_congr rfl; intro x _; split_ifs <;> simp
  calc (∏ x, (qf x) ^ C.wire g x)
      = ∏ x, ∏ b : (reduced C).Gate, if b = toC' C x then (q' b) ^ C.wire g x else 1 := by
        apply Finset.prod_congr rfl
        intro x _
        rw [Fintype.prod_ite_eq' (toC' C x) (fun b => (q' b) ^ C.wire g x)]
        by_cases hw : 0 < C.wire g x
        · rw [hagree x hw]
        · simp [Nat.le_zero.mp (Nat.not_lt.mp hw)]
    _ = ∏ x, ∏ b : (reduced C).Gate, if Equiv C x b.1 then (q' b) ^ C.wire g x else 1 := by
        apply Finset.prod_congr rfl; intro x _; apply Finset.prod_congr rfl; intro b _
        rw [show (b = toC' C x) = Equiv C x b.1 from propext toC'_eq_iff]
    _ = ∏ b : (reduced C).Gate, ∏ x, if Equiv C x b.1 then (q' b) ^ C.wire g x else 1 :=
        Finset.prod_comm
    _ = ∏ b : (reduced C).Gate, (q' b) ^ (reduced C).wire (toC' C g) b := by
        apply Finset.prod_congr rfl; intro b _; exact (hstep1 b).symm

/-- `C'` computes, at every gate, the polynomial that the corresponding gate of `C` computes. -/
theorem computesAt_transfer (C : Circuit V K) :
    ∀ (g : C.Gate) {q : MvPolynomial V K}, C.ComputesAt g q →
      (reduced C).ComputesAt (toC' C g) q := by
  intro g
  induction g using (wellFounded_child C).induction with
  | _ g ih =>
    intro q hq
    have hlabel : (reduced C).label (toC' C g) = C.label g :=
      (equiv_label_eq C (rep_equiv C g)).symm
    cases hq with
    | var hl => exact Circuit.ComputesAt.var (hlabel.trans hl)
    | const hl => exact Circuit.ComputesAt.const (hlabel.trans hl)
    | add qf hl hqf =>
      obtain ⟨q', hq'A, hq'B⟩ := transfer_aux C ih hqf
      rw [regroup_sum C g qf q' hq'B]
      exact Circuit.ComputesAt.add q' (hlabel.trans hl) hq'A
    | mul qf hl hqf =>
      obtain ⟨q', hq'A, hq'B⟩ := transfer_aux C ih hqf
      rw [regroup_prod C g qf q' hq'B]
      exact Circuit.ComputesAt.mul q' (hlabel.trans hl) hq'A

/-- `C'` computes the same polynomial as `C`. -/
theorem computes_transfer (C : Circuit V K) {p : MvPolynomial V K} (hp : C.Computes p) :
    (reduced C).Computes p := by
  have := computesAt_transfer C C.out hp
  have hout : toC' C C.out = (reduced C).out := by
    apply Subtype.ext
    show rep C C.out = rep C C.out
    rfl
  rwa [hout] at this

end Lax461425Proofs.RigidComputes
