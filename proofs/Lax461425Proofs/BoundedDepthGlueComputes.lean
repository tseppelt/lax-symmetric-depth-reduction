import Lax461425Proofs.BoundedDepthGlueCircuit
import Lax461425Proofs.BoundedDepthProdSum
import Lax461425Proofs.RigidHeight

/-!
**The glue circuit computes the scaled sum.** Given `(D i).Computes (p i)` for every block `i`,
`glueCircuit D f` computes `∑ i, f i • p i`.
-/

namespace Lax461425Proofs

open Lax461425.Circuits RigidHeight

open scoped Classical

variable {n m : ℕ} {K : Type*} [Field K] [CharZero K] (D : Fin m → Circuit (Fin n × Fin n) K)
  (f : Fin m → K)

theorem glueCircuit_wire : (glueCircuit D f).wire = gwire D := rfl

theorem glueCircuit_label : (glueCircuit D f).label = glabel D f := rfl

/-- Every outgoing wire of a block gate `blk D i y` not landing on another block-`i` gate has
multiplicity `0`: block gates are wired only within their own block. -/
theorem blk_wire_eq_zero_of_not_blk {i : Fin m} {y : (D i).Gate} {x : GGate D}
    (hx : ∀ y' : (D i).Gate, x ≠ blk D i y') : gwire D (blk D i y) x = 0 := by
  rcases x with ⟨i', y'⟩ | i' | i' | ⟨⟩
  · rw [gwire_blk_blk]
    by_cases heq : i = i'
    · subst heq; exact absurd rfl (hx y')
    · simp [dif_neg heq]
  · exact gwire_blk_scaled D i y i'
  · exact gwire_blk_const D i y i'
  · exact gwire_blk_out D i y

theorem gwire_blk_blk_self (i : Fin m) (y y' : (D i).Gate) :
    gwire D (blk D i y) (blk D i y') = (D i).wire y y' := by
  rw [gwire_blk_blk]; simp

/-- **Lifting `ComputesAt` through a block embedding.** -/
theorem blk_computesAt_lift (i : Fin m) :
    ∀ y : (D i).Gate, ∀ {q : MvPolynomial (Fin n × Fin n) K}, (D i).ComputesAt y q →
      (glueCircuit D f).ComputesAt (blk D i y) q := by
  intro y
  induction y using (wellFounded_child (D i)).induction with
  | _ y ih =>
    intro q hq
    cases hq with
    | var hl => exact Circuit.ComputesAt.var (show (glueCircuit D f).label (blk D i y) = _ from hl)
    | const hl =>
        exact Circuit.ComputesAt.const (show (glueCircuit D f).label (blk D i y) = _ from hl)
    | add qf hl hqf =>
        set Q : GGate D → MvPolynomial (Fin n × Fin n) K :=
          fun h => match h with
            | Sum.inl ⟨j, y'⟩ => if hh : j = i then qf (hh ▸ y') else 0
            | Sum.inr _ => 0 with hQdef
        have hQblk : ∀ y' : (D i).Gate, Q (blk D i y') = qf y' := by
          intro y'
          show (if hh : i = i then qf (hh ▸ y') else 0) = qf y'
          rw [dif_pos rfl]
        have hchildren : ∀ h, 0 < (glueCircuit D f).wire (blk D i y) h →
            (glueCircuit D f).ComputesAt h (Q h) := by
          intro h hpos
          by_cases hcase : ∃ y', h = blk D i y'
          · obtain ⟨y', rfl⟩ := hcase
            have hpos' : 0 < (D i).wire y y' := by
              rwa [glueCircuit_wire, gwire_blk_blk_self] at hpos
            rw [hQblk]
            exact ih y' hpos' (hqf y' hpos')
          · push Not at hcase
            rw [glueCircuit_wire] at hpos
            exact absurd (blk_wire_eq_zero_of_not_blk D hcase) (Nat.pos_iff_ne_zero.mp hpos)
        have hval := Circuit.ComputesAt.add Q
          (show (glueCircuit D f).label (blk D i y) = .add from hl) hchildren
        have hsumeq : (∑ h, (glueCircuit D f).wire (blk D i y) h • Q h) =
            ∑ y' : (D i).Gate, (D i).wire y y' • qf y' := by
          rw [glueCircuit_wire]
          rw [sum_eq_of_vanishing_outside_image (gwire D (blk D i y))
            Q (blk D i)
            (fun x y hxy => by
              simpa using (Sum.inl_injective hxy : (⟨i, x⟩ : Σ j, (D j).Gate) = ⟨i, y⟩))
            (fun x hx => blk_wire_eq_zero_of_not_blk D hx)]
          exact Finset.sum_congr rfl (fun y' _ => by
            show gwire D (blk D i y) (blk D i y') • Q (blk D i y') = _
            rw [gwire_blk_blk_self, hQblk])
        rw [← hsumeq]
        exact hval
    | mul qf hl hqf =>
        set Q : GGate D → MvPolynomial (Fin n × Fin n) K :=
          fun h => match h with
            | Sum.inl ⟨j, y'⟩ => if hh : j = i then qf (hh ▸ y') else 1
            | Sum.inr _ => 1 with hQdef
        have hQblk : ∀ y' : (D i).Gate, Q (blk D i y') = qf y' := by
          intro y'
          show (if hh : i = i then qf (hh ▸ y') else 1) = qf y'
          rw [dif_pos rfl]
        have hchildren : ∀ h, 0 < (glueCircuit D f).wire (blk D i y) h →
            (glueCircuit D f).ComputesAt h (Q h) := by
          intro h hpos
          by_cases hcase : ∃ y', h = blk D i y'
          · obtain ⟨y', rfl⟩ := hcase
            have hpos' : 0 < (D i).wire y y' := by
              rwa [glueCircuit_wire, gwire_blk_blk_self] at hpos
            rw [hQblk]
            exact ih y' hpos' (hqf y' hpos')
          · push Not at hcase
            rw [glueCircuit_wire] at hpos
            exact absurd (blk_wire_eq_zero_of_not_blk D hcase) (Nat.pos_iff_ne_zero.mp hpos)
        have hval := Circuit.ComputesAt.mul Q
          (show (glueCircuit D f).label (blk D i y) = .mul from hl) hchildren
        have hprodeq : (∏ h, Q h ^ (glueCircuit D f).wire (blk D i y) h) =
            ∏ y' : (D i).Gate, (qf y') ^ (D i).wire y y' := by
          rw [glueCircuit_wire]
          rw [prod_eq_of_vanishing_outside_image
            (gwire D (blk D i y)) Q (blk D i)
            (fun x y hxy => by
              simpa using (Sum.inl_injective hxy : (⟨i, x⟩ : Σ j, (D j).Gate) = ⟨i, y⟩))
            (fun x hx => blk_wire_eq_zero_of_not_blk D hx)]
          exact Finset.prod_congr rfl (fun y' _ => by
            show Q (blk D i y') ^ gwire D (blk D i y) (blk D i y') = _
            rw [gwire_blk_blk_self, hQblk])
        rw [← hprodeq]
        exact hval

/-- **The `scaledG i` gate computes `(output of block i) * f i`.** -/
theorem scaledG_computesAt (i : Fin m) {p : MvPolynomial (Fin n × Fin n) K}
    (hp : (D i).Computes p) :
    (glueCircuit D f).ComputesAt (scaledG D i) (p * MvPolynomial.C (f i)) := by
  set Q : GGate D → MvPolynomial (Fin n × Fin n) K :=
    fun h => if h = blk D i (D i).out then p else if h = constG D i then MvPolynomial.C (f i)
      else 1 with hQdef
  have hab : blk D i (D i).out ≠ constG D i := by
    intro hc; cases hc
  have hchildren : ∀ h, 0 < (glueCircuit D f).wire (scaledG D i) h →
      (glueCircuit D f).ComputesAt h (Q h) := by
    intro h hpos
    rw [glueCircuit_wire] at hpos
    rcases h with ⟨i', y'⟩ | i' | i' | ⟨⟩
    · rw [gwire_scaled_blk] at hpos
      by_cases heq : i = i'
      · subst heq
        by_cases hy : y' = (D i).out
        · subst hy
          show (glueCircuit D f).ComputesAt (blk D i (D i).out)
            (if blk D i (D i).out = blk D i (D i).out then p else _)
          rw [if_pos rfl]
          exact blk_computesAt_lift D f i (D i).out hp
        · simp [hy] at hpos
      · simp [dif_neg heq] at hpos
    · rw [gwire_scaled_scaled] at hpos; omega
    · rw [gwire_scaled_const] at hpos
      by_cases heq : i = i'
      · subst heq
        show (glueCircuit D f).ComputesAt (constG D i)
          (if constG D i = blk D i (D i).out then p
            else if constG D i = constG D i then MvPolynomial.C (f i) else 1)
        rw [if_neg (by intro hc; cases hc), if_pos rfl]
        exact Circuit.ComputesAt.const rfl
      · simp [heq] at hpos
    · rw [gwire_scaled_out] at hpos; omega
  have hval := Circuit.ComputesAt.mul Q (rfl : (glueCircuit D f).label (scaledG D i) = .mul)
    hchildren
  have hprodeq : (∏ h, Q h ^ (glueCircuit D f).wire (scaledG D i) h) =
      p * MvPolynomial.C (f i) := by
    rw [glueCircuit_wire]
    have hrest : ∀ x, x ≠ blk D i (D i).out → x ≠ constG D i →
        gwire D (scaledG D i) x = 0 := by
      intro x hxa hxb
      rcases x with ⟨i', y'⟩ | i' | i' | ⟨⟩
      · rw [gwire_scaled_blk]
        by_cases heq : i = i'
        · subst heq
          rw [dif_pos rfl]
          rw [if_neg]
          intro hc; exact hxa (by rw [show (blk D i (D i).out) = Sum.inl ⟨i, (D i).out⟩ from rfl,
            hc])
        · simp [dif_neg heq]
      · rfl
      · by_cases heq : i = i'
        · subst heq; exact absurd rfl hxb
        · rw [gwire_scaled_const]; simp [heq]
      · rfl
    rw [prod_eq_of_two_support (gwire D (scaledG D i)) Q hab hrest]
    have hQa : Q (blk D i (D i).out) = p := by rw [hQdef]; simp
    have hQb : Q (constG D i) = MvPolynomial.C (f i) := by
      rw [hQdef]; simp [hab.symm]
    have hea : gwire D (scaledG D i) (blk D i (D i).out) = 1 := by
      rw [gwire_scaled_blk]; simp
    have heb : gwire D (scaledG D i) (constG D i) = 1 := by
      rw [gwire_scaled_const]; simp
    rw [hQa, hQb, hea, heb, pow_one, pow_one]
  rw [← hprodeq]
  exact hval

/-- **The glue circuit computes `∑ i, f i • p i`.** -/
theorem glueCircuit_computes {p : Fin m → MvPolynomial (Fin n × Fin n) K}
    (hp : ∀ i, (D i).Computes (p i)) :
    (glueCircuit D f).Computes (∑ i, f i • p i) := by
  set Q : GGate D → MvPolynomial (Fin n × Fin n) K :=
    fun h => if hh : ∃ i, h = scaledG D i then p hh.choose * MvPolynomial.C (f hh.choose)
      else 0 with hQdef
  have hQscaled : ∀ i, Q (scaledG D i) = p i * MvPolynomial.C (f i) := by
    intro i
    have hex : ∃ i', scaledG D i = scaledG D i' := ⟨i, rfl⟩
    show (if hh : ∃ i', scaledG D i = scaledG D i' then
        p hh.choose * MvPolynomial.C (f hh.choose) else 0) = p i * MvPolynomial.C (f i)
    rw [dif_pos hex]
    have heq : hex.choose = i := by
      have := hex.choose_spec
      simpa [scaledG] using this.symm
    rw [heq]
  have hchildren : ∀ h, 0 < (glueCircuit D f).wire (outGG D) h →
      (glueCircuit D f).ComputesAt h (Q h) := by
    intro h hpos
    rw [glueCircuit_wire] at hpos
    rcases h with ⟨i, y⟩ | i | i | ⟨⟩
    · rw [gwire_out_blk] at hpos; omega
    · rw [hQscaled]
      exact scaledG_computesAt D f i (hp i)
    · rw [gwire_out_const] at hpos; omega
    · rw [gwire_out_out] at hpos; omega
  have hval := Circuit.ComputesAt.add Q (rfl : (glueCircuit D f).label (outGG D) = .add)
    hchildren
  have hsumeq : (∑ h, (glueCircuit D f).wire (outGG D) h • Q h) = ∑ i, f i • p i := by
    rw [glueCircuit_wire]
    rw [sum_eq_of_support_image (gwire D (outGG D)) Q (scaledG D)
      (fun x y hxy => by simpa [scaledG] using hxy)
      (fun i => by show gwire D (outGG D) (scaledG D i) = 1; rw [gwire_out_scaled])
      (fun x hx => by
        rcases x with ⟨i, y⟩ | i | i | ⟨⟩
        · exact gwire_out_blk D i y
        · exact absurd rfl (hx i)
        · exact gwire_out_const D i
        · exact gwire_out_out D)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hQscaled, mul_comm, Algebra.smul_def, MvPolynomial.C_eq_algebraMap]
  show (glueCircuit D f).ComputesAt (outGG D) (∑ i, f i • p i)
  rw [← hsumeq]
  exact hval

end Lax461425Proofs
