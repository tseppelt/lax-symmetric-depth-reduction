import Lax461425Proofs.RigidConstruction

/-!
Helper material for the rigidification proof: the reduced circuit `C'` is indeed reduced.
-/

namespace Lax461425Proofs.RigidReduced

open Lax461425.Circuits RigidHeight RigidEquiv RigidWeight RigidRep RigidConstruction

open scoped Classical

variable {V K : Type*} (C : Circuit V K)

/-- The reduced circuit `C'` is reduced: no two distinct gates carry the same label and, for
internal gates, the same multiset of children. -/
theorem isReduced_reduced : (reduced C).IsReduced := by
  constructor
  · intro p p' hinput heqlabel
    have hp : rep C p.1 = p.1 := isLive_rep_self C p.2
    have hp' : rep C p'.1 = p'.1 := isLive_rep_self C p'.2
    have heqlabel' : C.label p.1 = C.label p'.1 := heqlabel
    have hh0 : height C p.1 = 0 := height_isInput C hinput
    have hh0' : height C p'.1 = 0 :=
      height_isInput C (show (C.label p'.1).IsInput from heqlabel' ▸ hinput)
    have hEquiv : Equiv C p.1 p'.1 := by
      show EquivRel C (height C p.1) p.1 p'.1
      rw [hh0]
      exact ⟨heqlabel', hh0, hh0'⟩
    have hreq := rep_eq_of_equiv C hEquiv
    rw [hp, hp'] at hreq
    exact Subtype.ext hreq
  · intro p p' _hninput heqlabel heqwire
    have hp : rep C p.1 = p.1 := isLive_rep_self C p.2
    have hp' : rep C p'.1 = p'.1 := isLive_rep_self C p'.2
    have heqlabel' : C.label p.1 = C.label p'.1 := heqlabel
    have heqwire' : ∀ b : (reduced C).Gate, (reduced C).wire p b = (reduced C).wire p' b :=
      fun b => congrFun heqwire b
    have hheight : height C p.1 = height C p'.1 := by
      have e1 := height_eq_toC' C p.1
      have e2 := height_eq_toC' C p'.1
      rw [toC'_self] at e1
      rw [toC'_self] at e2
      rw [e1, e2]
      apply Finset.sup_congr rfl
      intro b _
      rw [heqwire' b]
    have hWfull : ∀ c, W C p.1 c = W C p'.1 c :=
      W_match_all_of_live C p.2 p'.2 (fun b => by
        have h := heqwire' b
        rwa [reduced_wire, reduced_wire] at h)
    rcases Nat.eq_zero_or_pos (height C p.1) with h0 | hpos
    · have h0' : height C p'.1 = 0 := by rw [← hheight]; exact h0
      have hEquiv : Equiv C p.1 p'.1 := by
        show EquivRel C (height C p.1) p.1 p'.1
        rw [h0]
        exact ⟨heqlabel', h0, h0'⟩
      have hreq := rep_eq_of_equiv C hEquiv
      rw [hp, hp'] at hreq
      exact Subtype.ext hreq
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hgk : height C p.1 = k + 1 := hk
      have hgk' : height C p'.1 = k + 1 := by rw [← hheight]; exact hgk
      have hcond : ∀ b : C.Gate, height C b ≤ k →
          (∑ h, if EquivRel C k h b then C.wire p.1 h else 0) =
            (∑ h, if EquivRel C k h b then C.wire p'.1 h else 0) := by
        intro b _
        rw [sum_equivRel_eq_W C (g := p.1) (b := b) (k := k) (by omega),
          sum_equivRel_eq_W C (g := p'.1) (b := b) (k := k) (by omega)]
        exact hWfull b
      have hnew : EquivRel C (k + 1) p.1 p'.1 := Or.inr ⟨heqlabel', hgk, hgk', hcond⟩
      have hEquiv : Equiv C p.1 p'.1 := by
        show EquivRel C (height C p.1) p.1 p'.1
        rw [hgk]
        exact hnew
      have hreq := rep_eq_of_equiv C hEquiv
      rw [hp, hp'] at hreq
      exact Subtype.ext hreq

end Lax461425Proofs.RigidReduced
