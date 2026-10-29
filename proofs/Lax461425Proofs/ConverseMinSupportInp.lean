import Lax461425Proofs.ConverseMinSupportS

/-!
**Step 1 of `thm:converse`'s support-depth item, for input gates.** The minimal support of
`toC' C₀ (CGate.inp i j)` is exactly `gatePoints N n (CGate.inp i j) = {Sum.inl i, Sum.inr j}`.
This is the easy case: the gate's own label `var (i, j)` is itself an invariant that no
automorphism moving `i` or `j` (while fixing everything else) can preserve, so a much simpler
"swap and compare labels" argument suffices (no polynomial evaluation needed).
-/

namespace Lax461425Proofs

open Classical Lax461425.Circuits Lax461425.HomomorphismPolynomials Lax461425.Forestwidth
open Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.RigidConstruction Lax461425Proofs.RigidRep Lax461425Proofs.RigidEquiv
open Lax461425Proofs.RigidSymmetric Lax461425Proofs.PatternsSupportAction
open Lax461425Proofs.PatternsSupportBasic

variable {F : Pattern} {Δ k : ℕ}

section EquivOfToC'

variable {V K : Type*} [CommSemiring K] {C : Circuit V K}

/-- If two gates have the same image under `toC'`, they are `Equiv`-related. -/
theorem equiv_of_toC'_eq {x y : C.Gate} (h : toC' C x = toC' C y) : Equiv C x y :=
  equiv_of_rep_eq C (congrArg Subtype.val h)

end EquivOfToC'

section MinSupportInp

variable (N : NormDecomp F Δ k) (n : ℕ) {K : Type*} [Field K] [CharZero K] (hn0 : 0 < n)
  (hE : ∃ a b, F.mult a b ≠ 0)

/-- **The hard direction, for input gates.** Every point of
`gatePoints N n (CGate.inp i j) = {Sum.inl i, Sum.inr j}` lies in the minimal support of
`toC' C₀ (CGate.inp i j)`. -/
theorem gatePoints_subset_minSupport_inp (hk2 : 2 ≤ k) (hn : 2 * k < n)
    (hrig : IsRigid (reduced (circuit N n K hn0 hE))) (i j : Fin n) :
    (gatePoints N n (CGate.inp i j) : Set (Fin n ⊕ Fin n)) ⊆
      minSupport (reduced (circuit N n K hn0 hE))
        (toC' (circuit N n K hn0 hE) (CGate.inp i j)) := by
  set C₀ := circuit N n K hn0 hE with hC₀
  intro p0 hp0
  intro T hTsupp hTcard
  by_contra hp0T
  have hTcardk : T.ncard ≤ k :=
    le_trans hTcard (supportSize_reduced_le N n hn0 hE hk2 hrig)
  have hp0F : p0 ∈ gatePoints N n (CGate.inp i j) := Finset.mem_coe.mp hp0
  have hp0cases : p0 = Sum.inl i ∨ p0 = Sum.inr j := by
    simpa [gatePoints] using hp0F
  rcases hp0cases with hpi | hpj
  · subst hpi
    have hne : leftPart T ∪ ({i} : Set (Fin n)) ≠ (Set.univ : Set (Fin n)) := by
      intro hcon
      have h1 : (leftPart T ∪ ({i} : Set (Fin n))).ncard = n := by
        rw [hcon, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
      have h2 : (leftPart T ∪ ({i} : Set (Fin n))).ncard ≤ (leftPart T).ncard + 1 := by
        calc (leftPart T ∪ ({i} : Set (Fin n))).ncard
            ≤ (leftPart T).ncard + ({i} : Set (Fin n)).ncard := Set.ncard_union_le _ _
          _ = (leftPart T).ncard + 1 := by rw [Set.ncard_singleton]
      have h3 := ncard_leftPart_le T
      omega
    obtain ⟨i1, hi1⟩ : ∃ i1, i1 ∉ leftPart T ∪ ({i} : Set (Fin n)) := by
      by_contra hcon2
      push_neg at hcon2
      exact hne (Set.eq_univ_of_forall (fun x => by simpa using hcon2 x))
    have hi1T : Sum.inl i1 ∉ T := fun hc => hi1 (Set.mem_union_left _ hc)
    have hi1ne : i1 ≠ i := fun hc => hi1 (Set.mem_union_right _ (Set.mem_singleton_iff.mpr hc))
    have hp0T'' : Sum.inl i ∉ T := hp0T
    have hfixT : ∀ x ∈ T, actPoint (swapLeft i i1) x = x :=
      actPoint_swapLeft_fixes hp0T'' hi1T
    have hfixed : σOf hrig (swapLeft i i1) (toC' C₀ (CGate.inp i j)) = toC' C₀ (CGate.inp i j) :=
      hTsupp (swapLeft i i1) (σOf hrig (swapLeft i i1)) hfixT (σOf_extends hrig _)
    have hstep := σOf_apply_toC' N n hn0 hE hrig (swapLeft i i1) (CGate.inp i j)
    have heqgate : toC' C₀ (CGate.inp i j) = toC' C₀ (CGate.inp i1 j) := by
      have : actGate N n (swapLeft i i1) (CGate.inp i j) = CGate.inp i1 j := by
        show CGate.inp ((swapLeft i i1).1 i) ((swapLeft i i1).2 j) = CGate.inp i1 j
        congr 1
        show Equiv.swap i i1 i = i1
        exact Equiv.swap_apply_left i i1
      rw [this] at hstep
      exact hfixed.symm.trans hstep
    have heqv : Equiv C₀ (CGate.inp i j) (CGate.inp i1 j) := equiv_of_toC'_eq heqgate
    have hlabel : C₀.label (CGate.inp i j) = C₀.label (CGate.inp i1 j) :=
      equiv_label_eq C₀ heqv
    have heq2 : (i, j) = (i1, j) := GateLabel.var.inj hlabel
    exact hi1ne (congrArg Prod.fst heq2).symm
  · subst hpj
    have hne : rightPart T ∪ ({j} : Set (Fin n)) ≠ (Set.univ : Set (Fin n)) := by
      intro hcon
      have h1 : (rightPart T ∪ ({j} : Set (Fin n))).ncard = n := by
        rw [hcon, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
      have h2 : (rightPart T ∪ ({j} : Set (Fin n))).ncard ≤ (rightPart T).ncard + 1 := by
        calc (rightPart T ∪ ({j} : Set (Fin n))).ncard
            ≤ (rightPart T).ncard + ({j} : Set (Fin n)).ncard := Set.ncard_union_le _ _
          _ = (rightPart T).ncard + 1 := by rw [Set.ncard_singleton]
      have h3 := ncard_rightPart_le T
      omega
    obtain ⟨j1, hj1⟩ : ∃ j1, j1 ∉ rightPart T ∪ ({j} : Set (Fin n)) := by
      by_contra hcon2
      push_neg at hcon2
      exact hne (Set.eq_univ_of_forall (fun x => by simpa using hcon2 x))
    have hj1T : Sum.inr j1 ∉ T := fun hc => hj1 (Set.mem_union_left _ hc)
    have hj1ne : j1 ≠ j := fun hc => hj1 (Set.mem_union_right _ (Set.mem_singleton_iff.mpr hc))
    have hp0T'' : Sum.inr j ∉ T := hp0T
    have hfixT : ∀ x ∈ T, actPoint (swapRight j j1) x = x :=
      actPoint_swapRight_fixes hp0T'' hj1T
    have hfixed :
        σOf hrig (swapRight j j1) (toC' C₀ (CGate.inp i j)) = toC' C₀ (CGate.inp i j) :=
      hTsupp (swapRight j j1) (σOf hrig (swapRight j j1)) hfixT (σOf_extends hrig _)
    have hstep := σOf_apply_toC' N n hn0 hE hrig (swapRight j j1) (CGate.inp i j)
    have heqgate : toC' C₀ (CGate.inp i j) = toC' C₀ (CGate.inp i j1) := by
      have : actGate N n (swapRight j j1) (CGate.inp i j) = CGate.inp i j1 := by
        show CGate.inp ((swapRight j j1).1 i) ((swapRight j j1).2 j) = CGate.inp i j1
        congr 1
        show Equiv.swap j j1 j = j1
        exact Equiv.swap_apply_left j j1
      rw [this] at hstep
      exact hfixed.symm.trans hstep
    have heqv : Equiv C₀ (CGate.inp i j) (CGate.inp i j1) := equiv_of_toC'_eq heqgate
    have hlabel : C₀.label (CGate.inp i j) = C₀.label (CGate.inp i j1) :=
      equiv_label_eq C₀ heqv
    have heq2 : (i, j) = (i, j1) := GateLabel.var.inj hlabel
    exact hj1ne (congrArg Prod.snd heq2).symm

/-- **Step 1 for input gates, complete.** The minimal support of `toC' C₀ (CGate.inp i j)` in
the reduced circuit is exactly `gatePoints N n (CGate.inp i j) = {Sum.inl i, Sum.inr j}`. -/
theorem minSupport_inp_eq (hk2 : 2 ≤ k) (hn : 2 * k < n)
    (hrig : IsRigid (reduced (circuit N n K hn0 hE))) (i j : Fin n) :
    minSupport (reduced (circuit N n K hn0 hE)) (toC' (circuit N n K hn0 hE) (CGate.inp i j)) =
      (gatePoints N n (CGate.inp i j) : Set (Fin n ⊕ Fin n)) :=
  Set.Subset.antisymm
    (minSupport_subset_of_isSupport_le hrig (isSupport_toC' N n hn0 hE hrig (CGate.inp i j))
      (by rw [Set.ncard_coe_finset]; exact card_gatePoints_le N n hk2 (CGate.inp i j))
      (supportSize_reduced_le N n hn0 hE hk2 hrig) hn)
    (gatePoints_subset_minSupport_inp N n hn0 hE hk2 hn hrig i j)

end MinSupportInp

end Lax461425Proofs
