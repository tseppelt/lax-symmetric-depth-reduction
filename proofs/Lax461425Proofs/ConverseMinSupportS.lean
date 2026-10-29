import Lax461425Proofs.ConverseMinSupportR

/-!
**Step 1 of `thm:converse`'s support-depth item, for `S`-gates.** The analogue of
`ConverseMinSupportR.lean`'s `minSupport_R_eq` for sum gates: the minimal support of
`toC' C₀ (CGate.S c δ)` is exactly `gatePoints N n (CGate.S c δ) = δ(β(parent c) ∩ β(c))`.

The argument is the same transposition/monomial-coverage argument as for `R`-gates, applied at
the node `c` instead of `t`, with the admissible map's domain shrunk from `β(c)` to
`β(parent c) ∩ β(c)` (via `Q_eq_sum_ExtVchild` in place of `P_eq_sum_ExtV`, and `ExtVchild` in
place of `ExtV`): every point of `β(parent c) ∩ β(c)` is still a vertex of `β(c)`, so
`represented_below` at `c` still applies, and the swap/eval machinery of
`ConverseMinSupportR.lean` transfers verbatim.
-/

namespace Lax461425Proofs

open Classical Lax461425.Circuits Lax461425.HomomorphismPolynomials Lax461425.Forestwidth
open Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.RigidConstruction Lax461425Proofs.RigidRep Lax461425Proofs.RigidEquiv
open Lax461425Proofs.RigidSymmetric Lax461425Proofs.RigidComputes
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open MvPolynomial

variable {F : Pattern} {Δ k : ℕ}

section MinSupportS

variable (N : NormDecomp F Δ k) (n : ℕ) {K : Type*} [Field K] [CharZero K] (hn0 : 0 < n)
  (hE : ∃ a b, F.mult a b ≠ 0)

/-- The two gates `S c δ` and `S c (actAdm n τ δ)` compute literally equal polynomials, given
that their images under `toC'` coincide. -/
theorem Q_eq_of_toC'_eq (hrig : IsRigid (reduced (circuit N n K hn0 hE))) {c : NonRoot N}
    {δ δ' : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1)}
    (heq : toC' (circuit N n K hn0 hE) (CGate.S c δ') = toC' (circuit N n K hn0 hE) (CGate.S c δ)) :
    Q N n (K := K) c δ' = Q N n (K := K) c δ := by
  set C₀ := circuit N n K hn0 hE with hC₀
  have h1 : (reduced C₀).ComputesAt (toC' C₀ (CGate.S c δ)) (Q N n (K := K) c δ) :=
    computesAt_transfer C₀ (CGate.S c δ) (computesAt_S N n hn0 hE c δ)
  have h2 : (reduced C₀).ComputesAt (toC' C₀ (CGate.S c δ)) (Q N n (K := K) c δ') := by
    rw [← heq]
    exact computesAt_transfer C₀ (CGate.S c δ') (computesAt_S N n hn0 hE c δ')
  exact computesAt_unique (reduced C₀) (toC' C₀ (CGate.S c δ)) h2 h1

/-- **The hard direction, for `S`-gates.** Every point of
`gatePoints N n (CGate.S c δ) = δ(β(parent c) ∩ β(c))` lies in the minimal support of
`toC' C₀ (CGate.S c δ)`. -/
theorem gatePoints_subset_minSupport_S (hk2 : 2 ≤ k) (hn : 2 * k < n)
    (hrig : IsRigid (reduced (circuit N n K hn0 hE))) (c : NonRoot N)
    (δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1)) :
    (gatePoints N n (CGate.S c δ) : Set (Fin n ⊕ Fin n)) ⊆
      minSupport (reduced (circuit N n K hn0 hE)) (toC' (circuit N n K hn0 hE) (CGate.S c δ)) := by
  set C₀ := circuit N n K hn0 hE with hC₀
  intro p0 hp0
  intro T hTsupp hTcard
  by_contra hp0T
  have hTcardk : T.ncard ≤ k :=
    le_trans hTcard (supportSize_reduced_le N n hn0 hE hk2 hrig)
  have hgpcardk : (gatePoints N n (CGate.S c δ) : Set (Fin n ⊕ Fin n)).ncard ≤ k := by
    rw [Set.ncard_coe_finset]; exact card_gatePoints_le N n hk2 (CGate.S c δ)
  have hT'supp : IsSupport (reduced C₀) (toC' C₀ (CGate.S c δ))
      (T ∩ (gatePoints N n (CGate.S c δ) : Set (Fin n ⊕ Fin n))) :=
    isSupport_inter_of_card_le hrig hTsupp (isSupport_toC' N n hn0 hE hrig (CGate.S c δ))
      hTcardk hgpcardk hn
  set T' : Set (Fin n ⊕ Fin n) := T ∩ (gatePoints N n (CGate.S c δ) : Set (Fin n ⊕ Fin n))
    with hT'def
  have hT'sub : T' ⊆ (gatePoints N n (CGate.S c δ) : Set (Fin n ⊕ Fin n)) :=
    Set.inter_subset_right
  have hp0T' : p0 ∉ T' := fun hc => hp0T hc.1
  have hp0F : p0 ∈ gatePoints N n (CGate.S c δ) := Finset.mem_coe.mp hp0
  obtain ⟨x0, -, hx0⟩ := Finset.mem_image.mp
    (show p0 ∈ (N.bag (N.parent c.1) ∩ N.bag c.1).attach.image (sideOfAdm δ) from hp0F)
  have hx0c : x0.1 ∈ N.bag c.1 := Finset.mem_of_mem_inter_right x0.2
  obtain ⟨a0, b0, hmult, hcase, m, hm⟩ := N.represented_below c.1 x0.1 hx0c
  have hab0 : (a0, b0) ∈ edgesBelow N c.1 := (mem_edgesBelow_iff N).mpr ⟨hmult, ⟨m, hm⟩⟩
  rcases hcase with hxa | hxb
  · -- `p0` is a row point `Sum.inl i0`.
    have hp0eq : p0 = Sum.inl (δ x0) := by
      rw [← hx0]; simp [sideOfAdm, hxa]
    subst hp0eq
    set i0 := δ x0 with hi0def
    have hi0mem : Sum.inl i0 ∈ gatePoints N n (CGate.S c δ) := hp0F
    obtain ⟨i1, hi1ne, hi1notmem⟩ :=
      exists_fresh_left hi0mem (card_gatePoints_le N n hk2 (CGate.S c δ)) hn
    have hp0T'' : Sum.inl i0 ∉ T' := hp0T'
    have hp1T' : Sum.inl i1 ∉ T' := fun hc => hi1notmem (hT'sub hc)
    have hfixT' : ∀ x ∈ T', actPoint (swapLeft i0 i1) x = x :=
      actPoint_swapLeft_fixes hp0T'' hp1T'
    have hfixed : σOf hrig (swapLeft i0 i1) (toC' C₀ (CGate.S c δ)) = toC' C₀ (CGate.S c δ) :=
      hT'supp (swapLeft i0 i1) (σOf hrig (swapLeft i0 i1)) hfixT' (σOf_extends hrig _)
    have hstep := σOf_apply_toC' N n hn0 hE hrig (swapLeft i0 i1) (CGate.S c δ)
    have heqgate : toC' C₀ (CGate.S c δ) =
        toC' C₀ (CGate.S c (actAdm n (swapLeft i0 i1) δ)) :=
      hfixed.symm.trans hstep
    have hQeq : Q N n (K := K) c (actAdm n (swapLeft i0 i1) δ) = Q N n (K := K) c δ :=
      Q_eq_of_toC'_eq N n hn0 hE hrig heqgate.symm
    have heval0 : eval (evalRow n i0) (Q N n (K := K) c δ) = 0 := by
      rw [Q_eq_sum_ExtVchild N n c δ (fun γ' => P_eq_sum_ExtV N n hn0 c.1 γ'), eval_sum]
      apply Finset.sum_eq_zero
      intro h hh
      apply eval_evalRow_Gval_eq_zero N n hab0
      have hval : h ⟨x0.1, bag_subset_V N c.1 hx0c⟩ = δ x0 :=
        (mem_ExtVchild N n).mp hh x0.1 x0.2
      have hsub : (⟨x0.1, bag_subset_V N c.1 hx0c⟩ : ↥(V N c.1)) =
          ⟨Sum.inl a0, mem_V_left N hab0⟩ := Subtype.ext hxa
      rwa [hsub] at hval
    let defaultVal : (F.A ⊕ F.B) → Fin n := Sum.elim (fun _ => i1) (fun _ => ⟨0, hn0⟩)
    let h'0 : Adm F n (V N c.1) := fun v =>
      if hv : v.1 ∈ N.bag (N.parent c.1) ∩ N.bag c.1 then
        actAdm n (swapLeft i0 i1) δ ⟨v.1, hv⟩ else defaultVal v.1
    have hh'0mem : h'0 ∈ ExtVchild N n c (actAdm n (swapLeft i0 i1) δ) := by
      rw [mem_ExtVchild]
      intro x hx
      show (if hv : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1 then
          actAdm n (swapLeft i0 i1) δ ⟨x, hv⟩ else defaultVal x) =
        actAdm n (swapLeft i0 i1) δ ⟨x, hx⟩
      rw [dif_pos hx]
    have hsafe : ∀ ab : F.A × F.B, (hab : ab ∈ edgesBelow N c.1) →
        h'0 ⟨Sum.inl ab.1, mem_V_left N hab⟩ ≠ i0 := by
      intro ab hab
      by_cases hbag : (Sum.inl ab.1 : F.A ⊕ F.B) ∈ N.bag (N.parent c.1) ∩ N.bag c.1
      · show (if hv : (Sum.inl ab.1 : F.A ⊕ F.B) ∈ N.bag (N.parent c.1) ∩ N.bag c.1 then
            actAdm n (swapLeft i0 i1) δ ⟨Sum.inl ab.1, hv⟩ else defaultVal (Sum.inl ab.1)) ≠ i0
        rw [dif_pos hbag]
        show actCoord n (swapLeft i0 i1) (Sum.inl ab.1) (δ ⟨Sum.inl ab.1, hbag⟩) ≠ i0
        simp only [actCoord, swapLeft]
        intro hcon
        have hy : δ ⟨Sum.inl ab.1, hbag⟩ = i1 :=
          (Equiv.swap i0 i1).injective (hcon.trans (Equiv.swap_apply_right i0 i1).symm)
        apply hi1notmem
        show Sum.inl i1 ∈ gatePoints N n (CGate.S c δ)
        apply Finset.mem_image.mpr
        refine ⟨⟨Sum.inl ab.1, hbag⟩, Finset.mem_attach _ _, ?_⟩
        show sideOfAdm δ ⟨Sum.inl ab.1, hbag⟩ = Sum.inl i1
        unfold sideOfAdm
        simp [hy]
      · show (if hv : (Sum.inl ab.1 : F.A ⊕ F.B) ∈ N.bag (N.parent c.1) ∩ N.bag c.1 then
            actAdm n (swapLeft i0 i1) δ ⟨Sum.inl ab.1, hv⟩ else defaultVal (Sum.inl ab.1)) ≠ i0
        rw [dif_neg hbag]
        show i1 ≠ i0
        exact hi1ne
    have heval1 : eval (evalRow n i0) (Gval N n (K := K) c.1 h'0) = 1 :=
      eval_evalRow_Gval_eq_one N n hsafe
    have heval1' :
        eval (evalRow n i0) (Q N n (K := K) c (actAdm n (swapLeft i0 i1) δ)) ≠ 0 := by
      rw [Q_eq_sum_ExtVchild N n c (actAdm n (swapLeft i0 i1) δ)
        (fun γ' => P_eq_sum_ExtV N n hn0 c.1 γ'), eval_sum]
      exact sum_ne_zero_of_mem_eq_one (ExtVchild N n c (actAdm n (swapLeft i0 i1) δ))
        (fun h => eval (evalRow n i0) (Gval N n (K := K) c.1 h))
        (fun h _ => eval_evalRow_Gval_mem N n h i0) hh'0mem heval1
    exact heval1' (hQeq ▸ heval0)
  · -- `p0` is a column point `Sum.inr j0`.
    have hp0eq : p0 = Sum.inr (δ x0) := by
      rw [← hx0]; simp [sideOfAdm, hxb]
    subst hp0eq
    set j0 := δ x0 with hj0def
    have hj0mem : Sum.inr j0 ∈ gatePoints N n (CGate.S c δ) := hp0F
    obtain ⟨j1, hj1ne, hj1notmem⟩ :=
      exists_fresh_right hj0mem (card_gatePoints_le N n hk2 (CGate.S c δ)) hn
    have hp0T'' : Sum.inr j0 ∉ T' := hp0T'
    have hp1T' : Sum.inr j1 ∉ T' := fun hc => hj1notmem (hT'sub hc)
    have hfixT' : ∀ x ∈ T', actPoint (swapRight j0 j1) x = x :=
      actPoint_swapRight_fixes hp0T'' hp1T'
    have hfixed : σOf hrig (swapRight j0 j1) (toC' C₀ (CGate.S c δ)) = toC' C₀ (CGate.S c δ) :=
      hT'supp (swapRight j0 j1) (σOf hrig (swapRight j0 j1)) hfixT' (σOf_extends hrig _)
    have hstep := σOf_apply_toC' N n hn0 hE hrig (swapRight j0 j1) (CGate.S c δ)
    have heqgate : toC' C₀ (CGate.S c δ) =
        toC' C₀ (CGate.S c (actAdm n (swapRight j0 j1) δ)) :=
      hfixed.symm.trans hstep
    have hQeq : Q N n (K := K) c (actAdm n (swapRight j0 j1) δ) = Q N n (K := K) c δ :=
      Q_eq_of_toC'_eq N n hn0 hE hrig heqgate.symm
    have heval0 : eval (evalCol n j0) (Q N n (K := K) c δ) = 0 := by
      rw [Q_eq_sum_ExtVchild N n c δ (fun γ' => P_eq_sum_ExtV N n hn0 c.1 γ'), eval_sum]
      apply Finset.sum_eq_zero
      intro h hh
      apply eval_evalCol_Gval_eq_zero N n hab0
      have hval : h ⟨x0.1, bag_subset_V N c.1 hx0c⟩ = δ x0 :=
        (mem_ExtVchild N n).mp hh x0.1 x0.2
      have hsub : (⟨x0.1, bag_subset_V N c.1 hx0c⟩ : ↥(V N c.1)) =
          ⟨Sum.inr b0, mem_V_right N hab0⟩ := Subtype.ext hxb
      rwa [hsub] at hval
    let defaultVal : (F.A ⊕ F.B) → Fin n := Sum.elim (fun _ => ⟨0, hn0⟩) (fun _ => j1)
    let h'0 : Adm F n (V N c.1) := fun v =>
      if hv : v.1 ∈ N.bag (N.parent c.1) ∩ N.bag c.1 then
        actAdm n (swapRight j0 j1) δ ⟨v.1, hv⟩ else defaultVal v.1
    have hh'0mem : h'0 ∈ ExtVchild N n c (actAdm n (swapRight j0 j1) δ) := by
      rw [mem_ExtVchild]
      intro x hx
      show (if hv : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1 then
          actAdm n (swapRight j0 j1) δ ⟨x, hv⟩ else defaultVal x) =
        actAdm n (swapRight j0 j1) δ ⟨x, hx⟩
      rw [dif_pos hx]
    have hsafe : ∀ ab : F.A × F.B, (hab : ab ∈ edgesBelow N c.1) →
        h'0 ⟨Sum.inr ab.2, mem_V_right N hab⟩ ≠ j0 := by
      intro ab hab
      by_cases hbag : (Sum.inr ab.2 : F.A ⊕ F.B) ∈ N.bag (N.parent c.1) ∩ N.bag c.1
      · show (if hv : (Sum.inr ab.2 : F.A ⊕ F.B) ∈ N.bag (N.parent c.1) ∩ N.bag c.1 then
            actAdm n (swapRight j0 j1) δ ⟨Sum.inr ab.2, hv⟩ else defaultVal (Sum.inr ab.2)) ≠ j0
        rw [dif_pos hbag]
        show actCoord n (swapRight j0 j1) (Sum.inr ab.2) (δ ⟨Sum.inr ab.2, hbag⟩) ≠ j0
        simp only [actCoord, swapRight]
        intro hcon
        have hy : δ ⟨Sum.inr ab.2, hbag⟩ = j1 :=
          (Equiv.swap j0 j1).injective (hcon.trans (Equiv.swap_apply_right j0 j1).symm)
        apply hj1notmem
        show Sum.inr j1 ∈ gatePoints N n (CGate.S c δ)
        apply Finset.mem_image.mpr
        refine ⟨⟨Sum.inr ab.2, hbag⟩, Finset.mem_attach _ _, ?_⟩
        show sideOfAdm δ ⟨Sum.inr ab.2, hbag⟩ = Sum.inr j1
        unfold sideOfAdm
        simp [hy]
      · show (if hv : (Sum.inr ab.2 : F.A ⊕ F.B) ∈ N.bag (N.parent c.1) ∩ N.bag c.1 then
            actAdm n (swapRight j0 j1) δ ⟨Sum.inr ab.2, hv⟩ else defaultVal (Sum.inr ab.2)) ≠ j0
        rw [dif_neg hbag]
        show j1 ≠ j0
        exact hj1ne
    have heval1 : eval (evalCol n j0) (Gval N n (K := K) c.1 h'0) = 1 :=
      eval_evalCol_Gval_eq_one N n hsafe
    have heval1' :
        eval (evalCol n j0) (Q N n (K := K) c (actAdm n (swapRight j0 j1) δ)) ≠ 0 := by
      rw [Q_eq_sum_ExtVchild N n c (actAdm n (swapRight j0 j1) δ)
        (fun γ' => P_eq_sum_ExtV N n hn0 c.1 γ'), eval_sum]
      exact sum_ne_zero_of_mem_eq_one (ExtVchild N n c (actAdm n (swapRight j0 j1) δ))
        (fun h => eval (evalCol n j0) (Gval N n (K := K) c.1 h))
        (fun h _ => eval_evalCol_Gval_mem N n h j0) hh'0mem heval1
    exact heval1' (hQeq ▸ heval0)

/-- **Step 1 for `S`-gates, complete.** The minimal support of `toC' C₀ (CGate.S c δ)` in the
reduced circuit is exactly `gatePoints N n (CGate.S c δ) = δ(β(parent c) ∩ β(c))`. -/
theorem minSupport_S_eq (hk2 : 2 ≤ k) (hn : 2 * k < n)
    (hrig : IsRigid (reduced (circuit N n K hn0 hE))) (c : NonRoot N)
    (δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1)) :
    minSupport (reduced (circuit N n K hn0 hE)) (toC' (circuit N n K hn0 hE) (CGate.S c δ)) =
      (gatePoints N n (CGate.S c δ) : Set (Fin n ⊕ Fin n)) :=
  Set.Subset.antisymm
    (minSupport_subset_of_isSupport_le hrig (isSupport_toC' N n hn0 hE hrig (CGate.S c δ))
      (by rw [Set.ncard_coe_finset]; exact card_gatePoints_le N n hk2 (CGate.S c δ))
      (supportSize_reduced_le N n hn0 hE hk2 hrig) hn)
    (gatePoints_subset_minSupport_S N n hn0 hE hk2 hn hrig c δ)

end MinSupportS

end Lax461425Proofs
