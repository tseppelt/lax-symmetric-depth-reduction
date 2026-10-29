import Lax461425Proofs.ConverseSupportSize
import Lax461425Proofs.ConverseSubtreeInduction
import Lax461425Proofs.RigidComputes
import Mathlib.Algebra.MvPolynomial.Eval

/-!
**Step 1 of `thm:converse`'s support-depth item, for `R`-gates.** We show that the minimal
support of `toC' C₀ (CGate.R t γ)` (in the reduced circuit) is *exactly* `gatePoints N n
(CGate.R t γ) = γ(β(t))`, not just contained in it (the easy direction, from
`minSupport_subset_of_isSupport_le`).

The hard direction (every point of `γ(β(t))` lies in the minimal support) is the paper's
transposition/monomial-coverage argument: if some point `p0 ∈ γ(β(t))` were missing from the
minimal support, there is a *bounded* support `T` of `toC' C₀ (R t γ)` missing `p0`; intersecting
with `γ(β(t))` itself gives a bounded support `T' ⊆ γ(β(t))` still missing `p0`. Picking a fresh
point `p1` on the same side as `p0` but outside `γ(β(t))`, the transposition `τ` swapping `p0,p1`
fixes `T'` pointwise, hence (rigidity) the automorphism `σOf hrig τ` fixes `toC' C₀ (R t γ)`,
hence (via `σOf_apply_toC'` and the `RigidComputes` correctness-transfer machinery) the
polynomials `P t γ` and `P t (actAdm τ γ)` are *literally equal*. But evaluating the variables
`X (i, j)` at `0` whenever `i = i0` (the row named by `p0`, in the case `p0` is a row point; a
dual argument handles column points) and at `1` otherwise kills every monomial of `P t γ`
(since every admissible extension on the subtree touches row `i0`, by `represented_below`), while
a suitably chosen extension of `actAdm τ γ` avoids row `i0` entirely (since no other point of
`β(t)` was named `i1` under `γ`, by the choice of `p1`), giving a nonzero evaluation on the other
side: a contradiction, since the two polynomials are equal.
-/

namespace Lax461425Proofs

open Classical Lax461425.Circuits Lax461425.HomomorphismPolynomials Lax461425.Forestwidth
open Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.RigidConstruction Lax461425Proofs.RigidRep Lax461425Proofs.RigidEquiv
open Lax461425Proofs.RigidSymmetric Lax461425Proofs.RigidComputes
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open MvPolynomial

variable {F : Pattern} {Δ k : ℕ}

section Swap

variable {n : ℕ}

/-- The transposition of `Γₙ` swapping two row indices, fixing everything else (in particular
all column indices). -/
def swapLeft (i0 i1 : Fin n) : Γ n := (Equiv.swap i0 i1, 1)

/-- The transposition of `Γₙ` swapping two column indices, fixing everything else. -/
def swapRight (j0 j1 : Fin n) : Γ n := (1, Equiv.swap j0 j1)

/-- `swapLeft i0 i1` fixes pointwise any set avoiding both `Sum.inl i0` and `Sum.inl i1`. -/
theorem actPoint_swapLeft_fixes {i0 i1 : Fin n} {S : Set (Fin n ⊕ Fin n)}
    (h0 : Sum.inl i0 ∉ S) (h1 : Sum.inl i1 ∉ S) :
    ∀ x ∈ S, actPoint (swapLeft i0 i1) x = x := by
  rintro (i | j) hx
  · show Sum.inl (Equiv.swap i0 i1 i) = Sum.inl i
    congr 1
    apply Equiv.swap_apply_of_ne_of_ne
    · rintro rfl; exact h0 hx
    · rintro rfl; exact h1 hx
  · rfl

/-- `swapRight j0 j1` fixes pointwise any set avoiding both `Sum.inr j0` and `Sum.inr j1`. -/
theorem actPoint_swapRight_fixes {j0 j1 : Fin n} {S : Set (Fin n ⊕ Fin n)}
    (h0 : Sum.inr j0 ∉ S) (h1 : Sum.inr j1 ∉ S) :
    ∀ x ∈ S, actPoint (swapRight j0 j1) x = x := by
  rintro (i | j) hx
  · rfl
  · show Sum.inr (Equiv.swap j0 j1 j) = Sum.inr j
    congr 1
    apply Equiv.swap_apply_of_ne_of_ne
    · rintro rfl; exact h0 hx
    · rintro rfl; exact h1 hx

/-- Given a point `Sum.inl i0` of a Finset `g` of size `≤ k` with `2 * k < n`, there is a fresh
row index `i1 ≠ i0` with `Sum.inl i1 ∉ g`. -/
theorem exists_fresh_left {g : Finset (Fin n ⊕ Fin n)} {i0 : Fin n} (hi0 : Sum.inl i0 ∈ g)
    {k : ℕ} (hgk : g.card ≤ k) (hn : 2 * k < n) :
    ∃ i1 : Fin n, i1 ≠ i0 ∧ Sum.inl i1 ∉ g := by
  classical
  set L : Finset (Fin n) := Finset.univ.filter (fun i => Sum.inl i ∈ g) with hL
  have hLcard : L.card ≤ g.card := by
    apply Finset.card_le_card_of_injOn (f := Sum.inl) (s := L) (t := g)
    · intro a ha; exact (Finset.mem_filter.mp ha).2
    · exact fun a _ b _ h => Sum.inl_injective h
  have hlt : L.card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨i1, -, hi1⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hi1' : Sum.inl i1 ∉ g := fun hc => hi1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  exact ⟨i1, fun h => hi1' (h ▸ hi0), hi1'⟩

/-- Given a point `Sum.inr j0` of a Finset `g` of size `≤ k` with `2 * k < n`, there is a fresh
column index `j1 ≠ j0` with `Sum.inr j1 ∉ g`. -/
theorem exists_fresh_right {g : Finset (Fin n ⊕ Fin n)} {j0 : Fin n} (hj0 : Sum.inr j0 ∈ g)
    {k : ℕ} (hgk : g.card ≤ k) (hn : 2 * k < n) :
    ∃ j1 : Fin n, j1 ≠ j0 ∧ Sum.inr j1 ∉ g := by
  classical
  set L : Finset (Fin n) := Finset.univ.filter (fun j => Sum.inr j ∈ g) with hL
  have hLcard : L.card ≤ g.card := by
    apply Finset.card_le_card_of_injOn (f := Sum.inr) (s := L) (t := g)
    · intro a ha; exact (Finset.mem_filter.mp ha).2
    · exact fun a _ b _ h => Sum.inr_injective h
  have hlt : L.card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨j1, -, hj1⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hj1' : Sum.inr j1 ∉ g := fun hc => hj1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  exact ⟨j1, fun h => hj1' (h ▸ hj0), hj1'⟩

end Swap

section Eval

variable (N : NormDecomp F Δ k) (n : ℕ) {K : Type*} [Field K] [CharZero K]

/-- The evaluation killing every variable in row `i0`. -/
def evalRow (i0 : Fin n) : Fin n × Fin n → K := fun p => if p.1 = i0 then 0 else 1

/-- The evaluation killing every variable in column `j0`. -/
def evalCol (j0 : Fin n) : Fin n × Fin n → K := fun p => if p.2 = j0 then 0 else 1

/-- If some edge represented at-or-below `t0`, under `h`, has its left endpoint equal to `i0`,
then `Gval t0 h` evaluates to `0` under `evalRow i0`. -/
theorem eval_evalRow_Gval_eq_zero {t0 : N.Node} {h : Adm F n (V N t0)} {ab0 : F.A × F.B}
    (hab0 : ab0 ∈ edgesBelow N t0) {i0 : Fin n}
    (heq : h ⟨Sum.inl ab0.1, mem_V_left N hab0⟩ = i0) :
    eval (evalRow n i0) (Gval N n (K := K) t0 h) = 0 := by
  rw [Gval, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_attach (edgesBelow N t0) ⟨ab0, hab0⟩)
  rw [eval_pow, eval_X, evalRow, if_pos heq]
  exact zero_pow ((mem_edgesBelow_iff N).mp hab0).1

/-- If every edge represented at-or-below `t0`, under `h`, has its left endpoint `≠ i0`, then
`Gval t0 h` evaluates to `1` under `evalRow i0`. -/
theorem eval_evalRow_Gval_eq_one {t0 : N.Node} {h : Adm F n (V N t0)} {i0 : Fin n}
    (hne : ∀ ab : F.A × F.B, (hab : ab ∈ edgesBelow N t0) →
      h ⟨Sum.inl ab.1, mem_V_left N hab⟩ ≠ i0) :
    eval (evalRow n i0) (Gval N n (K := K) t0 h) = 1 := by
  rw [Gval, eval_prod]
  apply Finset.prod_eq_one
  rintro ⟨ab, hab⟩ -
  rw [eval_pow, eval_X, evalRow, if_neg (hne ab hab)]
  exact one_pow _

/-- `Gval t0 h` evaluates to `0` or `1` under `evalRow i0`, for any `h`. -/
theorem eval_evalRow_Gval_mem {t0 : N.Node} (h : Adm F n (V N t0)) (i0 : Fin n) :
    eval (evalRow n i0) (Gval N n (K := K) t0 h) = 0 ∨
      eval (evalRow n i0) (Gval N n (K := K) t0 h) = 1 := by
  rw [Gval, eval_prod]
  apply Finset.prod_induction _ (fun x => x = 0 ∨ x = 1)
  · rintro a b (rfl | rfl) (rfl | rfl) <;> simp
  · exact Or.inr rfl
  · rintro ⟨ab, hab⟩ -
    rw [eval_pow, eval_X, evalRow]
    by_cases hc : h ⟨Sum.inl ab.1, mem_V_left N hab⟩ = i0
    · rw [if_pos hc]
      exact Or.inl (zero_pow ((mem_edgesBelow_iff N).mp hab).1)
    · rw [if_neg hc]
      exact Or.inr (one_pow _)

/-- The column analogue of `eval_evalRow_Gval_eq_zero`. -/
theorem eval_evalCol_Gval_eq_zero {t0 : N.Node} {h : Adm F n (V N t0)} {ab0 : F.A × F.B}
    (hab0 : ab0 ∈ edgesBelow N t0) {j0 : Fin n}
    (heq : h ⟨Sum.inr ab0.2, mem_V_right N hab0⟩ = j0) :
    eval (evalCol n j0) (Gval N n (K := K) t0 h) = 0 := by
  rw [Gval, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_attach (edgesBelow N t0) ⟨ab0, hab0⟩)
  rw [eval_pow, eval_X, evalCol, if_pos heq]
  exact zero_pow ((mem_edgesBelow_iff N).mp hab0).1

/-- The column analogue of `eval_evalRow_Gval_eq_one`. -/
theorem eval_evalCol_Gval_eq_one {t0 : N.Node} {h : Adm F n (V N t0)} {j0 : Fin n}
    (hne : ∀ ab : F.A × F.B, (hab : ab ∈ edgesBelow N t0) →
      h ⟨Sum.inr ab.2, mem_V_right N hab⟩ ≠ j0) :
    eval (evalCol n j0) (Gval N n (K := K) t0 h) = 1 := by
  rw [Gval, eval_prod]
  apply Finset.prod_eq_one
  rintro ⟨ab, hab⟩ -
  rw [eval_pow, eval_X, evalCol, if_neg (hne ab hab)]
  exact one_pow _

/-- The column analogue of `eval_evalRow_Gval_mem`. -/
theorem eval_evalCol_Gval_mem {t0 : N.Node} (h : Adm F n (V N t0)) (j0 : Fin n) :
    eval (evalCol n j0) (Gval N n (K := K) t0 h) = 0 ∨
      eval (evalCol n j0) (Gval N n (K := K) t0 h) = 1 := by
  rw [Gval, eval_prod]
  apply Finset.prod_induction _ (fun x => x = 0 ∨ x = 1)
  · rintro a b (rfl | rfl) (rfl | rfl) <;> simp
  · exact Or.inr rfl
  · rintro ⟨ab, hab⟩ -
    rw [eval_pow, eval_X, evalCol]
    by_cases hc : h ⟨Sum.inr ab.2, mem_V_right N hab⟩ = j0
    · rw [if_pos hc]
      exact Or.inl (zero_pow ((mem_edgesBelow_iff N).mp hab).1)
    · rw [if_neg hc]
      exact Or.inr (one_pow _)

/-- A finite sum of terms, each `0` or `1`, with at least one term equal to `1`, is nonzero. -/
theorem sum_ne_zero_of_mem_eq_one {ι : Type*} (s : Finset ι) (f : ι → K)
    (hb : ∀ i ∈ s, f i = 0 ∨ f i = 1) {i1 : ι} (hi1 : i1 ∈ s) (hval : f i1 = 1) :
    (∑ i ∈ s, f i) ≠ 0 := by
  classical
  have hsplit : ∑ i ∈ s, f i = ∑ i ∈ s, (if f i = 1 then (1 : K) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    rcases hb i hi with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp
  rw [hsplit, Finset.sum_boole]
  have hmem : i1 ∈ s.filter (fun i => f i = 1) := Finset.mem_filter.mpr ⟨hi1, hval⟩
  have hpos : 0 < (s.filter (fun i => f i = 1)).card := Finset.card_pos.mpr ⟨i1, hmem⟩
  exact Nat.cast_ne_zero.mpr hpos.ne'

end Eval

section MinSupportR

variable (N : NormDecomp F Δ k) (n : ℕ) {K : Type*} [Field K] [CharZero K] (hn0 : 0 < n)
  (hE : ∃ a b, F.mult a b ≠ 0)

/-- The two gates `R t γ` and `R t (actAdm n τ γ)` compute literally equal polynomials, given
that their images under `toC'` coincide (i.e. given that the gate `R t γ` is fixed, as a class,
by the canonical automorphism `σOf hrig τ`). -/
theorem P_eq_of_toC'_eq (hrig : IsRigid (reduced (circuit N n K hn0 hE))) {t : N.Node}
    {γ γ' : Adm F n (N.bag t)}
    (heq : toC' (circuit N n K hn0 hE) (CGate.R t γ') = toC' (circuit N n K hn0 hE) (CGate.R t γ)) :
    P N n (K := K) t γ' = P N n (K := K) t γ := by
  set C₀ := circuit N n K hn0 hE with hC₀
  have h1 : (reduced C₀).ComputesAt (toC' C₀ (CGate.R t γ)) (P N n (K := K) t γ) :=
    computesAt_transfer C₀ (CGate.R t γ) (computesAt_R N n hn0 hE t γ)
  have h2 : (reduced C₀).ComputesAt (toC' C₀ (CGate.R t γ)) (P N n (K := K) t γ') := by
    rw [← heq]
    exact computesAt_transfer C₀ (CGate.R t γ') (computesAt_R N n hn0 hE t γ')
  exact computesAt_unique (reduced C₀) (toC' C₀ (CGate.R t γ)) h2 h1

/-- **The hard direction.** Every point of `gatePoints N n (CGate.R t γ) = γ(β(t))` lies in the
minimal support of `toC' C₀ (CGate.R t γ)`. -/
theorem gatePoints_subset_minSupport_R (hk2 : 2 ≤ k) (hn : 2 * k < n)
    (hrig : IsRigid (reduced (circuit N n K hn0 hE))) (t : N.Node) (γ : Adm F n (N.bag t)) :
    (gatePoints N n (CGate.R t γ) : Set (Fin n ⊕ Fin n)) ⊆
      minSupport (reduced (circuit N n K hn0 hE)) (toC' (circuit N n K hn0 hE) (CGate.R t γ)) := by
  set C₀ := circuit N n K hn0 hE with hC₀
  intro p0 hp0
  intro T hTsupp hTcard
  by_contra hp0T
  have hTcardk : T.ncard ≤ k :=
    le_trans hTcard (supportSize_reduced_le N n hn0 hE hk2 hrig)
  have hgpcardk : (gatePoints N n (CGate.R t γ) : Set (Fin n ⊕ Fin n)).ncard ≤ k := by
    rw [Set.ncard_coe_finset]; exact card_gatePoints_le N n hk2 (CGate.R t γ)
  have hT'supp : IsSupport (reduced C₀) (toC' C₀ (CGate.R t γ))
      (T ∩ (gatePoints N n (CGate.R t γ) : Set (Fin n ⊕ Fin n))) :=
    isSupport_inter_of_card_le hrig hTsupp (isSupport_toC' N n hn0 hE hrig (CGate.R t γ))
      hTcardk hgpcardk hn
  set T' : Set (Fin n ⊕ Fin n) := T ∩ (gatePoints N n (CGate.R t γ) : Set (Fin n ⊕ Fin n))
    with hT'def
  have hT'sub : T' ⊆ (gatePoints N n (CGate.R t γ) : Set (Fin n ⊕ Fin n)) :=
    Set.inter_subset_right
  have hp0T' : p0 ∉ T' := fun hc => hp0T hc.1
  have hp0F : p0 ∈ gatePoints N n (CGate.R t γ) := Finset.mem_coe.mp hp0
  obtain ⟨x0, -, hx0⟩ := Finset.mem_image.mp
    (show p0 ∈ (N.bag t).attach.image (sideOfAdm γ) from hp0F)
  obtain ⟨a0, b0, hmult, hcase, m, hm⟩ := N.represented_below t x0.1 x0.2
  have hab0 : (a0, b0) ∈ edgesBelow N t := (mem_edgesBelow_iff N).mpr ⟨hmult, ⟨m, hm⟩⟩
  rcases hcase with hxa | hxb
  · -- `p0` is a row point `Sum.inl i0`.
    have hp0eq : p0 = Sum.inl (γ x0) := by
      rw [← hx0]; simp [sideOfAdm, hxa]
    subst hp0eq
    set i0 := γ x0 with hi0def
    have hi0mem : Sum.inl i0 ∈ gatePoints N n (CGate.R t γ) := hp0F
    obtain ⟨i1, hi1ne, hi1notmem⟩ :=
      exists_fresh_left hi0mem (card_gatePoints_le N n hk2 (CGate.R t γ)) hn
    have hp0T'' : Sum.inl i0 ∉ T' := hp0T'
    have hp1T' : Sum.inl i1 ∉ T' := fun hc => hi1notmem (hT'sub hc)
    have hfixT' : ∀ x ∈ T', actPoint (swapLeft i0 i1) x = x :=
      actPoint_swapLeft_fixes hp0T'' hp1T'
    have hfixed : σOf hrig (swapLeft i0 i1) (toC' C₀ (CGate.R t γ)) = toC' C₀ (CGate.R t γ) :=
      hT'supp (swapLeft i0 i1) (σOf hrig (swapLeft i0 i1)) hfixT' (σOf_extends hrig _)
    have hstep := σOf_apply_toC' N n hn0 hE hrig (swapLeft i0 i1) (CGate.R t γ)
    have heqgate : toC' C₀ (CGate.R t γ) =
        toC' C₀ (CGate.R t (actAdm n (swapLeft i0 i1) γ)) :=
      hfixed.symm.trans hstep
    have hPeq : P N n (K := K) t (actAdm n (swapLeft i0 i1) γ) = P N n (K := K) t γ :=
      P_eq_of_toC'_eq N n hn0 hE hrig heqgate.symm
    have heval0 : eval (evalRow n i0) (P N n (K := K) t γ) = 0 := by
      rw [P_eq_sum_ExtV N n hn0 t γ, eval_sum]
      apply Finset.sum_eq_zero
      intro h hh
      apply eval_evalRow_Gval_eq_zero N n hab0
      have hval : h ⟨x0.1, bag_subset_V N t x0.2⟩ = γ x0 :=
        congrFun ((mem_ExtV N n).mp hh) x0
      have hsub : (⟨x0.1, bag_subset_V N t x0.2⟩ : ↥(V N t)) = ⟨Sum.inl a0, mem_V_left N hab0⟩ :=
        Subtype.ext hxa
      rwa [hsub] at hval
    let defaultVal : (F.A ⊕ F.B) → Fin n := Sum.elim (fun _ => i1) (fun _ => ⟨0, hn0⟩)
    let h'0 : Adm F n (V N t) := fun v =>
      if hv : v.1 ∈ N.bag t then actAdm n (swapLeft i0 i1) γ ⟨v.1, hv⟩ else defaultVal v.1
    have hh'0mem : h'0 ∈ ExtV N n t (actAdm n (swapLeft i0 i1) γ) := by
      rw [mem_ExtV]
      funext x
      show (if hv : x.1 ∈ N.bag t then actAdm n (swapLeft i0 i1) γ ⟨x.1, hv⟩
          else defaultVal x.1) = actAdm n (swapLeft i0 i1) γ x
      rw [dif_pos x.2]
    have hsafe : ∀ ab : F.A × F.B, (hab : ab ∈ edgesBelow N t) →
        h'0 ⟨Sum.inl ab.1, mem_V_left N hab⟩ ≠ i0 := by
      intro ab hab
      by_cases hbag : (Sum.inl ab.1 : F.A ⊕ F.B) ∈ N.bag t
      · show (if hv : (Sum.inl ab.1 : F.A ⊕ F.B) ∈ N.bag t then
            actAdm n (swapLeft i0 i1) γ ⟨Sum.inl ab.1, hv⟩ else defaultVal (Sum.inl ab.1)) ≠ i0
        rw [dif_pos hbag]
        show actCoord n (swapLeft i0 i1) (Sum.inl ab.1) (γ ⟨Sum.inl ab.1, hbag⟩) ≠ i0
        simp only [actCoord, swapLeft]
        intro hcon
        have hy : γ ⟨Sum.inl ab.1, hbag⟩ = i1 :=
          (Equiv.swap i0 i1).injective (hcon.trans (Equiv.swap_apply_right i0 i1).symm)
        apply hi1notmem
        show Sum.inl i1 ∈ gatePoints N n (CGate.R t γ)
        apply Finset.mem_image.mpr
        refine ⟨⟨Sum.inl ab.1, hbag⟩, Finset.mem_attach _ _, ?_⟩
        show sideOfAdm γ ⟨Sum.inl ab.1, hbag⟩ = Sum.inl i1
        unfold sideOfAdm
        simp [hy]
      · show (if hv : (Sum.inl ab.1 : F.A ⊕ F.B) ∈ N.bag t then
            actAdm n (swapLeft i0 i1) γ ⟨Sum.inl ab.1, hv⟩ else defaultVal (Sum.inl ab.1)) ≠ i0
        rw [dif_neg hbag]
        show i1 ≠ i0
        exact hi1ne
    have heval1 : eval (evalRow n i0) (Gval N n (K := K) t h'0) = 1 :=
      eval_evalRow_Gval_eq_one N n hsafe
    have heval1' :
        eval (evalRow n i0) (P N n (K := K) t (actAdm n (swapLeft i0 i1) γ)) ≠ 0 := by
      rw [P_eq_sum_ExtV N n hn0 t (actAdm n (swapLeft i0 i1) γ), eval_sum]
      exact sum_ne_zero_of_mem_eq_one (ExtV N n t (actAdm n (swapLeft i0 i1) γ))
        (fun h => eval (evalRow n i0) (Gval N n (K := K) t h))
        (fun h _ => eval_evalRow_Gval_mem N n h i0) hh'0mem heval1
    exact heval1' (hPeq ▸ heval0)
  · -- `p0` is a column point `Sum.inr j0`.
    have hp0eq : p0 = Sum.inr (γ x0) := by
      rw [← hx0]; simp [sideOfAdm, hxb]
    subst hp0eq
    set j0 := γ x0 with hj0def
    have hj0mem : Sum.inr j0 ∈ gatePoints N n (CGate.R t γ) := hp0F
    obtain ⟨j1, hj1ne, hj1notmem⟩ :=
      exists_fresh_right hj0mem (card_gatePoints_le N n hk2 (CGate.R t γ)) hn
    have hp0T'' : Sum.inr j0 ∉ T' := hp0T'
    have hp1T' : Sum.inr j1 ∉ T' := fun hc => hj1notmem (hT'sub hc)
    have hfixT' : ∀ x ∈ T', actPoint (swapRight j0 j1) x = x :=
      actPoint_swapRight_fixes hp0T'' hp1T'
    have hfixed : σOf hrig (swapRight j0 j1) (toC' C₀ (CGate.R t γ)) = toC' C₀ (CGate.R t γ) :=
      hT'supp (swapRight j0 j1) (σOf hrig (swapRight j0 j1)) hfixT' (σOf_extends hrig _)
    have hstep := σOf_apply_toC' N n hn0 hE hrig (swapRight j0 j1) (CGate.R t γ)
    have heqgate : toC' C₀ (CGate.R t γ) =
        toC' C₀ (CGate.R t (actAdm n (swapRight j0 j1) γ)) :=
      hfixed.symm.trans hstep
    have hPeq : P N n (K := K) t (actAdm n (swapRight j0 j1) γ) = P N n (K := K) t γ :=
      P_eq_of_toC'_eq N n hn0 hE hrig heqgate.symm
    have heval0 : eval (evalCol n j0) (P N n (K := K) t γ) = 0 := by
      rw [P_eq_sum_ExtV N n hn0 t γ, eval_sum]
      apply Finset.sum_eq_zero
      intro h hh
      apply eval_evalCol_Gval_eq_zero N n hab0
      have hval : h ⟨x0.1, bag_subset_V N t x0.2⟩ = γ x0 :=
        congrFun ((mem_ExtV N n).mp hh) x0
      have hsub : (⟨x0.1, bag_subset_V N t x0.2⟩ : ↥(V N t)) = ⟨Sum.inr b0, mem_V_right N hab0⟩ :=
        Subtype.ext hxb
      rwa [hsub] at hval
    let defaultVal : (F.A ⊕ F.B) → Fin n := Sum.elim (fun _ => ⟨0, hn0⟩) (fun _ => j1)
    let h'0 : Adm F n (V N t) := fun v =>
      if hv : v.1 ∈ N.bag t then actAdm n (swapRight j0 j1) γ ⟨v.1, hv⟩ else defaultVal v.1
    have hh'0mem : h'0 ∈ ExtV N n t (actAdm n (swapRight j0 j1) γ) := by
      rw [mem_ExtV]
      funext x
      show (if hv : x.1 ∈ N.bag t then actAdm n (swapRight j0 j1) γ ⟨x.1, hv⟩
          else defaultVal x.1) = actAdm n (swapRight j0 j1) γ x
      rw [dif_pos x.2]
    have hsafe : ∀ ab : F.A × F.B, (hab : ab ∈ edgesBelow N t) →
        h'0 ⟨Sum.inr ab.2, mem_V_right N hab⟩ ≠ j0 := by
      intro ab hab
      by_cases hbag : (Sum.inr ab.2 : F.A ⊕ F.B) ∈ N.bag t
      · show (if hv : (Sum.inr ab.2 : F.A ⊕ F.B) ∈ N.bag t then
            actAdm n (swapRight j0 j1) γ ⟨Sum.inr ab.2, hv⟩ else defaultVal (Sum.inr ab.2)) ≠ j0
        rw [dif_pos hbag]
        show actCoord n (swapRight j0 j1) (Sum.inr ab.2) (γ ⟨Sum.inr ab.2, hbag⟩) ≠ j0
        simp only [actCoord, swapRight]
        intro hcon
        have hy : γ ⟨Sum.inr ab.2, hbag⟩ = j1 :=
          (Equiv.swap j0 j1).injective (hcon.trans (Equiv.swap_apply_right j0 j1).symm)
        apply hj1notmem
        show Sum.inr j1 ∈ gatePoints N n (CGate.R t γ)
        apply Finset.mem_image.mpr
        refine ⟨⟨Sum.inr ab.2, hbag⟩, Finset.mem_attach _ _, ?_⟩
        show sideOfAdm γ ⟨Sum.inr ab.2, hbag⟩ = Sum.inr j1
        unfold sideOfAdm
        simp [hy]
      · show (if hv : (Sum.inr ab.2 : F.A ⊕ F.B) ∈ N.bag t then
            actAdm n (swapRight j0 j1) γ ⟨Sum.inr ab.2, hv⟩ else defaultVal (Sum.inr ab.2)) ≠ j0
        rw [dif_neg hbag]
        show j1 ≠ j0
        exact hj1ne
    have heval1 : eval (evalCol n j0) (Gval N n (K := K) t h'0) = 1 :=
      eval_evalCol_Gval_eq_one N n hsafe
    have heval1' :
        eval (evalCol n j0) (P N n (K := K) t (actAdm n (swapRight j0 j1) γ)) ≠ 0 := by
      rw [P_eq_sum_ExtV N n hn0 t (actAdm n (swapRight j0 j1) γ), eval_sum]
      exact sum_ne_zero_of_mem_eq_one (ExtV N n t (actAdm n (swapRight j0 j1) γ))
        (fun h => eval (evalCol n j0) (Gval N n (K := K) t h))
        (fun h _ => eval_evalCol_Gval_mem N n h j0) hh'0mem heval1
    exact heval1' (hPeq ▸ heval0)

/-- **Step 1 for `R`-gates, complete.** The minimal support of `toC' C₀ (CGate.R t γ)` in the
reduced circuit is exactly `gatePoints N n (CGate.R t γ) = γ(β(t))`. -/
theorem minSupport_R_eq (hk2 : 2 ≤ k) (hn : 2 * k < n)
    (hrig : IsRigid (reduced (circuit N n K hn0 hE))) (t : N.Node) (γ : Adm F n (N.bag t)) :
    minSupport (reduced (circuit N n K hn0 hE)) (toC' (circuit N n K hn0 hE) (CGate.R t γ)) =
      (gatePoints N n (CGate.R t γ) : Set (Fin n ⊕ Fin n)) :=
  Set.Subset.antisymm
    (minSupport_subset_of_isSupport_le hrig (isSupport_toC' N n hn0 hE hrig (CGate.R t γ))
      (by rw [Set.ncard_coe_finset]; exact card_gatePoints_le N n hk2 (CGate.R t γ))
      (supportSize_reduced_le N n hn0 hE hk2 hrig) hn)
    (gatePoints_subset_minSupport_R N n hn0 hE hk2 hn hrig t γ)

end MinSupportR

end Lax461425Proofs
