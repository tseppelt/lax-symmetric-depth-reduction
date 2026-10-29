import Lax461425Proofs.ConverseMinSupportInp

/-!
**Step 1 and Step 2 of `thm:converse`'s support-depth item.** We show `supportDepth (reduced C₀)
≤ Δ`, where `C₀ := circuit N n K hn0 hE`.

The key device, avoiding any need to analyze the arbitrary representative `b.1` of a reduced
gate `b` (the obstruction a previous attempt got stuck on), is to track, alongside the path `p`
in `reduced C₀`, a *chosen witness chain* `w 0, w 1, …, w m : CGate N n` of literal `C₀`-gates
with `Equiv C₀ (w i) (p i).1` for every `i`, built step by step via `exists_of_W_pos` (never by
inspecting `(p i).1` itself). Since `toC' C₀ (w i) = p i` (via `toC'_eq_of_equiv`), the minimal
support of `p i` is *literally* `gatePoints N n (w i)`, computed from `w i`'s own, fully concrete,
`R`/`S`/`inp` structure via `minSupport_R_eq`/`minSupport_S_eq`/`minSupport_inp_eq` applied
directly to `w i`. This sidesteps entirely the question of whether `Equiv` identifies gates of
different tree nodes: we never need to know anything about `(p i).1`'s own representation.

Step 1 shows that wires out of an `R`-gate (into an input gate or an `S`-gate) never change the
support (`gatePoints` of the child is `⊆ gatePoints` of the parent), while wires out of an
`S`-gate (into the `R`-gate of the same node) may freely be charged `1` against the potential
`level`. Step 2 bounds the total count of such `S → R` steps on a path by `Δ`, via a potential
function `potentialOf` (the `level` of the gate's node, or `Δ` for input gates) that strictly
increases by exactly `1` at every `R → S` step (the level-increasing, non-support-changing
steps) and stays constant at every `S → R` step (the support-changing candidates), combined with
the uniform bound `level ≤ Δ`.
-/

namespace Lax461425Proofs

open Classical Lax461425.Circuits Lax461425.HomomorphismPolynomials Lax461425.Forestwidth
open Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.RigidConstruction Lax461425Proofs.RigidRep Lax461425Proofs.RigidEquiv
open Lax461425Proofs.RigidWeight Lax461425Proofs.RigidSymmetric

variable {F : Pattern} {Δ k : ℕ}

/-! ### A generic Fin-prefix counting lemma -/

section FinPrefix

variable {m : ℕ} (Q : Fin m → Prop)

/-- The number of indices `i : Fin m` with `(i : ℕ) < idx` satisfying `Q`. -/
noncomputable def prefixCount (idx : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => (i : ℕ) < idx ∧ Q i)).card

theorem prefixCount_zero : prefixCount Q 0 = 0 := by
  unfold prefixCount
  rw [Finset.card_eq_zero]
  ext j
  simp

/-- The key recursive bound: extending the prefix by one index adds at most one (exactly one, if
`Q` holds at the new index, else none) to the count. We only need the inequality. -/
theorem prefixCount_succ_le (idx : ℕ) (hidx : idx < m) :
    prefixCount Q (idx + 1) ≤ prefixCount Q idx + (if Q (⟨idx, hidx⟩ : Fin m) then 1 else 0) := by
  unfold prefixCount
  by_cases hQ : Q (⟨idx, hidx⟩ : Fin m)
  · rw [if_pos hQ]
    calc (Finset.univ.filter (fun i : Fin m => (i : ℕ) < idx + 1 ∧ Q i)).card
        ≤ (insert (⟨idx, hidx⟩ : Fin m)
            (Finset.univ.filter (fun i : Fin m => (i : ℕ) < idx ∧ Q i))).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases (by omega : (j : ℕ) < idx ∨ (j : ℕ) = idx) with h | h
          · exact Or.inr ⟨h, hj.2⟩
          · exact Or.inl
              (Fin.ext (show (j : ℕ) = (⟨idx, hidx⟩ : Fin m).val from h))
      _ ≤ _ := Finset.card_insert_le _ _
  · rw [if_neg hQ, add_zero]
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rcases (by omega : (j : ℕ) < idx ∨ (j : ℕ) = idx) with h | h
    · exact ⟨h, hj.2⟩
    · have heq : j = (⟨idx, hidx⟩ : Fin m) :=
        Fin.ext (show (j : ℕ) = (⟨idx, hidx⟩ : Fin m).val from h)
      exact absurd (heq ▸ hj.2 : Q (⟨idx, hidx⟩ : Fin m)) hQ

/-- At `idx = m`, the prefix condition `(i : ℕ) < m` is automatic, so the prefix count is the
full count. -/
theorem prefixCount_eq_card_univ : prefixCount Q m = (Finset.univ.filter Q).card := by
  unfold prefixCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨i.isLt, h⟩⟩

theorem ncard_setOf_eq_filter_card : {i : Fin m | Q i}.ncard = (Finset.univ.filter Q).card := by
  rw [← Set.ncard_coe_finset (Finset.univ.filter Q)]
  congr 1
  ext i
  simp

end FinPrefix

/-! ### Step 1: `gatePoints` containment for the non-support-changing wires out of `R`-gates -/

section Step1

variable (N : NormDecomp F Δ k) (n : ℕ)

/-- `sideOfAdm` only depends on the point and the *value* named there, not on which admissible
map or domain finset it is read off from. -/
theorem sideOfAdm_congr {S S' : Finset (F.A ⊕ F.B)} {γ : Adm F n S} {δ : Adm F n S'}
    {x : F.A ⊕ F.B} (hS : x ∈ S) (hS' : x ∈ S') (hv : γ ⟨x, hS⟩ = δ ⟨x, hS'⟩) :
    sideOfAdm γ (⟨x, hS⟩ : ↥S) = sideOfAdm δ (⟨x, hS'⟩ : ↥S') := by
  unfold sideOfAdm
  rcases x with a | b <;> simp [hv]

/-- **Step 1, input-gate case.** A positive `wireRtoInp` witnesses an edge represented at `t`
whose endpoints `γ` sends to `i, j`; both points of `gatePoints (inp i j)` are therefore already
in `gatePoints (R t γ)`. -/
theorem gatePoints_inp_subset_R {t : N.Node} {γ : Adm F n (N.bag t)} {i j : Fin n}
    (hw : 0 < wireRtoInp N n t γ i j) :
    gatePoints N n (CGate.inp i j) ⊆ gatePoints N n (CGate.R t γ) := by
  have hex : ∃ ab ∈ (edgesAt N t).attach,
      γ ⟨Sum.inl ab.1.1, mem_bag_left N ab.2⟩ = i ∧
        γ ⟨Sum.inr ab.1.2, mem_bag_right N ab.2⟩ = j := by
    by_contra hcon
    push_neg at hcon
    have hz : wireRtoInp N n t γ i j = 0 := by
      unfold wireRtoInp
      apply Finset.sum_eq_zero
      intro ab hab
      rw [if_neg (fun hc => hcon ab hab hc.1 hc.2)]
    omega
  obtain ⟨ab, hab, hi, hj⟩ := hex
  intro p hp
  simp only [gatePoints, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact Finset.mem_image.mpr
      ⟨⟨Sum.inl ab.1.1, mem_bag_left N ab.2⟩, Finset.mem_attach _ _, by simp [sideOfAdm, hi]⟩
  · exact Finset.mem_image.mpr
      ⟨⟨Sum.inr ab.1.2, mem_bag_right N ab.2⟩, Finset.mem_attach _ _, by simp [sideOfAdm, hj]⟩

/-- **Step 1, `S`-gate case.** A positive `wireRtoS` witnesses that `c`'s parent is `t` and `δ`
agrees with `γ` on the intersection; `gatePoints (S c δ)` is therefore already `⊆ gatePoints
(R t γ)`. -/
theorem gatePoints_S_subset_R {t : N.Node} {γ : Adm F n (N.bag t)} {c : NonRoot N}
    {δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1)} (hw : 0 < wireRtoS N n t γ c δ) :
    gatePoints N n (CGate.S c δ) ⊆ gatePoints N n (CGate.R t γ) := by
  unfold wireRtoS at hw
  by_cases hpar : N.parent c.1 = t
  · rw [dif_pos hpar] at hw
    by_cases hmatch : ∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
        γ ⟨x, hpar ▸ Finset.inter_subset_left hx⟩ = δ ⟨x, hx⟩
    · intro p hp
      obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hp
      apply Finset.mem_image.mpr
      refine ⟨⟨y.1, hpar ▸ Finset.inter_subset_left y.2⟩, Finset.mem_attach _ _, ?_⟩
      rw [← hy]
      exact sideOfAdm_congr n (hpar ▸ Finset.inter_subset_left y.2) y.2 (hmatch y.1 y.2)
    · rw [if_neg hmatch] at hw; omega
  · rw [dif_neg hpar] at hw; omega

end Step1

/-! ### Step 2: the potential function and the main counting bound -/

section Step2

variable (N : NormDecomp F Δ k) (n : ℕ) {K : Type*} [Field K] [CharZero K] (hn0 : 0 < n)
  (hE : ∃ a b, F.mult a b ≠ 0)

/-- The potential of a raw gate: the `level` of its node for `R`/`S`-gates (bounded by `Δ`), and
`Δ` itself for input gates (a dummy value, never load-bearing since input gates are always the
very last element of any path and no invariant needs to be propagated past them). -/
noncomputable def potentialOf (N : NormDecomp F Δ k) (n : ℕ) : CGate N n → ℕ
  | .R t _ => level N.depth_le t
  | .S c _ => level N.depth_le c.1
  | .inp _ _ => Δ

/-- The indicator of being an `S`-gate. -/
def indS (N : NormDecomp F Δ k) (n : ℕ) : CGate N n → ℕ
  | .S _ _ => 1
  | _ => 0

theorem potentialOf_le (w : CGate N n) : potentialOf N n w ≤ Δ := by
  cases w with
  | R t γ => exact level_le N.depth_le t
  | S c δ => exact level_le N.depth_le c.1
  | inp i j => exact le_refl Δ

/-- **The main witness-chain invariant**, proved by induction on the prefix length `idx`:
at every stage there is a genuine `C₀`-gate `w`, equivalent to the (arbitrary, unexamined)
representative `(p idx).1`, whose potential dominates the number of support-changing wires
strictly before `idx` plus (if `w` is itself an `S`-gate) one more unit of "credit" needed for
the upcoming `S → R` step. -/
theorem exists_witness_prefix (hk2 : 2 ≤ k) (hn : 2 * k < n)
    (hrig : IsRigid (reduced (circuit N n K hn0 hE))) {m : ℕ}
    (p : Fin (m + 1) → (reduced (circuit N n K hn0 hE)).Gate)
    (hp : (reduced (circuit N n K hn0 hE)).IsPath p) :
    ∀ idx : ℕ, (hidx : idx ≤ m) →
      ∃ w : CGate N n, Equiv (circuit N n K hn0 hE) w (p ⟨idx, by omega⟩).1 ∧
        prefixCount (fun i : Fin m =>
          ¬ minSupport (reduced (circuit N n K hn0 hE)) (p i.succ) ⊆
            minSupport (reduced (circuit N n K hn0 hE)) (p i.castSucc)) idx + indS N n w ≤
          potentialOf N n w := by
  set Q : Fin m → Prop := fun i =>
    ¬ minSupport (reduced (circuit N n K hn0 hE)) (p i.succ) ⊆ minSupport (reduced (circuit N n K hn0 hE)) (p i.castSucc) with hQdef
  intro idx
  induction idx with
  | zero =>
      intro _
      rcases hcase : (p (⟨0, by omega⟩ : Fin (m + 1))).1 with ⟨t, γ⟩ | ⟨c, δ⟩ | ⟨i, j⟩
      · refine ⟨CGate.R t γ, ?_, ?_⟩
        · exact equiv_refl _ _
        · rw [prefixCount_zero]; simp [indS, potentialOf]
      · refine ⟨CGate.S c δ, ?_, ?_⟩
        · exact equiv_refl _ _
        · rw [prefixCount_zero]
          have hne0 : level N.depth_le c.1 ≠ 0 := by
            intro hz
            exact c.2 ((level_eq_zero_iff N.depth_le N.parent_root c.1).mp hz)
          simp only [indS, potentialOf]
          omega
      · refine ⟨CGate.inp i j, ?_, ?_⟩
        · exact equiv_refl _ _
        · rw [prefixCount_zero]; simp [indS, potentialOf]
  | succ idx ih =>
      intro hidx1
      have hidxm : idx < m := by omega
      obtain ⟨w, hwequiv, hwinv⟩ := ih (by omega)
      have hcast : (⟨idx, hidxm⟩ : Fin m).castSucc = (⟨idx, by omega⟩ : Fin (m + 1)) := by
        apply Fin.ext; simp [Fin.castSucc]
      have hsucc : (⟨idx, hidxm⟩ : Fin m).succ = (⟨idx + 1, by omega⟩ : Fin (m + 1)) := by
        apply Fin.ext; simp [Fin.succ]
      have hwire0 : 0 < (reduced (circuit N n K hn0 hE)).wire
          (p (⟨idx, hidxm⟩ : Fin m).castSucc) (p (⟨idx, hidxm⟩ : Fin m).succ) := hp ⟨idx, hidxm⟩
      rw [hcast, hsucc] at hwire0
      have hWpos : 0 < W (circuit N n K hn0 hE) (p (⟨idx, by omega⟩ : Fin (m + 1))).1
          (p (⟨idx + 1, by omega⟩ : Fin (m + 1))).1 := by
        rw [← reduced_wire]; exact hwire0
      have hWpos' : 0 < W (circuit N n K hn0 hE) w (p (⟨idx + 1, by omega⟩ : Fin (m + 1))).1 := by
        rw [W_eq_of_equiv (circuit N n K hn0 hE) hwequiv]
        exact hWpos
      obtain ⟨w', hw'equiv, hw'wire⟩ := exists_of_W_pos (circuit N n K hn0 hE) hWpos'
      refine ⟨w', hw'equiv, ?_⟩
      have hle := prefixCount_succ_le Q idx hidxm
      have hmA : minSupport (reduced (circuit N n K hn0 hE)) (p (⟨idx, by omega⟩ : Fin (m + 1))) =
          (gatePoints N n w : Set (Fin n ⊕ Fin n)) := by
        rw [← RigidConstruction.toC'_eq_of_equiv (circuit N n K hn0 hE) hwequiv]
        cases w with
        | R t γ => exact minSupport_R_eq N n hn0 hE hk2 hn hrig t γ
        | S c δ => exact minSupport_S_eq N n hn0 hE hk2 hn hrig c δ
        | inp i' j' => exact minSupport_inp_eq N n hn0 hE hk2 hn hrig i' j'
      have hmB : minSupport (reduced (circuit N n K hn0 hE)) (p (⟨idx + 1, by omega⟩ : Fin (m + 1))) =
          (gatePoints N n w' : Set (Fin n ⊕ Fin n)) := by
        rw [← RigidConstruction.toC'_eq_of_equiv (circuit N n K hn0 hE) hw'equiv]
        cases w' with
        | R t γ => exact minSupport_R_eq N n hn0 hE hk2 hn hrig t γ
        | S c δ => exact minSupport_S_eq N n hn0 hE hk2 hn hrig c δ
        | inp i' j' => exact minSupport_inp_eq N n hn0 hE hk2 hn hrig i' j'
      cases w with
      | R t γ =>
          cases w' with
          | R t' γ' =>
              have hz : (0:ℕ) < wire N n (CGate.R t γ) (CGate.R t' γ') := hw'wire
              simp only [wire] at hz
              omega
          | inp i' j' =>
              have hsub : gatePoints N n (CGate.inp i' j') ⊆ gatePoints N n (CGate.R t γ) :=
                gatePoints_inp_subset_R N n hw'wire
              have hnotQ : ¬ Q (⟨idx, hidxm⟩ : Fin m) := by
                rw [hQdef]
                simp only [not_not, hcast, hsucc, hmA, hmB]
                exact Finset.coe_subset.mpr hsub
              rw [if_neg hnotQ, add_zero] at hle
              have hbound : prefixCount Q idx ≤ level N.depth_le t := by
                simpa [indS, potentialOf] using hwinv
              simp only [indS, potentialOf]
              have := level_le N.depth_le t
              omega
          | S c' δ' =>
              have hw'wire2 : 0 < wireRtoS N n t γ c' δ' := hw'wire
              have hparc' : N.parent c'.1 = t := by
                by_contra hne
                unfold wireRtoS at hw'wire2
                rw [dif_neg hne] at hw'wire2
                omega
              have hsub : gatePoints N n (CGate.S c' δ') ⊆ gatePoints N n (CGate.R t γ) :=
                gatePoints_S_subset_R N n hw'wire
              have hnotQ : ¬ Q (⟨idx, hidxm⟩ : Fin m) := by
                rw [hQdef]
                simp only [not_not, hcast, hsucc, hmA, hmB]
                exact Finset.coe_subset.mpr hsub
              rw [if_neg hnotQ, add_zero] at hle
              have hbound : prefixCount Q idx ≤ level N.depth_le t := by
                simpa [indS, potentialOf] using hwinv
              have hlev : level N.depth_le c'.1 = level N.depth_le t + 1 := by
                rw [← hparc']; exact level_succ N.depth_le N.parent_root c'.2
              simp only [indS, potentialOf]
              omega
      | S c δ =>
          cases w' with
          | S c' δ' =>
              have hz : (0:ℕ) < wire N n (CGate.S c δ) (CGate.S c' δ') := hw'wire
              simp only [wire] at hz
              omega
          | inp i' j' =>
              have hz : (0:ℕ) < wire N n (CGate.S c δ) (CGate.inp i' j') := hw'wire
              simp only [wire] at hz
              omega
          | R t' γ' =>
              have hw'wire2 : 0 < wireStoR N n c δ t' γ' := hw'wire
              have hct' : c.1 = t' := by
                by_contra hne
                unfold wireStoR at hw'wire2
                rw [dif_neg hne] at hw'wire2
                omega
              subst hct'
              have hbound : prefixCount Q idx + 1 ≤ level N.depth_le c.1 := by
                simpa [indS, potentialOf] using hwinv
              simp only [indS, potentialOf]
              split_ifs at hle <;> omega
      | inp i j =>
          have hz : (0:ℕ) < wire N n (CGate.inp i j) w' := hw'wire
          have hz0 : wire N n (CGate.inp i j) w' = 0 := by cases w' <;> rfl
          omega

/-- **The main per-path bound.** `supportChanges (reduced (circuit N n K hn0 hE)) p ≤ Δ` for every path `p`. -/
theorem supportChanges_le_Δ (hk2 : 2 ≤ k) (hn : 2 * k < n)
    (hrig : IsRigid (reduced (circuit N n K hn0 hE))) {m : ℕ}
    (p : Fin (m + 1) → (reduced (circuit N n K hn0 hE)).Gate)
    (hp : (reduced (circuit N n K hn0 hE)).IsPath p) :
    supportChanges (reduced (circuit N n K hn0 hE)) p ≤ Δ := by
  set Q : Fin m → Prop := fun i =>
    ¬ minSupport (reduced (circuit N n K hn0 hE)) (p i.succ) ⊆ minSupport (reduced (circuit N n K hn0 hE)) (p i.castSucc) with hQdef
  obtain ⟨w, -, hw⟩ := exists_witness_prefix N n hn0 hE hk2 hn hrig p hp m (le_refl m)
  have hQeq : (fun i : Fin m => ¬ minSupport (reduced (circuit N n K hn0 hE)) (p i.succ) ⊆ minSupport (reduced (circuit N n K hn0 hE)) (p i.castSucc)) = Q :=
    rfl
  rw [hQeq] at hw
  rw [show supportChanges (reduced (circuit N n K hn0 hE)) p = {i : Fin m | Q i}.ncard from rfl,
    ncard_setOf_eq_filter_card Q, ← prefixCount_eq_card_univ Q]
  have hpot := potentialOf_le N n w
  omega

/-- **Item 1 (support depth bound).** `supportDepth (reduced C₀) ≤ Δ`, in the "real" branch
(support size `≤ k < n / 2`). -/
theorem supportDepth_reduced_le (hk2 : 2 ≤ k) (hn : 2 * k < n)
    (hrig : IsRigid (reduced (circuit N n K hn0 hE))) :
    supportDepth (reduced (circuit N n K hn0 hE)) ≤ Δ := by
  have hss : supportSize (reduced (circuit N n K hn0 hE)) ≤ k :=
    supportSize_reduced_le N n hn0 hE hk2 hrig
  rw [supportDepth, if_pos (by omega)]
  apply csSup_le'
  rintro c ⟨m, p, hp, hc⟩
  rw [← hc]
  exact supportChanges_le_Δ N n hn0 hE hk2 hn hrig p hp

/-- **Convenience corollary**, mirroring `supportSize_reduced_le'`: combining the pieces needed
to invoke `supportDepth_reduced_le` from `IsMatrixSymmetric C₀` alone. -/
theorem supportDepth_reduced_le' (hk2 : 2 ≤ k) (hn : 2 * k < n) :
    supportDepth (reduced (circuit N n K hn0 hE)) ≤ Δ := by
  have hsym₀ : IsMatrixSymmetric (circuit N n K hn0 hE) := isMatrixSymmetric_circuit N n hn0 hE
  have hred : (reduced (circuit N n K hn0 hE)).IsReduced :=
    Lax461425Proofs.RigidReduced.isReduced_reduced (circuit N n K hn0 hE)
  have hsym : IsMatrixSymmetric (reduced (circuit N n K hn0 hE)) :=
    isMatrixSymmetric_reduced (circuit N n K hn0 hE) hsym₀
  have hrig : IsRigid (reduced (circuit N n K hn0 hE)) :=
    Lax461425Proofs.ReducedRigid.isRigid hsym hred
  exact supportDepth_reduced_le N n hn0 hE hk2 hn hrig

end Step2

end Lax461425Proofs
