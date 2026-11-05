import Lax461425.FormulaSupportDepth
import Lax461425Proofs.SymVFSupportDepthOrbit
import Lax461425Proofs.RigidReduced
import Lax461425Proofs.RigidOrbit
import Lax461425Proofs.RigidComputes
import Lax461425Proofs.ReducedRigid
import Lax461425Proofs.SupportTheorem

/-!
The rigidification of a symmetric formula of small orbit size has bounded support depth. Along
a path of the rigidification, every support-changing wire is moved by a stabiliser of its
parent so that it adds a new point to the union of the supports along the path. While the end
of the path is a non-input gate, both sides of this union stay below `κ`, as otherwise the
orbit of a lifted gate in the formula would be at least `n.choose κ`.
-/

namespace Lax461425Proofs.SymVFSupportDepth

open Lax461425.Circuits Lax461425.CircuitProperties Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425.SymmetricFamilies
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open RigidConstruction SymVFSupportDepthBasic SymVFSupportDepthOrbit

open scoped Classical

variable {K : Type*} {n κ : ℕ} (C : Circuit (Fin n × Fin n) K)

/-- Both sides of the union of the supports along a path ending in a non-input gate stay
below `κ`, as long as they are at most `2 (κ - 1)`. -/
theorem side_le (hf : IsFormula C) (hsym : IsMatrixSymmetric C) (hκ : 3 * κ ≤ n + 2)
    (horb : orbitSize C < n.choose κ) (hrig : IsRigid (reduced C))
    (hn2 : 2 * supportSize (reduced C) < n) (q : ℕ → (reduced C).Gate) (k : ℕ)
    (hq : ∀ l < k, 0 < (reduced C).wire (q l) (q (l + 1)))
    (hint : ¬ ((reduced C).label (q k)).IsInput) :
    ((leftPart (pathUnion q k)).ncard ≤ 2 * (κ - 1) → (leftPart (pathUnion q k)).ncard ≤ κ - 1) ∧
    ((rightPart (pathUnion q k)).ncard ≤ 2 * (κ - 1) →
      (rightPart (pathUnion q k)).ncard ≤ κ - 1) := by
  have hrange := ncard_range_le C hf hsym hrig q k hq hint
  constructor
  · intro h2
    by_contra hcon
    have h1 := choose_le_choose_of_between (n := n) (κ := κ)
      (a := (leftPart (pathUnion q k)).ncard) (by omega) (by omega)
    have h3 := choose_left_le hrig hn2 q k
    omega
  · intro h2
    by_contra hcon
    have h1 := choose_le_choose_of_between (n := n) (κ := κ)
      (a := (rightPart (pathUnion q k)).ncard) (by omega) (by omega)
    have h3 := choose_right_le hrig hn2 q k
    omega

theorem side_union_le (U S : Set (Fin n ⊕ Fin n)) :
    (leftPart (U ∪ S)).ncard ≤ (leftPart U).ncard + S.ncard ∧
      (rightPart (U ∪ S)).ncard ≤ (rightPart U).ncard + S.ncard := by
  constructor
  · rw [leftPart_union]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left (ncard_leftPart_le S) _)
  · rw [rightPart_union]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left (ncard_rightPart_le S) _)

/-- Every path of the rigidification has at most `2 κ` support-changing wires. -/
theorem supportChanges_le_of_sides {D : Circuit (Fin n × Fin n) K} (hn : 20 ≤ n)
    (hκ : 3 * κ ≤ n + 2) (hκ1 : 1 ≤ κ) (hrig : IsRigid D) (hsz : supportSize D ≤ κ - 1)
    (hside : ∀ (q : ℕ → D.Gate) (k : ℕ), (∀ l < k, 0 < D.wire (q l) (q (l + 1))) →
      ¬ (D.label (q k)).IsInput →
      ((leftPart (pathUnion q k)).ncard ≤ 2 * (κ - 1) →
          (leftPart (pathUnion q k)).ncard ≤ κ - 1) ∧
        ((rightPart (pathUnion q k)).ncard ≤ 2 * (κ - 1) →
          (rightPart (pathUnion q k)).ncard ≤ κ - 1))
    {m : ℕ} (p : Fin (m + 1) → D.Gate) (hp : D.IsPath p) : supportChanges D p ≤ 2 * κ := by
  have hn2 : 2 * supportSize D < n := by omega
  have hsupc : ∀ g : D.Gate, (minSupport D g).ncard ≤ κ - 1 :=
    fun g => (minSupport_spec hrig hn2 g).2.trans hsz
  let pp : ℕ → D.Gate := fun i => p ⟨min i m, by omega⟩
  have hpp : ∀ i < m, 0 < D.wire (pp i) (pp (i + 1)) := by
    intro i hi
    have h := hp ⟨i, hi⟩
    have e1 : pp i = p (Fin.castSucc ⟨i, hi⟩) := congrArg p (Fin.ext (by simp; omega))
    have e2 : pp (i + 1) = p (Fin.succ ⟨i, hi⟩) := congrArg p (Fin.ext (by simp; omega))
    rw [e1, e2]
    exact h
  let chg : ℕ → Prop := fun i => ¬ minSupport D (pp (i + 1)) ⊆ minSupport D (pp i)
  let cnt : ℕ → ℕ := fun k => ((Finset.range k).filter chg).card
  have hcnt_m : supportChanges D p = cnt m := by
    unfold supportChanges
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
    apply Finset.card_bij (fun i _ => i.val)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_filter, Finset.mem_range, i.isLt, true_and]
      have e1 : pp i.val = p i.castSucc := congrArg p (Fin.ext (by simp))
      have e2 : pp (i.val + 1) = p i.succ := congrArg p (Fin.ext (by simp))
      show ¬ minSupport D (pp (i.val + 1)) ⊆ minSupport D (pp i.val)
      rw [e1, e2]
      exact hi
    · intro i _ j _ h
      exact Fin.ext h
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      refine ⟨⟨b, hb.1⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have e1 : pp b = p (Fin.castSucc ⟨b, hb.1⟩) := congrArg p (Fin.ext (by simp; omega))
      have e2 : pp (b + 1) = p (Fin.succ ⟨b, hb.1⟩) := congrArg p (Fin.ext (by simp; omega))
      have := hb.2
      change ¬ minSupport D (pp (b + 1)) ⊆ minSupport D (pp b) at this
      rwa [e1, e2] at this
  have hcnt_succ : ∀ k, cnt (k + 1) = cnt k + (if chg k then 1 else 0) := by
    intro k
    show ((Finset.range (k + 1)).filter chg).card = ((Finset.range k).filter chg).card + _
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rfl
  have claim : ∀ k, k + 1 ≤ m → ∃ (q : ℕ → D.Gate) (γ : Γ n),
      (∀ l < k, 0 < D.wire (q l) (q (l + 1))) ∧ q k = σOf hrig γ (pp k) ∧
      cnt k ≤ (pathUnion q k).ncard ∧ (leftPart (pathUnion q k)).ncard ≤ κ - 1 ∧
      (rightPart (pathUnion q k)).ncard ≤ κ - 1 := by
    intro k
    induction k with
    | zero =>
      intro _
      have hsub : pathUnion (fun _ : ℕ => pp 0) 0 ⊆ minSupport D (pp 0) := by
        rintro x ⟨l, -, hx⟩
        exact hx
      have hU := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (hsupc (pp 0))
      refine ⟨fun _ => pp 0, 1, fun l hl => absurd hl (Nat.not_lt_zero _), ?_, ?_, ?_, ?_⟩
      · rw [σOf_one]; rfl
      · show ((Finset.range 0).filter chg).card ≤ _
        simp
      · exact (ncard_leftPart_le _).trans hU
      · exact (ncard_rightPart_le _).trans hU
    | succ k ih =>
      intro hkm
      obtain ⟨q, γ, hqw, hqk, hcnt, hL, hR⟩ := ih (by omega)
      set U := pathUnion q k with hUdef
      set x := σOf hrig γ (pp (k + 1)) with hx
      have hwx : 0 < D.wire (q k) x := by
        rw [hqk, hx, wire_σOf]; exact hpp k (by omega)
      have hUk : minSupport D (q k) ⊆ U := fun z hz => ⟨k, le_rfl, hz⟩
      obtain ⟨τ, hτ, hτz⟩ : ∃ τ : Γ n, σOf hrig τ (q k) = q k ∧
          (chg k → ∃ z ∈ minSupport D (σOf hrig τ x), z ∉ U) := by
        by_cases hc : chg k
        · have hc' : ¬ minSupport D x ⊆ minSupport D (q k) := by
            rw [hqk, hx]; exact not_subset_smul hrig hn2 γ hc
          obtain ⟨τ, h1, h2⟩ := exists_reroute hrig hn2 hc' U hUk (by omega) (by omega)
          exact ⟨τ, h1, fun _ => h2⟩
        · exact ⟨1, by rw [σOf_one]; rfl, fun h => absurd h hc⟩
      set y := σOf hrig τ x with hy
      let q' : ℕ → D.Gate := fun l => if l ≤ k then q l else y
      have hq'k : q' k = q k := by simp [q']
      have hq'k1 : q' (k + 1) = y := by simp [q']
      have hU' : pathUnion q' (k + 1) = U ∪ minSupport D y := by
        ext z
        constructor
        · rintro ⟨l, hl, hz⟩
          by_cases hlk : l ≤ k
          · left
            refine ⟨l, hlk, ?_⟩
            have : q' l = q l := by simp [q', hlk]
            rwa [this] at hz
          · right
            have : q' l = y := by simp [q', hlk]
            rwa [this] at hz
        · rintro (⟨l, hl, hz⟩ | hz)
          · refine ⟨l, by omega, ?_⟩
            have : q' l = q l := by simp [q', hl]
            rwa [this]
          · exact ⟨k + 1, le_rfl, by rwa [hq'k1]⟩
      have hyw : 0 < D.wire (q k) y := by
        rw [hy, ← hτ, wire_σOf]; exact hwx
      have hq'w : ∀ l < k + 1, 0 < D.wire (q' l) (q' (l + 1)) := by
        intro l hl
        by_cases hlk : l < k
        · have e1 : q' l = q l := by simp [q', show l ≤ k by omega]
          have e2 : q' (l + 1) = q (l + 1) := by simp [q', show l + 1 ≤ k by omega]
          rw [e1, e2]; exact hqw l hlk
        · have : l = k := by omega
          subst this
          rw [hq'k, hq'k1]; exact hyw
      have hyγ : y = σOf hrig (τ * γ) (pp (k + 1)) := by
        rw [σOf_mul, Equiv.Perm.mul_apply]
      have hcnt' : cnt (k + 1) ≤ (pathUnion q' (k + 1)).ncard := by
        rw [hcnt_succ, hU']
        split_ifs with hc
        · obtain ⟨z, hz, hzU⟩ := hτz hc
          calc cnt k + 1 ≤ U.ncard + 1 := by omega
            _ = (insert z U).ncard := (Set.ncard_insert_of_notMem hzU (Set.toFinite _)).symm
            _ ≤ (U ∪ minSupport D y).ncard := Set.ncard_le_ncard
                (Set.insert_subset (Or.inr hz) Set.subset_union_left) (Set.toFinite _)
        · exact hcnt.trans (Set.ncard_le_ncard Set.subset_union_left (Set.toFinite _))
      have hint : ¬ (D.label (q' (k + 1))).IsInput := by
        rw [hq'k1, hyγ]
        apply not_isInput_of_wire_pos (h := σOf hrig (τ * γ) (pp (k + 2)))
        rw [wire_σOf]; exact hpp (k + 1) (by omega)
      have hsides := hside q' (k + 1) hq'w hint
      have hun := side_union_le U (minSupport D y)
      have hsy := hsupc y
      refine ⟨q', τ * γ, hq'w, by rw [hq'k1, hyγ], hcnt', ?_, ?_⟩
      · apply hsides.1; rw [hU']; omega
      · apply hsides.2; rw [hU']; omega
  rw [hcnt_m]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [cnt]
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    obtain ⟨q, γ, -, -, hcnt, hL, hR⟩ := claim j le_rfl
    have hsucc := hcnt_succ j
    have hU := ncard_le_left_add_right (pathUnion q j)
    show cnt (j + 1) ≤ 2 * κ
    have h1 : cnt (j + 1) ≤ cnt j + 1 := by rw [hsucc]; split_ifs <;> omega
    omega

/--
---
conclusion: Lax461425.FormulaSupportDepth.exists_reduced
---
The rigidification of a symmetric formula of orbit size `< n.choose κ` has support size
`≤ κ - 1` by the support theorem, and support depth `≤ 2κ`: along any path, support-changing
wires are moved by stabilisers so that each adds a new point to the union of supports; lifting
to the formula, where non-input gates have unique parents, bounds both sides of this union by
`κ - 1` while the path ends in a non-input gate.
-/
theorem exists_reduced {K : Type*} [CommSemiring K] {n κ : ℕ} (hn : 20 ≤ n)
    (hκ : 3 * κ ≤ n + 2) (C : Circuit (Fin n × Fin n) K) (hformula : IsFormula C)
    (hsym : IsMatrixSymmetric C) (horb : orbitSize C < n.choose κ)
    {p : MatrixPolynomial n K} (hp : C.Computes p) :
    ∃ C' : Circuit (Fin n × Fin n) K,
      C'.Computes p ∧ C'.IsReduced ∧ IsMatrixSymmetric C' ∧
        supportSize C' ≤ κ - 1 ∧ supportDepth C' ≤ 2 * κ := by
  have hred := RigidReduced.isReduced_reduced C
  have hsym' := RigidSymmetric.isMatrixSymmetric_reduced C hsym
  have horb' : orbitSize (reduced C) < n.choose κ :=
    (RigidOrbit.orbitSize_reduced_le C hsym).trans_lt horb
  have hsz := SupportTheorem.supportSize_le hn hκ (reduced C) hred hsym' horb'
  have hrig : IsRigid (reduced C) := ReducedRigid.isRigid hsym' hred
  refine ⟨reduced C, RigidComputes.computes_transfer C hp, hred, hsym', hsz, ?_⟩
  unfold supportDepth
  rw [if_pos (by omega)]
  apply csSup_le'
  rintro c ⟨m, q, hq, rfl⟩
  have hn2 : 2 * supportSize (reduced C) < n := by omega
  have hκ1 : 1 ≤ κ := by
    by_contra h0
    have hk0 : κ = 0 := by omega
    rw [hk0, Nat.choose_zero_right] at horb
    obtain ⟨σ, hσ⟩ := hsym 1
    have hne : (orbit C C.out).Nonempty := ⟨σ C.out, 1, σ, hσ, rfl⟩
    have h1 := (Set.ncard_pos (Set.toFinite _)).mpr hne
    have h2 : (orbit C C.out).ncard ≤ orbitSize C :=
      Finset.le_sup (f := fun g => (orbit C g).ncard) (Finset.mem_univ _)
    omega
  exact supportChanges_le_of_sides hn hκ hκ1 hrig hsz
    (fun q k hq hint => side_le C hformula hsym hκ horb hrig hn2 q k hq hint) q hq

end Lax461425Proofs.SymVFSupportDepth
