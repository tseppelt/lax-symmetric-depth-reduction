import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Nat.Choose.Sum

/-!
---
title: Products from power sums (Newton's identities, set-partition form)
type: definition
---
Let $R$ be a commutative $\mathbb{Q}$-algebra, $N \geq 1$, and $y_1, \dots, y_N \in R$. Writing
$p_m := \sum_i y_i^m$ for the degree-$m$ power sum, we prove
$$
  N! \cdot \prod_i y_i = \sum_\pi \mu(\pi) \prod_{P \in \pi} p_{|P|},
$$
where $\pi$ ranges over the set partitions of $\{1, \dots, N\}$ (formalised as
`Finpartition (Finset.univ : Finset (Fin N))`) and
$\mu(\pi) := \prod_{P \in \pi} (-1)^{|P|-1} (|P|-1)!$.

We avoid the explicit `1/N!` from the informal statement (meaningless in a general commutative
ring) by multiplying through by `N!`; this is the natural form for later use inside a polynomial
ring, which need not be a field.

The proof proceeds by strong induction on `s.card` for a auxiliary statement about an arbitrary
`s : Finset (Fin N)` (not just `univ`), using the recursion obtained by grouping the partitions
of `s` according to the part containing a fixed element `x₀ ∈ s`, and comparing with the
classical two-term recurrence for elementary symmetric polynomials
(`MvPolynomial.mul_esymm_eq_sum`) transported from formal variables to the actual elements `y i`
via `MvPolynomial.aeval`.
-/

namespace Lax461425Proofs.PatternsNewton

open Finset MvPolynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R] {N : ℕ}

/-- The degree-`m` power sum of `y`. -/
noncomputable def powerSum (y : Fin N → R) (m : ℕ) : R :=
  ∑ i, y i ^ m

/-- The weight of a single block `B` of a partition: `(-1)^(|B|-1) (|B|-1)! \cdot p_{|B|}`,
combining the sign/factorial factor `μ` and the power-sum factor into a single term. -/
noncomputable def blockWeight (y : Fin N → R) (B : Finset (Fin N)) : R :=
  (-1 : R) ^ (B.card - 1) * ((Nat.factorial (B.card - 1) : ℕ) : R) * powerSum y B.card

/-- `Qsum y s` is the sum, over all set partitions `π` of `s`, of the product of the block
weights of `π`. For `s = univ : Finset (Fin N)` this is the right-hand side of Newton's
identity (with `μ(π)` and the product of power sums combined into a single product). -/
noncomputable def Qsum (y : Fin N → R) (s : Finset (Fin N)) : R :=
  ∑ π : Finpartition s, ∏ B ∈ π.parts, blockWeight y B

omit [Algebra ℚ R] in
@[simp]
theorem Qsum_empty (y : Fin N → R) : Qsum y (∅ : Finset (Fin N)) = 1 := by
  have hU : Unique (Finpartition (∅ : Finset (Fin N))) := by
    rw [← Finset.bot_eq_empty]; infer_instance
  have hdefault : (default : Finpartition (∅ : Finset (Fin N))).parts = ∅ :=
    Finpartition.parts_eq_empty_iff.2 rfl
  rw [Qsum, Finset.univ_unique, Finset.sum_singleton, hdefault, Finset.prod_empty]

section Avoid

/-- If `B` is a part of `π`, avoiding `B` erases exactly `B` from the parts of `π`. -/
theorem avoid_parts_of_mem {s : Finset (Fin N)} (π : Finpartition s) {B : Finset (Fin N)}
    (hB : B ∈ π.parts) : (π.avoid B).parts = π.parts.erase B := by
  ext C
  rw [Finpartition.mem_avoid, Finset.mem_erase]
  constructor
  · rintro ⟨D, hD, hDnle, rfl⟩
    have hDB : D ≠ B := by
      rintro rfl; exact hDnle le_rfl
    have hdisj : Disjoint D B := π.disjoint hD hB hDB
    rw [hdisj.sdiff_eq_left]
    exact ⟨hDB, hD⟩
  · rintro ⟨hCB, hC⟩
    refine ⟨C, hC, ?_, (π.disjoint hC hB hCB).sdiff_eq_left⟩
    intro hCleB
    have : C = (⊥ : Finset (Fin N)) := disjoint_self.mp ((π.disjoint hC hB hCB).mono_right hCleB)
    exact π.ne_bot hC this

/-- Extending the partition of `s \ B` obtained by avoiding `B` recovers `π`, when `B` was a
part of `π`. -/
theorem extend_avoid {s : Finset (Fin N)} (π : Finpartition s) {B : Finset (Fin N)}
    (hB : B ∈ π.parts) (hBne : B ≠ (⊥ : Finset (Fin N))) (hBdisj : Disjoint (s \ B) B)
    (hBsup : s \ B ⊔ B = s) : (π.avoid B).extend hBne hBdisj hBsup = π := by
  have hparts : ((π.avoid B).extend hBne hBdisj hBsup).parts = π.parts := by
    rw [Finpartition.extend_parts, avoid_parts_of_mem π hB, Finset.insert_erase hB]
  ext C
  rw [hparts]

/-- Avoiding `B` after extending a partition of `s \ B` by `B` recovers the original
partition. -/
theorem avoid_extend {s B : Finset (Fin N)} (π' : Finpartition (s \ B))
    (hBne : B ≠ (⊥ : Finset (Fin N))) (hBdisj : Disjoint (s \ B) B) (hBsup : s \ B ⊔ B = s) :
    (π'.extend hBne hBdisj hBsup).avoid B = π' := by
  have hBnotmem : B ∉ π'.parts := by
    intro hmem
    have hBle : B ≤ s \ B := π'.le hmem
    exact hBne (disjoint_self.mp (hBdisj.mono_left hBle))
  have hparts : ((π'.extend hBne hBdisj hBsup).avoid B).parts = π'.parts := by
    rw [avoid_parts_of_mem _ (by rw [Finpartition.extend_parts]; exact Finset.mem_insert_self _ _),
      Finpartition.extend_parts, Finset.erase_insert hBnotmem]
  ext C
  rw [hparts]

end Avoid

omit [Algebra ℚ R] in
/-- Grouping the partitions of `s` by the part containing a fixed element `x₀ ∈ s`: `Qsum y s`
decomposes as a sum, over nonempty `B ⊆ s` containing `x₀`, of the weight of `B` times
`Qsum y (s \ B)`. -/
theorem Qsum_recursion {s : Finset (Fin N)} {x0 : Fin N} (hx0 : x0 ∈ s) (y : Fin N → R) :
    Qsum y s =
      ∑ B ∈ (Finset.univ : Finset (Finset (Fin N))).filter (fun B => x0 ∈ B ∧ B ⊆ s),
        blockWeight y B * Qsum y (s \ B) := by
  classical
  have hfiber : Qsum y s = ∑ B : Finset (Fin N),
      ∑ π ∈ (Finset.univ : Finset (Finpartition s)).filter (fun π => π.part x0 = B),
        ∏ C ∈ π.parts, blockWeight y C :=
    (Finset.sum_fiberwise (Finset.univ : Finset (Finpartition s))
      (fun π => π.part x0) (fun π => ∏ C ∈ π.parts, blockWeight y C)).symm
  rw [hfiber, ← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Finset (Fin N)))
    (fun B => x0 ∈ B ∧ B ⊆ s)]
  have hzero : ∑ B ∈ (Finset.univ : Finset (Finset (Fin N))).filter
      (fun B => ¬ (x0 ∈ B ∧ B ⊆ s)),
      ∑ π ∈ (Finset.univ : Finset (Finpartition s)).filter (fun π => π.part x0 = B),
        ∏ C ∈ π.parts, blockWeight y C = 0 := by
    refine Finset.sum_eq_zero fun B hB => Finset.sum_eq_zero fun π hπ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB hπ
    exact absurd ⟨hπ ▸ π.mem_part hx0, hπ ▸ π.part_subset x0⟩ hB
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun B hB => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
  obtain ⟨hx0B, hBs⟩ := hB
  have hBne : B ≠ (⊥ : Finset (Fin N)) := by rintro rfl; simp at hx0B
  have hBdisj : Disjoint (s \ B) B := disjoint_sdiff_self_left
  have hBsup : s \ B ⊔ B = s := sdiff_sup_cancel hBs
  rw [Qsum, Finset.mul_sum]
  refine Finset.sum_nbij' (fun π => π.avoid B) (fun π' => π'.extend hBne hBdisj hBsup)
    (fun π _ => Finset.mem_univ _) (fun π' _ => ?_) (fun π hπ => ?_) (fun π' _ => ?_)
    (fun π hπ => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hBmem : B ∈ (π'.extend hBne hBdisj hBsup).parts := by
      rw [Finpartition.extend_parts]; exact Finset.mem_insert_self _ _
    exact (π'.extend hBne hBdisj hBsup).part_eq_of_mem hBmem hx0B
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    have hBmem : B ∈ π.parts := hπ ▸ π.part_mem.mpr hx0
    exact extend_avoid π hBmem hBne hBdisj hBsup
  · exact avoid_extend π' hBne hBdisj hBsup
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    have hBmem : B ∈ π.parts := hπ ▸ π.part_mem.mpr hx0
    rw [avoid_parts_of_mem π hBmem]
    exact (Finset.mul_prod_erase π.parts (blockWeight y) hBmem).symm

section Esym

/-- The degree-`k` elementary symmetric function of `y`, as an honest sum (not going through
`MvPolynomial`). -/
noncomputable def esym (y : Fin N → R) (k : ℕ) : R :=
  ∑ t ∈ Finset.powersetCard k (Finset.univ : Finset (Fin N)), ∏ i ∈ t, y i

omit [Algebra ℚ R] in
theorem esym_card (y : Fin N → R) : esym y N = ∏ i, y i := by
  have hcard : (Finset.univ : Finset (Fin N)).card = N :=
    Finset.card_univ.trans (Fintype.card_fin N)
  have h : Finset.powersetCard N (Finset.univ : Finset (Fin N)) = {Finset.univ} := by
    have := congrArg (fun m => Finset.powersetCard m (Finset.univ : Finset (Fin N))) hcard
    simpa using this.symm.trans (Finset.powersetCard_self (Finset.univ : Finset (Fin N)))
  rw [esym, h, Finset.sum_singleton]

theorem aeval_esymm (y : Fin N → R) (k : ℕ) :
    MvPolynomial.aeval y (MvPolynomial.esymm (Fin N) ℚ k) = esym y k := by
  rw [MvPolynomial.esymm, esym, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_prod]
  simp

theorem aeval_psum (y : Fin N → R) (m : ℕ) :
    MvPolynomial.aeval y (MvPolynomial.psum (Fin N) ℚ m) = powerSum y m := by
  rw [MvPolynomial.psum, powerSum, map_sum]
  simp

/-- The classical two-term Newton recurrence for `esym`, transported from `MvPolynomial` to the
actual elements `y i` via `aeval`. -/
theorem esym_recursion (y : Fin N → R) (k : ℕ) :
    (k : R) * esym y k = (-1 : R) ^ (k + 1) *
      ∑ a ∈ Finset.antidiagonal k with a.1 < k, (-1 : R) ^ a.1 * esym y a.1 * powerSum y a.2 := by
  have h := congrArg (MvPolynomial.aeval y) (MvPolynomial.mul_esymm_eq_sum (Fin N) ℚ k)
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum, aeval_esymm, aeval_psum]
    at h
  exact h

/-- The Newton recurrence, reindexed from `Finset.antidiagonal` to `Finset.range`. -/
theorem esym_recursion' (y : Fin N → R) (k : ℕ) :
    (k : R) * esym y k =
      ∑ m ∈ Finset.range k, (-1 : R) ^ m * esym y (k - 1 - m) * powerSum y (m + 1) := by
  rw [esym_recursion]
  have hreindex : ∑ a ∈ Finset.antidiagonal k with a.1 < k,
      (-1 : R) ^ a.1 * esym y a.1 * powerSum y a.2
      = ∑ m ∈ Finset.range k, (-1 : R) ^ (k - 1 - m) * esym y (k - 1 - m) * powerSum y (m + 1) := by
    refine Finset.sum_nbij' (fun a => a.2 - 1) (fun m => (k - 1 - m, m + 1)) ?_ ?_ ?_ ?_ ?_
    · rintro a ha
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at ha
      simp only [Finset.mem_range]
      omega
    · intro m hm
      simp only [Finset.mem_range] at hm
      simp only [Finset.mem_filter, Finset.mem_antidiagonal]
      omega
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at ha
      have h1 : k - 1 - (a.2 - 1) = a.1 := by omega
      have h2 : a.2 - 1 + 1 = a.2 := by omega
      rw [Prod.ext_iff]
      exact ⟨h1, h2⟩
    · intro m hm
      simp only [Finset.mem_range] at hm
      show m + 1 - 1 = m
      omega
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at ha
      have h1 : k - 1 - (a.2 - 1) = a.1 := by omega
      have h2 : a.2 - 1 + 1 = a.2 := by omega
      rw [h1, h2]
  rw [hreindex, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finset.mem_range] at hm
  have hexp : (k + 1) + (k - 1 - m) = m + 2 * (k - m) := by omega
  have hsign : (-1 : R) ^ (k + 1) * (-1 : R) ^ (k - 1 - m) = (-1 : R) ^ m := by
    rw [← pow_add, hexp, pow_add, pow_mul]
    norm_num
  calc (-1 : R) ^ (k + 1) * ((-1 : R) ^ (k - 1 - m) * esym y (k - 1 - m) * powerSum y (m + 1))
      = ((-1 : R) ^ (k + 1) * (-1 : R) ^ (k - 1 - m)) * esym y (k - 1 - m) * powerSum y (m + 1) := by
        ring
    _ = (-1 : R) ^ m * esym y (k - 1 - m) * powerSum y (m + 1) := by rw [hsign]

end Esym

/-- `Qsum y s` equals `|s|! * esym y |s|`, by strong induction on `|s|` using
`Qsum_recursion` and `esym_recursion'`. -/
theorem Qsum_eq (y : Fin N → R) : ∀ k, ∀ s : Finset (Fin N), s.card = k →
    Qsum y s = (Nat.factorial k : R) * esym y k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hs
    rcases Finset.eq_empty_or_nonempty s with hempty | hnonempty
    · subst hempty
      simp only [Finset.card_empty] at hs
      subst hs
      simp [esym]
    · obtain ⟨x0, hx0⟩ := hnonempty
      have hk0 : k ≠ 0 := by rintro rfl; rw [Finset.card_eq_zero] at hs; subst hs; simp at hx0
      rw [Qsum_recursion hx0]
      have hreindex : ∑ B ∈ (Finset.univ : Finset (Finset (Fin N))).filter
          (fun B => x0 ∈ B ∧ B ⊆ s), blockWeight y B * Qsum y (s \ B)
          = ∑ T ∈ (s.erase x0).powerset,
              blockWeight y (insert x0 T) * Qsum y (s \ insert x0 T) := by
        refine Finset.sum_nbij' (fun B => B.erase x0) (fun T => insert x0 T) ?_ ?_ ?_ ?_ ?_
        · rintro B hB
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
          simp only [Finset.mem_powerset]
          intro a ha
          rw [Finset.mem_erase] at ha
          exact Finset.mem_erase.mpr ⟨ha.1, hB.2 ha.2⟩
        · intro T hT
          simp only [Finset.mem_powerset] at hT
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨Finset.mem_insert_self _ _, ?_⟩
          intro a ha
          rcases Finset.mem_insert.mp ha with rfl | haT
          · exact hx0
          · exact (Finset.mem_erase.mp (hT haT)).2
        · intro B hB
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
          exact Finset.insert_erase hB.1
        · intro T hT
          simp only [Finset.mem_powerset] at hT
          exact Finset.erase_insert (fun h => (Finset.mem_erase.mp (hT h)).1 rfl)
        · intro B hB
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
          rw [Finset.insert_erase hB.1]
      rw [hreindex]
      have hterm : ∀ T ∈ (s.erase x0).powerset,
          blockWeight y (insert x0 T) * Qsum y (s \ insert x0 T)
            = (-1 : R) ^ T.card * ((Nat.factorial T.card : ℕ) : R) * powerSum y (T.card + 1)
              * ((Nat.factorial (k - T.card - 1) : ℕ) : R) * esym y (k - T.card - 1) := by
        intro T hT
        simp only [Finset.mem_powerset] at hT
        have hx0T : x0 ∉ T := fun h => (Finset.mem_erase.mp (hT h)).1 rfl
        have hcardB : (insert x0 T).card = T.card + 1 := Finset.card_insert_of_notMem hx0T
        have hTs : T ⊆ s := hT.trans (Finset.erase_subset _ _)
        have hBs : insert x0 T ⊆ s := Finset.insert_subset hx0 hTs
        have hcardsdiff : (s \ insert x0 T).card = k - (T.card + 1) := by
          rw [Finset.card_sdiff_of_subset hBs, hcardB, hs]
        have hlt : (s \ insert x0 T).card < k := by rw [hcardsdiff]; omega
        have hsub2 : k - (T.card + 1) = k - T.card - 1 := by omega
        have hblock : blockWeight y (insert x0 T)
            = (-1 : R) ^ T.card * ((Nat.factorial T.card : ℕ) : R) * powerSum y (T.card + 1) := by
          rw [blockWeight, hcardB]; simp
        rw [hblock, ih _ hlt (s \ insert x0 T) rfl, hcardsdiff, hsub2]
        ring
      rw [Finset.sum_congr rfl hterm]
      have hcardx : (s.erase x0).card = k - 1 := by
        rw [Finset.card_erase_of_mem hx0, hs]
      have hsum : ∑ T ∈ (s.erase x0).powerset,
          ((-1 : R) ^ T.card * ((Nat.factorial T.card : ℕ) : R) * powerSum y (T.card + 1)
            * ((Nat.factorial (k - T.card - 1) : ℕ) : R) * esym y (k - T.card - 1))
          = ∑ m ∈ Finset.range ((s.erase x0).card + 1),
              ((s.erase x0).card.choose m : R) *
                ((-1 : R) ^ m * ((Nat.factorial m : ℕ) : R) * powerSum y (m + 1)
                  * ((Nat.factorial (k - m - 1) : ℕ) : R) * esym y (k - m - 1)) := by
        have := Finset.sum_powerset_apply_card
          (f := fun m => (-1 : R) ^ m * ((Nat.factorial m : ℕ) : R) * powerSum y (m + 1)
            * ((Nat.factorial (k - m - 1) : ℕ) : R) * esym y (k - m - 1))
          (x := s.erase x0)
        simpa [nsmul_eq_mul] using this
      rw [hsum, hcardx]
      have hrange : Finset.range (k - 1 + 1) = Finset.range k := by
        congr 1; omega
      rw [hrange]
      have hcoeff : ∀ m ∈ Finset.range k,
          ((k - 1).choose m : R) * ((-1 : R) ^ m * ((Nat.factorial m : ℕ) : R)
              * powerSum y (m + 1) * ((Nat.factorial (k - m - 1) : ℕ) : R) * esym y (k - m - 1))
            = (Nat.factorial (k - 1) : R) *
              ((-1 : R) ^ m * esym y (k - 1 - m) * powerSum y (m + 1)) := by
        intro m hm
        simp only [Finset.mem_range] at hm
        have hmle : m ≤ k - 1 := by omega
        have hfact : (k - 1).choose m * Nat.factorial m * Nat.factorial (k - 1 - m)
            = Nat.factorial (k - 1) := Nat.choose_mul_factorial_mul_factorial hmle
        have heq : k - m - 1 = k - 1 - m := by omega
        rw [heq]
        have hfactR : ((k - 1).choose m : R) * (Nat.factorial m : R) * (Nat.factorial (k - 1 - m) : R)
            = (Nat.factorial (k - 1) : R) := by
          have h := congrArg (fun n : ℕ => (n : R)) hfact
          push_cast at h
          exact h
        calc ((k - 1).choose m : R) * ((-1 : R) ^ m * (Nat.factorial m : R)
            * powerSum y (m + 1) * (Nat.factorial (k - 1 - m) : R) * esym y (k - 1 - m))
            = (((k - 1).choose m : R) * (Nat.factorial m : R) * (Nat.factorial (k - 1 - m) : R))
              * ((-1 : R) ^ m * esym y (k - 1 - m) * powerSum y (m + 1)) := by ring
          _ = (Nat.factorial (k - 1) : R) * ((-1 : R) ^ m * esym y (k - 1 - m) * powerSum y (m + 1)) := by
              rw [hfactR]
      rw [Finset.sum_congr rfl hcoeff, ← Finset.mul_sum, ← esym_recursion']
      have hfact2 : (k : R) * (Nat.factorial (k - 1) : R) = (Nat.factorial k : R) := by
        have h := congrArg (fun n : ℕ => (n : R)) (Nat.mul_factorial_pred hk0)
        push_cast at h
        exact h
      calc (Nat.factorial (k - 1) : R) * ((k : R) * esym y k)
          = ((k : R) * (Nat.factorial (k - 1) : R)) * esym y k := by ring
        _ = (Nat.factorial k : R) * esym y k := by rw [hfact2]

/-- `μ(π) := ∏_{B ∈ π} (-1)^(|B|-1) (|B|-1)!`, the sign/factorial factor from Newton's
identity. -/
noncomputable def mu (π : Finpartition (Finset.univ : Finset (Fin N))) : R :=
  ∏ B ∈ π.parts, (-1 : R) ^ (B.card - 1) * ((Nat.factorial (B.card - 1) : ℕ) : R)

/-- **Products from power sums** (`lem:newton`). For `y : Fin N → R` in a commutative
`ℚ`-algebra `R`, writing `p_m := powerSum y m = ∑ i, y i ^ m` for the power sums,
$$ N! \cdot \prod_i y_i = \sum_\pi \mu(\pi) \prod_{P \in \pi} p_{|P|}, $$
where `π` ranges over the set partitions of `Fin N` (`Finpartition (Finset.univ : Finset
(Fin N))`) and `μ(π) := ∏_{P ∈ π} (-1)^(|P|-1) (|P|-1)!`. (We multiply the informal identity
through by `N!` since `1/N!` is not meaningful in a general commutative ring; `N! : R` is
genuinely a unit here, but keeping the statement free of division makes it more convenient to
apply inside a polynomial ring.) -/
theorem newton (y : Fin N → R) :
    (Nat.factorial N : R) * ∏ i, y i =
      ∑ π : Finpartition (Finset.univ : Finset (Fin N)), mu π * ∏ B ∈ π.parts, powerSum y B.card := by
  have h1 : Qsum y (Finset.univ : Finset (Fin N)) = (Nat.factorial N : R) * ∏ i, y i := by
    rw [Qsum_eq y N Finset.univ (Finset.card_univ.trans (Fintype.card_fin N)), esym_card]
  rw [← h1, Qsum]
  refine Finset.sum_congr rfl fun π _ => ?_
  calc ∏ B ∈ π.parts, blockWeight y B
      = (∏ B ∈ π.parts, (-1 : R) ^ (B.card - 1) * ((Nat.factorial (B.card - 1) : ℕ) : R))
          * ∏ B ∈ π.parts, powerSum y B.card :=
        Finset.prod_mul_distrib
    _ = mu π * ∏ B ∈ π.parts, powerSum y B.card := by rw [mu]
