import Mathlib.Algebra.Group.Subgroup.Map
import Lax461425Proofs.PatternsSupportAction
import Lax461425Proofs.PatternsSupportLemma

/-!
Basic structural facts about `IsSupport`/`minSupport`/`supportSize` for a reduced
matrix-symmetric circuit `C : Circuit (Fin n × Fin n) K`.

We show:

* the output gate has empty minimal support (`minSupport_out`);
* `supportSize C` is realised: every gate has an actual support of size `≤ supportSize C`
  (`supportSize_spec`);
* a reformulation of `IsSupport` as a subgroup inequality `fixingSubgroup (Γ n) S ≤
  gateStabilizer hrig g` (given rigidity), which lets us lift the group-theoretic fact from
  `PatternsSupportLemma` from `Perm α` to `Γ n = Perm (Fin n) × Perm (Fin n)`;
* the key pairwise fact: if `S`, `T` support `g` and both have `ncard ≤ k` with `2 * k < n`,
  then `S ∩ T` supports `g` (`isSupport_inter_of_card_le`);
* a finite, pairwise-intersection-closed family of small supports, hence a `⊆`-least support
  among those of size `≤ supportSize C` (`exists_least_small_support`);
* equivariance of `IsSupport`/`minSupport` under the `Γ n`-action on gates coming from
  rigidity (`isSupport_smul`, `minSupport_smul`).

**Honesty note.** We were *not* able to show the literal statement `IsSupport C g
(minSupport C g)` (i.e. that the intersection of *all* supports, with no size bound, is itself
a support) from just `hred`, `hsym` and `2 * supportSize C < n`. The obstruction appears to be
real: at the level of bare `Γ n`-sets, two supports `S`, `T` of the same point can fail to have
`S ∩ T` as a support whenever `S ∪ T` is everything on some side (this is exactly why
`PatternsSupportLemma.fixingSubgroup_inter_le` needs that hypothesis), and we were unable to
rule out such configurations arising for an actual gate of a reduced matrix-symmetric circuit
(e.g. a `+`/`×` gate with several "symmetric" children can plausibly have a stabiliser that is
not a pointwise-fixing subgroup at all, such as a genuine Young-type subgroup of `Γ n`, which
can admit two incomparable "independent" supports whose intersection is not itself a support).
We therefore deliver the best fully-proved substitute: `exists_least_small_support`, the
`⊆`-least element among supports of size `≤ supportSize C`, together with
`minSupport_subset_least_small_support` relating it to `minSupport`. A later agent should use
`exists_least_small_support`'s witness in place of `minSupport` for the induction if the literal
statement about `minSupport` turns out not to be needed, or revisit this with more
circuit-specific structure than used here.
-/

namespace Lax461425Proofs.PatternsSupportBasic

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportAction

variable {V K : Type*}

/-! ### The output gate has empty minimal support -/

/-- If `z` is reached (via the child relation, read backwards) from every gate, then `z` is the
output gate: this is forced by acyclicity. -/
theorem out_unique {C : Circuit V K} {z : C.Gate}
    (hz : ∀ g, Relation.ReflTransGen (fun a b => 0 < C.wire b a) g z) : z = C.out := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp (hz C.out) with h | h
  · exact h
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp (C.reaches_out z) with h' | h'
  · exact h'.symm
  exact absurd (h.trans h') (C.acyclic C.out)

/-- Every circuit automorphism fixes the output gate. -/
theorem extends_fixes_out {C : Circuit V K} {σ : C.Gate ≃ C.Gate} {π : V → V}
    (h : Extends C σ π) : σ C.out = C.out := by
  apply out_unique
  intro g
  have hg : Relation.ReflTransGen (fun a b => 0 < C.wire b a) (σ.symm g) C.out := C.reaches_out _
  have hmap : ∀ {a b : C.Gate}, Relation.ReflTransGen (fun a b => 0 < C.wire b a) a b →
      Relation.ReflTransGen (fun a b => 0 < C.wire b a) (σ a) (σ b) := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact ih.tail (by rw [h.2]; exact hstep)
  have hfin := hmap hg
  simpa using hfin

variable {n : ℕ}

/-- The empty set supports the output gate: every circuit automorphism fixes it. -/
theorem isSupport_out_empty (C : Circuit (Fin n × Fin n) K) :
    IsSupport C C.out (∅ : Set (Fin n ⊕ Fin n)) :=
  fun _γ _σ _hfix hext => extends_fixes_out hext

/-- The output gate has empty minimal support. -/
theorem minSupport_out (C : Circuit (Fin n × Fin n) K) :
    minSupport C C.out = (∅ : Set (Fin n ⊕ Fin n)) :=
  Set.subset_empty_iff.mp
    (fun _x hx => hx ∅ (isSupport_out_empty C) (by simp))

variable {C : Circuit (Fin n × Fin n) K}

/-! ### `actPoint`/`actVar`/`σOf` cancellation facts -/

theorem actPoint_self_inv_apply (γ : Γ n) (x : Fin n ⊕ Fin n) :
    actPoint γ⁻¹ (actPoint γ x) = x := by
  have h : actPoint (γ⁻¹ * γ) x = x := by
    rw [inv_mul_cancel]; exact congrFun actPoint_one x
  rwa [actPoint_mul, Function.comp_apply] at h

theorem actPoint_inv_self_apply (γ : Γ n) (x : Fin n ⊕ Fin n) :
    actPoint γ (actPoint γ⁻¹ x) = x := by
  have h : actPoint (γ * γ⁻¹) x = x := by
    rw [mul_inv_cancel]; exact congrFun actPoint_one x
  rwa [actPoint_mul, Function.comp_apply] at h

/-- The canonical gate automorphism applied to `γ⁻¹` cancels that applied to `γ`. -/
theorem σOf_inv_σOf (hrig : IsRigid C) (γ : Γ n) (g : C.Gate) :
    σOf hrig γ⁻¹ (σOf hrig γ g) = g := by
  have h1 : σOf hrig γ⁻¹ * σOf hrig γ = 1 := by
    rw [← σOf_mul, inv_mul_cancel, σOf_one]
  have h2 := congrArg (fun e : Equiv.Perm C.Gate => e g) h1
  simpa [Equiv.Perm.mul_apply] using h2

theorem σOf_σOf_inv (hrig : IsRigid C) (γ : Γ n) (g : C.Gate) :
    σOf hrig γ (σOf hrig γ⁻¹ g) = g := by
  have h1 : σOf hrig γ * σOf hrig γ⁻¹ = 1 := by
    rw [← σOf_mul, mul_inv_cancel, σOf_one]
  have h2 := congrArg (fun e : Equiv.Perm C.Gate => e g) h1
  simpa [Equiv.Perm.mul_apply] using h2

/-! ### `IsSupport` as a subgroup inequality -/

/-- The "row" part of a subset of `[n] ⊎ [n]`. -/
def leftPart (S : Set (Fin n ⊕ Fin n)) : Set (Fin n) := {i | Sum.inl i ∈ S}

/-- The "column" part of a subset of `[n] ⊎ [n]`. -/
def rightPart (S : Set (Fin n ⊕ Fin n)) : Set (Fin n) := {j | Sum.inr j ∈ S}

theorem leftPart_inter (S T : Set (Fin n ⊕ Fin n)) :
    leftPart (S ∩ T) = leftPart S ∩ leftPart T := rfl

theorem rightPart_inter (S T : Set (Fin n ⊕ Fin n)) :
    rightPart (S ∩ T) = rightPart S ∩ rightPart T := rfl

/-- The pointwise stabiliser of `S` in `Γ n` splits as a product of the pointwise stabilisers of
its two sides in `Perm (Fin n)`. -/
theorem fixingSubgroupΓ_eq_prod (S : Set (Fin n ⊕ Fin n)) :
    fixingSubgroup (Γ n) S =
      (fixingSubgroup (Equiv.Perm (Fin n)) (leftPart S)).prod
        (fixingSubgroup (Equiv.Perm (Fin n)) (rightPart S)) := by
  apply Subgroup.ext
  intro γ
  constructor
  · intro hγ
    have hγ' : ∀ x ∈ S, actPoint γ x = x := by
      intro x hx
      have hraw := (mem_fixingSubgroup_iff (M := Γ n) (s := S) (m := γ)).mp hγ x hx
      rwa [smul_point_def] at hraw
    apply Subgroup.mem_prod.mpr
    refine ⟨?_, ?_⟩
    · apply (mem_fixingSubgroup_iff (M := Equiv.Perm (Fin n)) (s := leftPart S) (m := γ.1)).mpr
      intro i hi
      have hh := hγ' (Sum.inl i) hi
      have h2 : actPoint γ (Sum.inl i) = Sum.inl (γ.1 i) := rfl
      rw [h2] at hh
      exact Sum.inl_injective hh
    · apply (mem_fixingSubgroup_iff (M := Equiv.Perm (Fin n)) (s := rightPart S) (m := γ.2)).mpr
      intro j hj
      have hh := hγ' (Sum.inr j) hj
      have h2 : actPoint γ (Sum.inr j) = Sum.inr (γ.2 j) := rfl
      rw [h2] at hh
      exact Sum.inr_injective hh
  · intro hγ
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.mp hγ
    have h1' : ∀ i ∈ leftPart S, γ.1 i = i :=
      (mem_fixingSubgroup_iff (M := Equiv.Perm (Fin n)) (s := leftPart S) (m := γ.1)).mp h1
    have h2' : ∀ j ∈ rightPart S, γ.2 j = j :=
      (mem_fixingSubgroup_iff (M := Equiv.Perm (Fin n)) (s := rightPart S) (m := γ.2)).mp h2
    apply (mem_fixingSubgroup_iff (M := Γ n) (s := S) (m := γ)).mpr
    intro x hx
    rw [smul_point_def]
    cases x with
    | inl i =>
      rw [show actPoint γ (Sum.inl i) = Sum.inl (γ.1 i) from rfl, h1' i hx]
    | inr j =>
      rw [show actPoint γ (Sum.inr j) = Sum.inr (γ.2 j) from rfl, h2' j hx]

/-- In a product of groups, `(A ⊔ B).prod (P ⊔ Q) ≤ A.prod P ⊔ B.prod Q`. -/
theorem subgroup_prod_sup_prod_le {G H : Type*} [Group G] [Group H]
    (A B : Subgroup G) (P Q : Subgroup H) :
    (A ⊔ B).prod (P ⊔ Q) ≤ A.prod P ⊔ B.prod Q := by
  rw [Subgroup.prod_le_iff]
  constructor
  · rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact Subgroup.mem_sup_left (Subgroup.mem_prod.mpr ⟨ha, P.one_mem⟩)
    · rintro _ ⟨b, hb, rfl⟩
      exact Subgroup.mem_sup_right (Subgroup.mem_prod.mpr ⟨hb, Q.one_mem⟩)
  · rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩
      exact Subgroup.mem_sup_left (Subgroup.mem_prod.mpr ⟨A.one_mem, hp⟩)
    · rintro _ ⟨q, hq, rfl⟩
      exact Subgroup.mem_sup_right (Subgroup.mem_prod.mpr ⟨B.one_mem, hq⟩)

/-- The lift of `PatternsSupportLemma.fixingSubgroup_inter_le` from `Perm (Fin n)` to
`Γ n = Perm (Fin n) × Perm (Fin n)`. -/
theorem fixingSubgroupΓ_inter_le {S T : Set (Fin n ⊕ Fin n)}
    (hL : leftPart S ∪ leftPart T ≠ Set.univ) (hR : rightPart S ∪ rightPart T ≠ Set.univ) :
    fixingSubgroup (Γ n) (S ∩ T) ≤ fixingSubgroup (Γ n) S ⊔ fixingSubgroup (Γ n) T := by
  rw [fixingSubgroupΓ_eq_prod, fixingSubgroupΓ_eq_prod, fixingSubgroupΓ_eq_prod,
    leftPart_inter, rightPart_inter]
  refine le_trans (Subgroup.prod_mono (PatternsSupportLemma.fixingSubgroup_inter_le hL)
    (PatternsSupportLemma.fixingSubgroup_inter_le hR)) ?_
  exact subgroup_prod_sup_prod_le _ _ _ _

/-- The subgroup of `Γ n` fixing a given gate, via the canonical automorphisms `σOf hrig`. -/
def gateStabilizer (hrig : IsRigid C) (g : C.Gate) : Subgroup (Γ n) where
  carrier := {γ | σOf hrig γ g = g}
  one_mem' := by
    show σOf hrig 1 g = g
    rw [σOf_one]
    exact Equiv.Perm.one_apply g
  mul_mem' {a b} ha hb := by
    show σOf hrig (a * b) g = g
    rw [σOf_mul, Equiv.Perm.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    show σOf hrig a⁻¹ g = g
    have h1 : σOf hrig a⁻¹ * σOf hrig a = 1 := by
      rw [← σOf_mul, inv_mul_cancel, σOf_one]
    have h2 := congrArg (fun e : Equiv.Perm C.Gate => e g) h1
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h2
    rwa [ha] at h2

theorem mem_gateStabilizer_iff (hrig : IsRigid C) {g : C.Gate} {γ : Γ n} :
    γ ∈ gateStabilizer hrig g ↔ σOf hrig γ g = g := Iff.rfl

/-- Given rigidity, `IsSupport C g S` is the same as `fixingSubgroup (Γ n) S ≤
gateStabilizer hrig g`. -/
theorem isSupport_iff_fixingSubgroup_le (hrig : IsRigid C) (g : C.Gate)
    (S : Set (Fin n ⊕ Fin n)) :
    IsSupport C g S ↔ fixingSubgroup (Γ n) S ≤ gateStabilizer hrig g := by
  constructor
  · intro hS γ hγ
    rw [mem_gateStabilizer_iff]
    rw [mem_fixingSubgroup_iff] at hγ
    exact hS γ (σOf hrig γ) hγ (σOf_extends hrig γ)
  · intro hle γ σ hfix hext
    have hγmem : γ ∈ fixingSubgroup (Γ n) S := by
      rw [mem_fixingSubgroup_iff]; exact hfix
    have hstab : σOf hrig γ g = g := hle hγmem
    rw [σOf_unique hrig hext]
    exact hstab

/-! ### The key pairwise fact -/

/-- If `S` and `T` both support `g` and neither side of `S ∪ T` is everything, then `S ∩ T`
supports `g`. -/
theorem isSupport_inter (hrig : IsRigid C) {g : C.Gate} {S T : Set (Fin n ⊕ Fin n)}
    (hS : IsSupport C g S) (hT : IsSupport C g T)
    (hL : leftPart S ∪ leftPart T ≠ Set.univ) (hR : rightPart S ∪ rightPart T ≠ Set.univ) :
    IsSupport C g (S ∩ T) := by
  rw [isSupport_iff_fixingSubgroup_le hrig] at hS hT ⊢
  exact le_trans (fixingSubgroupΓ_inter_le hL hR) (sup_le hS hT)

theorem ncard_leftPart_le (S : Set (Fin n ⊕ Fin n)) : (leftPart S).ncard ≤ S.ncard := by
  have hsub : Sum.inl '' leftPart S ⊆ S := by rintro _ ⟨i, hi, rfl⟩; exact hi
  calc (leftPart S).ncard = (Sum.inl '' leftPart S).ncard :=
        (Set.ncard_image_of_injective _ Sum.inl_injective).symm
    _ ≤ S.ncard := Set.ncard_le_ncard hsub (Set.toFinite S)

theorem ncard_rightPart_le (S : Set (Fin n ⊕ Fin n)) : (rightPart S).ncard ≤ S.ncard := by
  have hsub : Sum.inr '' rightPart S ⊆ S := by rintro _ ⟨j, hj, rfl⟩; exact hj
  calc (rightPart S).ncard = (Sum.inr '' rightPart S).ncard :=
        (Set.ncard_image_of_injective _ Sum.inr_injective).symm
    _ ≤ S.ncard := Set.ncard_le_ncard hsub (Set.toFinite S)

/-- If `S` and `T` both support `g` and both have `ncard ≤ k` with `2 * k < n`, then `S ∩ T`
supports `g`. This is the main tool for showing small supports are closed under intersection. -/
theorem isSupport_inter_of_card_le (hrig : IsRigid C) {g : C.Gate} {S T : Set (Fin n ⊕ Fin n)}
    {k : ℕ} (hS : IsSupport C g S) (hT : IsSupport C g T) (hSc : S.ncard ≤ k)
    (hTc : T.ncard ≤ k) (hn : 2 * k < n) : IsSupport C g (S ∩ T) := by
  have hL : leftPart S ∪ leftPart T ≠ Set.univ := by
    intro hcon
    have h1 : (leftPart S ∪ leftPart T).ncard = n := by rw [hcon]; simp [Set.ncard_univ]
    have h2 : (leftPart S ∪ leftPart T).ncard ≤ (leftPart S).ncard + (leftPart T).ncard :=
      Set.ncard_union_le _ _
    have h3 := ncard_leftPart_le S
    have h4 := ncard_leftPart_le T
    omega
  have hR : rightPart S ∪ rightPart T ≠ Set.univ := by
    intro hcon
    have h1 : (rightPart S ∪ rightPart T).ncard = n := by rw [hcon]; simp [Set.ncard_univ]
    have h2 : (rightPart S ∪ rightPart T).ncard ≤ (rightPart S).ncard + (rightPart T).ncard :=
      Set.ncard_union_le _ _
    have h3 := ncard_rightPart_le S
    have h4 := ncard_rightPart_le T
    omega
  exact isSupport_inter hrig hS hT hL hR

/-! ### `supportSize` is realised -/

theorem actPoint_eq_id_iff {γ : Γ n} : actPoint γ = id ↔ γ = 1 := by
  constructor
  · intro h
    have h1 : γ.1 = 1 := by
      apply Equiv.ext
      intro i
      have hh := congrFun h (Sum.inl i)
      simp only [actPoint, id, Sum.map_inl] at hh
      rw [Equiv.Perm.one_apply]
      exact Sum.inl_injective hh
    have h2 : γ.2 = 1 := by
      apply Equiv.ext
      intro j
      have hh := congrFun h (Sum.inr j)
      simp only [actPoint, id, Sum.map_inr] at hh
      rw [Equiv.Perm.one_apply]
      exact Sum.inr_injective hh
    exact Prod.ext h1 h2
  · rintro rfl
    exact actPoint_one

/-- `Set.univ` (trivially) supports every gate, given rigidity. -/
theorem isSupport_univ (hrig : IsRigid C) (g : C.Gate) :
    IsSupport C g (Set.univ : Set (Fin n ⊕ Fin n)) := by
  intro γ σ hfix hext
  have hid : actPoint γ = id := funext fun x => hfix x (Set.mem_univ x)
  have hγ1 : γ = 1 := actPoint_eq_id_iff.mp hid
  subst hγ1
  rw [σOf_unique hrig hext, σOf_one]
  exact Equiv.Perm.one_apply g

/-- `supportSize C` is realised: every gate has an actual support of size `≤ supportSize C`. -/
theorem supportSize_spec (hrig : IsRigid C) (g : C.Gate) :
    ∃ S, IsSupport C g S ∧ S.ncard ≤ supportSize C := by
  have hne : ({k | ∀ g', ∃ S, IsSupport C g' S ∧ S.ncard ≤ k} : Set ℕ).Nonempty :=
    ⟨(Set.univ : Set (Fin n ⊕ Fin n)).ncard,
      fun g' => ⟨Set.univ, isSupport_univ hrig g', le_refl _⟩⟩
  exact Nat.sInf_mem hne g

/-! ### The least small support -/

/-- Among supports of `g` with `ncard ≤ supportSize C`, there is a `⊆`-least one, provided
`2 * supportSize C < n`. -/
theorem exists_least_small_support (hrig : IsRigid C) (hn : 2 * supportSize C < n)
    (g : C.Gate) :
    ∃ T : Set (Fin n ⊕ Fin n), IsSupport C g T ∧ T.ncard ≤ supportSize C ∧
      ∀ S, IsSupport C g S → S.ncard ≤ supportSize C → T ⊆ S := by
  classical
  obtain ⟨T0, hT0S, hT0c⟩ := supportSize_spec hrig g
  have hT0mem : T0 ∈ {T : Set (Fin n ⊕ Fin n) | IsSupport C g T ∧ T.ncard ≤ supportSize C} :=
    ⟨hT0S, hT0c⟩
  have hne : {T : Set (Fin n ⊕ Fin n) | IsSupport C g T ∧ T.ncard ≤ supportSize C}.Nonempty :=
    ⟨T0, hT0mem⟩
  have h𝒢fin : {T : Set (Fin n ⊕ Fin n) | IsSupport C g T ∧ T.ncard ≤ supportSize C}.Finite :=
    Set.toFinite _
  -- Any nonempty subfamily of small supports has its intersection still a small support.
  have main : ∀ s : Finset (Set (Fin n ⊕ Fin n)), ∀ (_ : s.Nonempty),
      (↑s : Set (Set (Fin n ⊕ Fin n))) ⊆
        {T | IsSupport C g T ∧ T.ncard ≤ supportSize C} →
      IsSupport C g (⋂ T ∈ s, T) ∧ (⋂ T ∈ s, T).ncard ≤ supportSize C := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton T =>
      intro hsub
      have hT := hsub (show T ∈ (↑({T} : Finset _) : Set _) by simp)
      simpa using hT
    | cons T s hT hs ih =>
      intro hsub
      have hTmem : T ∈ {U | IsSupport C g U ∧ U.ncard ≤ supportSize C} :=
        hsub (show T ∈ (↑(Finset.cons T s hT) : Set _) by simp)
      have hssub : (↑s : Set (Set (Fin n ⊕ Fin n))) ⊆
          {U | IsSupport C g U ∧ U.ncard ≤ supportSize C} := by
        intro U hU
        exact hsub (show U ∈ (↑(Finset.cons T s hT) : Set _) by simp [hU])
      obtain ⟨ihS, ihc⟩ := ih hssub
      have hinterEq : (⋂ U ∈ Finset.cons T s hT, U) = T ∩ ⋂ U ∈ s, U := by
        simp
      rw [hinterEq]
      refine ⟨isSupport_inter_of_card_le hrig hTmem.1 ihS hTmem.2 ihc hn, ?_⟩
      exact le_trans (Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)) ihc
  obtain ⟨sF, hsFeq⟩ := h𝒢fin.exists_finset_coe
  have hsFne : sF.Nonempty := by
    rw [← Finset.coe_nonempty, hsFeq]; exact hne
  have hsFsub : (↑sF : Set (Set (Fin n ⊕ Fin n))) ⊆
      {T | IsSupport C g T ∧ T.ncard ≤ supportSize C} := by rw [hsFeq]
  obtain ⟨hTstarS, hTstarc⟩ := main sF hsFne hsFsub
  refine ⟨⋂ T ∈ sF, T, hTstarS, hTstarc, ?_⟩
  intro S hS hSc
  have hSmem : S ∈ {T : Set (Fin n ⊕ Fin n) | IsSupport C g T ∧ T.ncard ≤ supportSize C} :=
    ⟨hS, hSc⟩
  have hSmem' : S ∈ (↑sF : Set (Set (Fin n ⊕ Fin n))) := by rw [hsFeq]; exact hSmem
  exact Set.biInter_subset_of_mem (Finset.mem_coe.mp hSmem')

/-- The intersection of all BOUNDED-size supports of `g` is contained in every bounded-size
support (in particular in every "least small support" as constructed by
`exists_least_small_support`). -/
theorem minSupport_subset_of_isSupport {g : C.Gate} {T : Set (Fin n ⊕ Fin n)}
    (hT : IsSupport C g T) (hTc : T.ncard ≤ supportSize C) : minSupport C g ⊆ T :=
  fun _x hx => hx T hT hTc

/-- `actPoint γ` is injective: it is `Sum.map γ.1 γ.2` applied to two bijections. -/
theorem actPoint_injective (γ : Γ n) : Function.Injective (actPoint γ) :=
  γ.1.injective.sumMap γ.2.injective

/-- Applying `actPoint γ` to a set does not change its cardinality. -/
theorem ncard_actPoint_image (γ : Γ n) (S : Set (Fin n ⊕ Fin n)) :
    (actPoint γ '' S).ncard = S.ncard :=
  Set.ncard_image_of_injective S (actPoint_injective γ)

/-! ### Equivariance -/

/-- `IsSupport` is equivariant under the `Γ n`-action on gates coming from rigidity. -/
theorem isSupport_smul (hrig : IsRigid C) (γ : Γ n) {g : C.Gate} {S : Set (Fin n ⊕ Fin n)}
    (hS : IsSupport C g S) : IsSupport C (σOf hrig γ g) (actPoint γ '' S) := by
  intro γ' σ' hfix' hext'
  set δ := γ⁻¹ * γ' * γ with hδ
  have hδfix : ∀ x ∈ S, actPoint δ x = x := by
    intro x hx
    have h1 : actPoint γ' (actPoint γ x) = actPoint γ x := hfix' _ ⟨x, hx, rfl⟩
    have e1 : actPoint δ x = actPoint γ⁻¹ (actPoint γ' (actPoint γ x)) := by
      show actPoint (γ⁻¹ * γ' * γ) x = actPoint γ⁻¹ (actPoint γ' (actPoint γ x))
      rw [mul_assoc, actPoint_mul, Function.comp_apply, actPoint_mul, Function.comp_apply]
    rw [e1, h1, actPoint_self_inv_apply]
  have hgfix : σOf hrig δ g = g := hS δ (σOf hrig δ) hδfix (σOf_extends hrig δ)
  have hσ'eq : σ' = σOf hrig γ' := σOf_unique hrig hext'
  have hδeq : σOf hrig δ = σOf hrig γ⁻¹ * σ' * σOf hrig γ := by
    rw [hδ, σOf_mul, σOf_mul, hσ'eq]
  rw [hδeq] at hgfix
  have hcancel : σOf hrig γ * σOf hrig γ⁻¹ = 1 := by
    rw [← σOf_mul, mul_inv_cancel, σOf_one]
  have hc := congrArg (σOf hrig γ) hgfix
  rw [← Equiv.Perm.mul_apply] at hc
  simp only [← mul_assoc] at hc
  rw [hcancel, one_mul, Equiv.Perm.mul_apply] at hc
  exact hc

/-- `minSupport` is equivariant under the `Γ n`-action on gates coming from rigidity. -/
theorem minSupport_smul (hrig : IsRigid C) (γ : Γ n) (g : C.Gate) :
    minSupport C (σOf hrig γ g) = actPoint γ '' minSupport C g := by
  ext x
  simp only [Set.mem_image]
  constructor
  · intro hx
    refine ⟨actPoint γ⁻¹ x, ?_, actPoint_inv_self_apply γ x⟩
    intro S hS hSc
    have hS' : IsSupport C (σOf hrig γ g) (actPoint γ '' S) := isSupport_smul hrig γ hS
    have hS'c : (actPoint γ '' S).ncard ≤ supportSize C := (ncard_actPoint_image γ S).le.trans hSc
    obtain ⟨z, hz, hzx⟩ := hx (actPoint γ '' S) hS' hS'c
    rw [← hzx, actPoint_self_inv_apply]
    exact hz
  · rintro ⟨y, hy, rfl⟩
    intro S' hS' hS'c
    have hSγ : IsSupport C g (actPoint γ⁻¹ '' S') := by
      have hraw := isSupport_smul hrig γ⁻¹ hS'
      rwa [σOf_inv_σOf hrig γ g] at hraw
    have hSγc : (actPoint γ⁻¹ '' S').ncard ≤ supportSize C :=
      (ncard_actPoint_image γ⁻¹ S').le.trans hS'c
    obtain ⟨z, hz, hzy⟩ := hy _ hSγ hSγc
    rw [← hzy, actPoint_inv_self_apply]
    exact hz

end Lax461425Proofs.PatternsSupportBasic
