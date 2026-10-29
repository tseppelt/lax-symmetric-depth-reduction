import Mathlib.Data.Finset.Sort
import Lax461425Proofs.PatternsSupportBasic
import Lax461425Proofs.PatternsSupportDepth

/-!
Setup for `lem:induction` (the gate-by-gate induction underlying `mem_span_hom`).

**Design choice on indexing.** The paper indexes the labels used at a gate `g` by the *actual*
sizes `|sup_L(g)|, |sup_R(g)|` of the two sides of `sup(g)`, which vary from gate to gate. We keep
this variable-length indexing (rather than padding every gate's labels to a fixed width `k`):
padding to a fixed `k` throughout would make it impossible to "make room" for the genuinely new
label positions `N(h) = sup(h) \ sup(g)` that appear when descending from a gate `g` to a child
`h` (the whole point of the `Δ`-depth increase at a support-changing wire), since a fixed-width
label vector has no spare, semantically meaningful room for those new entries without already
colliding with the padding machinery for *unrelated* purposes. So: every gate `g` gets its own
`ℓ_g := (leftPart (supOf g)).ncard`, `r_g := (rightPart (supOf g)).ncard`, each `≤ supportSize C`.

To avoid the induction's statement having to carry a single canonical, globally-fixed
enumeration function of each gate's support (which would force reconciling the specific
enumeration chosen at a gate `g` against the ones chosen at each of its children, an unnecessary
rigidity), we instead state everything relative to *some* injective enumeration matching the
support's range, and provide `exists_perm_of_range_eq`: any two injective functions `Fin m → Fin
n` with the same range differ by a permutation of `Fin m`. Combined with `PatternsLabelledOps`'s
`relabel` (which transports `InClass`/`InClassP` membership along such a permutation, leaving the
represented homomorphism-polynomial value process unchanged up to precisely that reindexing),
this lets every step of the induction pick whichever enumeration is locally convenient.
-/

namespace Lax461425Proofs.PatternsInductionSetup

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open Lax461425Proofs.PatternsSupportDepth

/-! ### Enumerating a finite subset of `Fin n` -/

variable {n : ℕ}

/-- The (noncomputable) `Finset` underlying a set `S : Set (Fin n)` (always finite, since
`Fin n` is finite). -/
noncomputable def finsetOf (S : Set (Fin n)) : Finset (Fin n) := (Set.toFinite S).toFinset

theorem mem_finsetOf {S : Set (Fin n)} {x : Fin n} : x ∈ finsetOf S ↔ x ∈ S :=
  Set.Finite.mem_toFinset _

theorem card_finsetOf (S : Set (Fin n)) : (finsetOf S).card = S.ncard :=
  (Set.ncard_eq_toFinset_card S (Set.toFinite S)).symm

/-- A canonical enumeration of a finite set `S : Set (Fin n)` by `Fin S.ncard`, as an order
embedding (in particular, injective) with range exactly `S`. -/
noncomputable def enumOf (S : Set (Fin n)) : Fin S.ncard ↪o Fin n :=
  (card_finsetOf S) ▸ (finsetOf S).orderEmbOfFin rfl

theorem range_enumOf (S : Set (Fin n)) : Set.range (enumOf S) = S := by
  have hcast : ∀ {m m' : ℕ} (h : m = m') (f : Fin m ↪o Fin n),
      Set.range (h ▸ f : Fin m' ↪o Fin n) = Set.range f := by
    rintro m m' rfl f; rfl
  show Set.range ((card_finsetOf S) ▸ (finsetOf S).orderEmbOfFin rfl) = S
  rw [hcast (card_finsetOf S) ((finsetOf S).orderEmbOfFin rfl), Finset.range_orderEmbOfFin]
  ext x
  rw [Finset.mem_coe, mem_finsetOf]

theorem enumOf_injective (S : Set (Fin n)) : Function.Injective (enumOf S) :=
  (enumOf S).injective

/-- Any two injective functions `Fin m → Fin n` with the same range differ by a permutation of
`Fin m`: the reindexing needed to transport a construction built against one enumeration of a
finite subset of `Fin n` to any other. -/
theorem exists_perm_of_range_eq {m : ℕ} {f g : Fin m → Fin n} (hf : Function.Injective f)
    (hg : Function.Injective g) (hrange : Set.range f = Set.range g) :
    ∃ σ : Equiv.Perm (Fin m), g = f ∘ σ := by
  set ef : Fin m ≃ Set.range f := Equiv.ofInjective f hf with hef
  set eg : Fin m ≃ Set.range g := Equiv.ofInjective g hg with heg
  set castEquiv : Set.range g ≃ Set.range f := Equiv.setCongr hrange.symm with hcastEquiv
  refine ⟨(eg.trans castEquiv).trans ef.symm, ?_⟩
  funext x
  show g x = f (ef.symm (castEquiv (eg x)))
  have hval : (ef (ef.symm (castEquiv (eg x))) : Fin n) = (castEquiv (eg x) : Fin n) :=
    congrArg Subtype.val (ef.apply_symm_apply _)
  have heq1 : (ef (ef.symm (castEquiv (eg x))) : Fin n) = f (ef.symm (castEquiv (eg x))) := rfl
  have heq2 : (castEquiv (eg x) : Fin n) = (eg x : Fin n) := by
    simp [hcastEquiv, Equiv.setCongr_apply]
  have heq3 : (eg x : Fin n) = g x := rfl
  rw [heq1, heq2, heq3] at hval
  exact hval.symm

/-! ### `supOf`: the least small support of a gate, packaged -/

variable {K : Type*} [Field K] {C : Circuit (Fin n × Fin n) K}

/-- `supOf hrig hn g`: the `⊆`-least support of `g` among those of size `≤ supportSize C`,
witnessed by `exists_least_small_support`. This is the object the induction calls `sup(g)`. -/
noncomputable def supOf (hrig : IsRigid C) (hn : 2 * supportSize C < n) (g : C.Gate) :
    Set (Fin n ⊕ Fin n) :=
  (exists_least_small_support hrig hn g).choose

omit [Field K] in
theorem isSupport_supOf (hrig : IsRigid C) (hn : 2 * supportSize C < n) (g : C.Gate) :
    IsSupport C g (supOf hrig hn g) :=
  (exists_least_small_support hrig hn g).choose_spec.1

omit [Field K] in
theorem ncard_supOf_le (hrig : IsRigid C) (hn : 2 * supportSize C < n) (g : C.Gate) :
    (supOf hrig hn g).ncard ≤ supportSize C :=
  (exists_least_small_support hrig hn g).choose_spec.2.1

omit [Field K] in
/-- `supOf hrig hn g` is contained in every support of `g` of size `≤ supportSize C`: the
"least small support" property. -/
theorem supOf_subset (hrig : IsRigid C) (hn : 2 * supportSize C < n) (g : C.Gate)
    {S : Set (Fin n ⊕ Fin n)} (hS : IsSupport C g S) (hSc : S.ncard ≤ supportSize C) :
    supOf hrig hn g ⊆ S :=
  (exists_least_small_support hrig hn g).choose_spec.2.2 S hS hSc

omit [Field K] in
/-- The left side of `supOf hrig hn g` has at most `supportSize C` elements. -/
theorem ncard_leftPart_supOf_le (hrig : IsRigid C) (hn : 2 * supportSize C < n) (g : C.Gate) :
    (leftPart (supOf hrig hn g)).ncard ≤ supportSize C :=
  (ncard_leftPart_le _).trans (ncard_supOf_le hrig hn g)

omit [Field K] in
/-- The right side of `supOf hrig hn g` has at most `supportSize C` elements. -/
theorem ncard_rightPart_supOf_le (hrig : IsRigid C) (hn : 2 * supportSize C < n) (g : C.Gate) :
    (rightPart (supOf hrig hn g)).ncard ≤ supportSize C :=
  (ncard_rightPart_le _).trans (ncard_supOf_le hrig hn g)

/-! ### A canonical enumeration of a gate's support -/

/-- The number of left labels needed at `g`: `|sup_L(g)|`. -/
noncomputable def leftCard (hrig : IsRigid C) (hn : 2 * supportSize C < n) (g : C.Gate) : ℕ :=
  (leftPart (supOf hrig hn g)).ncard

/-- The number of right labels needed at `g`: `|sup_R(g)|`. -/
noncomputable def rightCard (hrig : IsRigid C) (hn : 2 * supportSize C < n) (g : C.Gate) : ℕ :=
  (rightPart (supOf hrig hn g)).ncard

/-- A canonical enumeration of `sup_L(g)`, injective, with range exactly `sup_L(g)`. -/
noncomputable def leftEnum (hrig : IsRigid C) (hn : 2 * supportSize C < n) (g : C.Gate) :
    Fin (leftCard hrig hn g) → Fin n :=
  enumOf (leftPart (supOf hrig hn g))

/-- A canonical enumeration of `sup_R(g)`, injective, with range exactly `sup_R(g)`. -/
noncomputable def rightEnum (hrig : IsRigid C) (hn : 2 * supportSize C < n) (g : C.Gate) :
    Fin (rightCard hrig hn g) → Fin n :=
  enumOf (rightPart (supOf hrig hn g))

omit [Field K] in
theorem leftEnum_injective (hrig : IsRigid C) (hn : 2 * supportSize C < n) (g : C.Gate) :
    Function.Injective (leftEnum hrig hn g) :=
  enumOf_injective _

omit [Field K] in
theorem rightEnum_injective (hrig : IsRigid C) (hn : 2 * supportSize C < n) (g : C.Gate) :
    Function.Injective (rightEnum hrig hn g) :=
  enumOf_injective _

omit [Field K] in
theorem range_leftEnum (hrig : IsRigid C) (hn : 2 * supportSize C < n) (g : C.Gate) :
    Set.range (leftEnum hrig hn g) = leftPart (supOf hrig hn g) :=
  range_enumOf _

omit [Field K] in
theorem range_rightEnum (hrig : IsRigid C) (hn : 2 * supportSize C < n) (g : C.Gate) :
    Set.range (rightEnum hrig hn g) = rightPart (supOf hrig hn g) :=
  range_enumOf _

omit [Field K] in
theorem leftCard_le (hrig : IsRigid C) (hn : 2 * supportSize C < n) (g : C.Gate) :
    leftCard hrig hn g ≤ supportSize C :=
  ncard_leftPart_supOf_le hrig hn g

omit [Field K] in
theorem rightCard_le (hrig : IsRigid C) (hn : 2 * supportSize C < n) (g : C.Gate) :
    rightCard hrig hn g ≤ supportSize C :=
  ncard_rightPart_supOf_le hrig hn g

/-! ### `sc` vanishes at gates with no children -/

omit [Field K] in
/-- An input gate (no children, since `C.wire_eq_zero_of_isInput`) has `sc C g = 0`: the only
path starting at `g` is the trivial, length-`0` path. -/
theorem sc_eq_zero_of_isInput {g : C.Gate} (hinput : (C.label g).IsInput) : sc C g = 0 := by
  apply le_antisymm _ (Nat.zero_le _)
  apply csSup_le (sc_set_nonempty g)
  rintro c ⟨m, p, hp0, hpath, rfl⟩
  match m with
  | 0 =>
      show ({i : Fin 0 | _} : Set (Fin 0)).ncard ≤ 0
      rw [show ({i : Fin 0 | ¬ minSupport C (p i.succ) ⊆ minSupport C (p i.castSucc)} :
          Set (Fin 0)) = ∅ from Set.eq_empty_iff_forall_notMem.mpr (fun i _ => i.elim0)]
      simp
  | (m' + 1) =>
      exfalso
      have hstep : 0 < C.wire (p (0 : Fin (m' + 1)).castSucc) (p (0 : Fin (m' + 1)).succ) :=
        hpath 0
      have hcast0 : (0 : Fin (m' + 1)).castSucc = (0 : Fin (m' + 2)) := rfl
      rw [hcast0, hp0] at hstep
      rw [C.wire_eq_zero_of_isInput g _ hinput] at hstep
      exact absurd hstep (lt_irrefl 0)

end Lax461425Proofs.PatternsInductionSetup
