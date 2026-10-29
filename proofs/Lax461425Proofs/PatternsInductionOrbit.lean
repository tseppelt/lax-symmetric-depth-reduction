import Lax461425Proofs.PatternsInductionSetup
import Lax461425Proofs.PatternsSupportDepth

/-!
Orbit-decomposition groundwork for `lem:induction`'s internal-gate case (the step that handles
children `h` of a gate `g` whose wire is *support-changing*, i.e. `¬ minSupport C h ⊆ minSupport
C g`).

We establish three equivariance facts about the `Γₙ`-action on gates coming from rigidity
(`PatternsSupportAction.σOf`), none of which were previously available:

* **`wire_eq_of_mem_gateStabilizer`**: every `γ ∈ gateStabilizer hrig g` permutes the children of
  `g` (as a set, via `σOf hrig γ`), *preserving wire multiplicity exactly*
  (`C.wire g (σOf hrig γ h) = C.wire g h`), not merely whether a wire is present. This is what
  makes `gateStabilizer hrig g`'s action on `{h // 0 < C.wire g h}` meaningful: children in a
  single orbit all carry the same wire multiplicity into `g`.
* **`sc_smul`**: `sc C (σOf hrig γ g) = sc C g` for *every* `γ : Γ n` (not just those stabilizing
  `g`): applying a circuit automorphism to every gate on a witnessing path produces another path
  with the exact same `supportChanges` count (`minSupport` is equivariant, and `actPoint γ` is
  injective, so the defining `⊆`-conditions transport literally, index-for-index). In particular
  children related by an element of `gateStabilizer hrig g` have the same `sc`.
* **`supOf_smul`**: `supOf hrig hn (σOf hrig γ g) = actPoint γ '' (supOf hrig hn g)`: `supOf` (the
  `⊆`-least support of size `≤ supportSize C`) is *itself* equivariant, via the uniqueness of the
  defining "least small support" property (`least_small_support_unique`) combined with
  `isSupport_smul`/`ncard_actPoint_image`.

**Honesty note on scope.** This file supplies the orbit-theoretic groundwork described in the
task (children of a fixed gate split into `gateStabilizer`-orbits, with wire multiplicity and
`sc` constant across an orbit). It does *not* complete the sum-gate/product-gate elimination
step itself. Attempting to push through to that step surfaced what looks like a genuine
obstruction worth recording precisely (see the report accompanying this commit): the natural
plan is to feed a single orbit representative's induction-hypothesis witness `φ` (a function of
*arbitrary* injective label assignments, known to equal the representative's computed polynomial
only at *one* specific point) into `PatternsRestrictedSum.exists_ψSum`/
`PatternsRestrictedProd.exists_ψProd`, whose conclusions describe `ψSum(v,w)`/`ψProd(v,w)` via a
partition of `Y ℓ' r' n v w` — the set of *all* injective extensions of `(v,w)` by `ℓ'`/`r'` new
values in `Fin n` — into uniform-size blocks on which `φ` is constant. But `Y ℓ' r' n v w` is
generically far larger (growing with `n`, which is unbounded by the hypotheses) than the number
of actual circuit gates in the orbit, and a hom-polynomial of a fixed finite graph with edges
touching the new label positions is generically *non-constant*, in fact injective-ish, across
distinct injective completions (different completions produce different monomials
`X(a, y_i)`). So the only uniform block size available in general is `c = 1`, forcing
`ψSum(v,w)`/`ψProd(v,w)` to equal a sum/product over *all* of `Y(v,w)` — not just the (far
smaller, circuit-dependent) set of completions that correspond to actual sibling gates in the
orbit. Reconciling this (most likely via a stronger invariant than "`φ` matches the computed
polynomial at one point", e.g. some equivariance of `φ` itself under `gateStabilizer hrig g`, or
a different accounting that does not evaluate `φ` away from real completions at all) needs either
consulting the published proof of `lem:restricted`/`lem:induction` directly or substantially more
exploration than could be completed here. A later agent should start from the equivariance facts
in this file.
-/

namespace Lax461425Proofs.PatternsInductionOrbit

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open Lax461425Proofs.PatternsSupportDepth Lax461425Proofs.PatternsInductionSetup

variable {K : Type*} [Field K] {n : ℕ} {C : Circuit (Fin n × Fin n) K}

/-! ### Wire multiplicity is preserved by `gateStabilizer` -/

omit [Field K] in
/-- Every `γ ∈ gateStabilizer hrig g` preserves the wire multiplicity from `g` to any gate `h`,
when `h` is replaced by its image `σOf hrig γ h`: in particular `σOf hrig γ` permutes the
(multi)set of children of `g`. This is the exact sense in which `gateStabilizer hrig g` acts on
`g`'s children "preserving wire multiplicity". -/
theorem wire_eq_of_mem_gateStabilizer (hrig : IsRigid C) {g : C.Gate} {γ : Γ n}
    (hγ : γ ∈ gateStabilizer hrig g) (h : C.Gate) :
    C.wire g (σOf hrig γ h) = C.wire g h := by
  have hwire : C.wire (σOf hrig γ g) (σOf hrig γ h) = C.wire g h := (σOf_extends hrig γ).2 g h
  rwa [mem_gateStabilizer_iff hrig |>.mp hγ] at hwire

/-! ### `sc` is equivariant under the whole `Γ n`-action -/

omit [Field K] in
/-- Composing a witnessing path with a circuit automorphism `σOf hrig γ` gives another path. -/
theorem isPath_comp_σOf (hrig : IsRigid C) (γ : Γ n) {m : ℕ} {p : Fin (m + 1) → C.Gate}
    (hp : C.IsPath p) : C.IsPath (σOf hrig γ ∘ p) := by
  intro i
  show 0 < C.wire (σOf hrig γ (p i.castSucc)) (σOf hrig γ (p i.succ))
  rw [(σOf_extends hrig γ).2 (p i.castSucc) (p i.succ)]
  exact hp i

omit [Field K] in
/-- Composing a witnessing path with a circuit automorphism `σOf hrig γ` leaves the
`supportChanges` count exactly unchanged: `minSupport` transports along `actPoint γ`
(`minSupport_smul`), and `actPoint γ`'s injectivity turns the `⊆`-condition defining each
support-changing index into a literal `iff`, so the two defining index *sets* (not just their
cardinalities) coincide. -/
theorem supportChanges_comp_σOf (hrig : IsRigid C) (γ : Γ n) {m : ℕ} {p : Fin (m + 1) → C.Gate} :
    supportChanges C (σOf hrig γ ∘ p) = supportChanges C p := by
  have hset : ∀ i : Fin m,
      (¬ minSupport C ((σOf hrig γ ∘ p) i.succ) ⊆ minSupport C ((σOf hrig γ ∘ p) i.castSucc)) ↔
        ¬ minSupport C (p i.succ) ⊆ minSupport C (p i.castSucc) := by
    intro i
    show (¬ minSupport C (σOf hrig γ (p i.succ)) ⊆ minSupport C (σOf hrig γ (p i.castSucc))) ↔ _
    rw [minSupport_smul hrig γ (p i.succ), minSupport_smul hrig γ (p i.castSucc)]
    rw [Set.image_subset_image_iff (actPoint_injective γ)]
  show ({i : Fin m | ¬ minSupport C ((σOf hrig γ ∘ p) i.succ) ⊆
      minSupport C ((σOf hrig γ ∘ p) i.castSucc)} : Set (Fin m)).ncard
      = ({i : Fin m | ¬ minSupport C (p i.succ) ⊆ minSupport C (p i.castSucc)} :
        Set (Fin m)).ncard
  congr 1
  exact Set.ext hset

omit [Field K] in
/-- The defining candidate-set of `sc C (σOf hrig γ g)` equals that of `sc C g`: a path witnesses
one iff its image under `σOf hrig γ` (resp. `σOf hrig γ⁻¹`) witnesses the other, with the same
`supportChanges` count. -/
theorem sc_candidateSet_smul (hrig : IsRigid C) (γ : Γ n) (g : C.Gate) :
    {c | ∃ (m : ℕ) (p : Fin (m + 1) → C.Gate), p 0 = σOf hrig γ g ∧ C.IsPath p ∧
        supportChanges C p = c}
      = {c | ∃ (m : ℕ) (p : Fin (m + 1) → C.Gate), p 0 = g ∧ C.IsPath p ∧ supportChanges C p = c} := by
  ext c
  constructor
  · rintro ⟨m, p, hp0, hpath, hpc⟩
    refine ⟨m, σOf hrig γ⁻¹ ∘ p, ?_, isPath_comp_σOf hrig γ⁻¹ hpath, ?_⟩
    · show σOf hrig γ⁻¹ (p 0) = g
      rw [hp0, σOf_inv_σOf]
    · rw [supportChanges_comp_σOf hrig γ⁻¹, hpc]
  · rintro ⟨m, p, hp0, hpath, hpc⟩
    refine ⟨m, σOf hrig γ ∘ p, ?_, isPath_comp_σOf hrig γ hpath, ?_⟩
    · show σOf hrig γ (p 0) = σOf hrig γ g
      rw [hp0]
    · rw [supportChanges_comp_σOf hrig γ, hpc]

omit [Field K] in
/-- **`sc` is equivariant under the whole `Γ n`-action coming from rigidity.** -/
theorem sc_smul (hrig : IsRigid C) (γ : Γ n) (g : C.Gate) :
    sc C (σOf hrig γ g) = sc C g := by
  unfold Lax461425Proofs.PatternsSupportDepth.sc
  rw [sc_candidateSet_smul hrig γ g]

omit [Field K] in
/-- Children related by an element of `gateStabilizer hrig g` (i.e. in the same orbit of `g`'s
children under `gateStabilizer hrig g`) have the same `sc`. -/
theorem sc_eq_of_mem_gateStabilizer (hrig : IsRigid C) (γ : Γ n) (h : C.Gate) :
    sc C (σOf hrig γ h) = sc C h :=
  sc_smul hrig γ h

/-! ### `supOf` is equivariant under the whole `Γ n`-action -/

omit [Field K] in
/-- The "least small support" property determines its witness uniquely. -/
theorem least_small_support_unique {g : C.Gate} {T T' : Set (Fin n ⊕ Fin n)}
    (hT : IsSupport C g T ∧ T.ncard ≤ supportSize C ∧
      ∀ S, IsSupport C g S → S.ncard ≤ supportSize C → T ⊆ S)
    (hT' : IsSupport C g T' ∧ T'.ncard ≤ supportSize C ∧
      ∀ S, IsSupport C g S → S.ncard ≤ supportSize C → T' ⊆ S) :
    T = T' :=
  Set.Subset.antisymm (hT.2.2 T' hT'.1 hT'.2.1) (hT'.2.2 T hT.1 hT.2.1)

omit [Field K] in
/-- **`supOf` is equivariant under the whole `Γ n`-action coming from rigidity.** -/
theorem supOf_smul (hrig : IsRigid C) (hn : 2 * supportSize C < n) (γ : Γ n) (g : C.Gate) :
    supOf hrig hn (σOf hrig γ g) = actPoint γ '' (supOf hrig hn g) := by
  have hprop : IsSupport C (σOf hrig γ g) (actPoint γ '' supOf hrig hn g) ∧
      (actPoint γ '' supOf hrig hn g).ncard ≤ supportSize C ∧
      ∀ S, IsSupport C (σOf hrig γ g) S → S.ncard ≤ supportSize C →
        (actPoint γ '' supOf hrig hn g) ⊆ S := by
    refine ⟨isSupport_smul hrig γ (isSupport_supOf hrig hn g), ?_, ?_⟩
    · rw [ncard_actPoint_image]
      exact ncard_supOf_le hrig hn g
    · intro S hS hSc
      have hS0 : IsSupport C g (actPoint γ⁻¹ '' S) := by
        have hraw := isSupport_smul hrig γ⁻¹ hS
        rwa [σOf_inv_σOf hrig γ g] at hraw
      have hS0c : (actPoint γ⁻¹ '' S).ncard ≤ supportSize C := by
        rwa [ncard_actPoint_image]
      have hsub : supOf hrig hn g ⊆ actPoint γ⁻¹ '' S := supOf_subset hrig hn g hS0 hS0c
      have himg : actPoint γ '' (supOf hrig hn g) ⊆ actPoint γ '' (actPoint γ⁻¹ '' S) :=
        Set.image_mono hsub
      have himgeq : actPoint γ '' (actPoint γ⁻¹ '' S) = S := by
        ext x
        simp only [Set.mem_image]
        constructor
        · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
          rwa [actPoint_inv_self_apply]
        · intro hx
          exact ⟨actPoint γ⁻¹ x, ⟨x, hx, rfl⟩, actPoint_inv_self_apply γ x⟩
      rwa [himgeq] at himg
  have hspecProp : IsSupport C (σOf hrig γ g) (supOf hrig hn (σOf hrig γ g)) ∧
      (supOf hrig hn (σOf hrig γ g)).ncard ≤ supportSize C ∧
      ∀ S, IsSupport C (σOf hrig γ g) S → S.ncard ≤ supportSize C →
        supOf hrig hn (σOf hrig γ g) ⊆ S :=
    ⟨isSupport_supOf hrig hn (σOf hrig γ g), ncard_supOf_le hrig hn (σOf hrig γ g),
      fun S hS hSc => supOf_subset hrig hn (σOf hrig γ g) hS hSc⟩
  exact least_small_support_unique hspecProp hprop

end Lax461425Proofs.PatternsInductionOrbit
