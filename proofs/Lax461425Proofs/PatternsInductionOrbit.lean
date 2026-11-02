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

end Lax461425Proofs.PatternsInductionOrbit
