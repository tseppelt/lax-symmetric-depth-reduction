import Lax461425Proofs.PatternsInductionReindex

/-!
The "no new support" (`N = ∅`) sub-case of `lem:induction`'s internal-gate step: lifting a
witness `φ ∈ 𝔗^{Δ,k}_n(ℓ_h,r_h)` for a child `h` (at `h`'s own canonical arity) to a witness at
`g`'s canonical arity, whenever `sup(h) ⊆ sup(g)` — i.e. whenever descending from `g` to `h`
introduces no genuinely new support positions. Combined with `PatternsRestrictedMono.span𝔗P_mono`
and `PatternsSupportDepth.sc_mono` (`sc C h ≤ sc C g` for any child `h` of `g`), this gives
exactly the single-child "lift" step used when `g`'s wire to `h` is not support-changing.

The construction: `leftEnum hrig hn h`'s range (= `leftPart (supOf h)`) is contained in
`leftEnum hrig hn g`'s range (= `leftPart (supOf g)`), so there is an embedding `ι` of `h`'s
canonical left-label index set into `g`'s with `leftEnum g ∘ ι = leftEnum h` (and similarly on
the right, via `κ`); applying `PatternsInductionReindex.span𝔗P_pad_mem` to `φ` along `ι, κ`
reindexes it to `g`'s arity while leaving its value at `(leftEnum g, rightEnum g)` equal to its
old value at `(leftEnum h, rightEnum h)`.
-/

namespace Lax461425Proofs.PatternsInductionChild

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open Lax461425Proofs.PatternsSupportDepth Lax461425Proofs.PatternsInductionSetup
open Lax461425Proofs.PatternsLabelledOps Lax461425Proofs.PatternsRestrictedMono
open Lax461425Proofs.PatternsInductionReindex
open scoped Classical

/-- If `Set.range f ⊆ Set.range g` for injective `f : Fin m → Fin n`, `g : Fin m' → Fin n`, then
`f` factors through `g` along an embedding `ι : Fin m ↪ Fin m'`: the reindexing tool needed to
transport a witness built against one injective enumeration of a finite subset to any other
injective enumeration of a *superset*. -/
theorem embedding_of_range_subset {m m' n : ℕ} {f : Fin m → Fin n} {g : Fin m' → Fin n}
    (hf : Function.Injective f) (hg : Function.Injective g) (hsub : Set.range f ⊆ Set.range g) :
    ∃ ι : Fin m ↪ Fin m', g ∘ ι = f := by
  classical
  set eg : Fin m' ≃ Set.range g := Equiv.ofInjective g hg with heg
  refine ⟨⟨fun i => eg.symm ⟨f i, hsub (Set.mem_range_self i)⟩, ?_⟩, ?_⟩
  · intro i1 i2 heq
    have h2 := congrArg eg heq
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2
    exact hf (Subtype.ext_iff.mp h2)
  · funext i
    show g (eg.symm ⟨f i, hsub (Set.mem_range_self i)⟩) = f i
    exact congrArg Subtype.val (Equiv.apply_symm_apply eg ⟨f i, hsub (Set.mem_range_self i)⟩)

variable {K : Type*} [Field K] {n : ℕ} {C : Circuit (Fin n × Fin n) K}

/-- **The `N = ∅` child-lift, at fixed depth.** If `sup(h) ⊆ sup(g)`, any witness for `h` at
`h`'s own canonical arity reindexes to a witness for `g` at `g`'s canonical arity, at the *same*
depth bound, with the same value at the canonical enumerations. -/
theorem exists_pad_of_subset (hrig : IsRigid C) (hn : 2 * supportSize C < n) {g h : C.Gate}
    (hsub : supOf hrig hn h ⊆ supOf hrig hn g) {Δ k : ℕ}
    (φ : (Fin (leftCard hrig hn h) → Fin n) → (Fin (rightCard hrig hn h) → Fin n) →
      MvPolynomial (Fin n × Fin n) K)
    (hφ : φ ∈ span𝔗P K Δ k n
      (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h)))) :
    ∃ ψ : (Fin (leftCard hrig hn g) → Fin n) → (Fin (rightCard hrig hn g) → Fin n) →
      MvPolynomial (Fin n × Fin n) K,
      ψ ∈ span𝔗P K Δ k n
        (Finset.univ : Finset (Fin (leftCard hrig hn g) ⊕ Fin (rightCard hrig hn g))) ∧
      ψ (leftEnum hrig hn g) (rightEnum hrig hn g) = φ (leftEnum hrig hn h) (rightEnum hrig hn h) := by
  have hsubL : leftPart (supOf hrig hn h) ⊆ leftPart (supOf hrig hn g) := fun i hi => hsub hi
  have hsubR : rightPart (supOf hrig hn h) ⊆ rightPart (supOf hrig hn g) := fun j hj => hsub hj
  have hrangeL : Set.range (leftEnum hrig hn h) ⊆ Set.range (leftEnum hrig hn g) := by
    rw [range_leftEnum, range_leftEnum]; exact hsubL
  have hrangeR : Set.range (rightEnum hrig hn h) ⊆ Set.range (rightEnum hrig hn g) := by
    rw [range_rightEnum, range_rightEnum]; exact hsubR
  obtain ⟨ι, hι⟩ := embedding_of_range_subset (leftEnum_injective hrig hn h)
    (leftEnum_injective hrig hn g) hrangeL
  obtain ⟨κ, hκ⟩ := embedding_of_range_subset (rightEnum_injective hrig hn h)
    (rightEnum_injective hrig hn g) hrangeR
  refine ⟨fun v w => φ (v ∘ ι) (w ∘ κ), span𝔗P_pad_mem ι κ φ hφ, ?_⟩
  show φ ((leftEnum hrig hn g) ∘ ι) ((rightEnum hrig hn g) ∘ κ) =
    φ (leftEnum hrig hn h) (rightEnum hrig hn h)
  rw [hι, hκ]

/-- **The `N = ∅` child-lift, with a depth increase folded in.** The version actually used in
the induction: `Δ ≤ Δ'` (from `sc_mono`) lets the result land in the depth-`Δ'` span directly. -/
theorem exists_pad_of_subset_mono (hrig : IsRigid C) (hn : 2 * supportSize C < n) {g h : C.Gate}
    (hsub : supOf hrig hn h ⊆ supOf hrig hn g) {Δ Δ' k : ℕ} (hΔ : Δ ≤ Δ')
    (φ : (Fin (leftCard hrig hn h) → Fin n) → (Fin (rightCard hrig hn h) → Fin n) →
      MvPolynomial (Fin n × Fin n) K)
    (hφ : φ ∈ span𝔗P K Δ k n
      (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h)))) :
    ∃ ψ : (Fin (leftCard hrig hn g) → Fin n) → (Fin (rightCard hrig hn g) → Fin n) →
      MvPolynomial (Fin n × Fin n) K,
      ψ ∈ span𝔗P K Δ' k n
        (Finset.univ : Finset (Fin (leftCard hrig hn g) ⊕ Fin (rightCard hrig hn g))) ∧
      ψ (leftEnum hrig hn g) (rightEnum hrig hn g) = φ (leftEnum hrig hn h) (rightEnum hrig hn h) := by
  obtain ⟨ψ, hψmem, hψeq⟩ := exists_pad_of_subset hrig hn hsub φ hφ
  exact ⟨ψ, span𝔗P_mono hΔ hψmem, hψeq⟩

/-- **Applying the lift to an actual child in the circuit.** If `h` is a child of `g`
(`0 < C.wire g h`) and `sup(h) ⊆ sup(g)`, then `sc C h ≤ sc C g` (`PatternsSupportDepth.sc_mono`)
gives the needed depth bound for free: any witness for `h` at depth `sc C h` lifts to a witness
for `g` at depth `sc C g`. -/
theorem exists_pad_of_child (hrig : IsRigid C) (hn : 2 * supportSize C < n) {g h : C.Gate}
    (hwire : 0 < C.wire g h) (hsub : supOf hrig hn h ⊆ supOf hrig hn g) {k : ℕ}
    (φ : (Fin (leftCard hrig hn h) → Fin n) → (Fin (rightCard hrig hn h) → Fin n) →
      MvPolynomial (Fin n × Fin n) K)
    (hφ : φ ∈ span𝔗P K (sc C h) k n
      (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h)))) :
    ∃ ψ : (Fin (leftCard hrig hn g) → Fin n) → (Fin (rightCard hrig hn g) → Fin n) →
      MvPolynomial (Fin n × Fin n) K,
      ψ ∈ span𝔗P K (sc C g) k n
        (Finset.univ : Finset (Fin (leftCard hrig hn g) ⊕ Fin (rightCard hrig hn g))) ∧
      ψ (leftEnum hrig hn g) (rightEnum hrig hn g) = φ (leftEnum hrig hn h) (rightEnum hrig hn h) :=
  exists_pad_of_subset_mono hrig hn hsub (sc_mono hwire) φ hφ

end Lax461425Proofs.PatternsInductionChild
