import Lax461425Proofs.PatternsInductionOrbitMap
import Lax461425Proofs.PatternsInductionHomRename
import Lax461425Proofs.PatternsInductionEquivariant
import Lax461425Proofs.RigidComputes

/-!
**`ψ_h`'s assembly and evaluation.** Given a gate `g`, a child `h` of `g`, and an induction
hypothesis witness `φ_h` for `h` (a member of `span𝔗P K (sc h) k n univ` whose evaluation at
`h`'s own canonical enumeration computes `h`'s polynomial), we build `ψ_h` by padding `φ_h`
along the embeddings `ιPadEmb` of `PatternsInductionNidx`, and show that `ψ_h`, evaluated at
`(Fin.append u.1 y, Fin.append u.2 z)` for *any* `(y, z) ∈ Y_u`, computes the polynomial of the
sibling gate `hYtot y z` (`PatternsInductionOrbitMap`'s total `h_y` map).

This is the exact payoff the whole chain of lemmas in `PatternsInductionTransitive`,
`PatternsInductionNidx`, `PatternsInductionOrbitMap`, `PatternsInductionHomRename` and
`PatternsInductionEquivariant` was built for, and resolves precisely the point where a previous
attempt (earlier in this session) believed there was a genuine mathematical obstruction: every
point of `Y_u`, not just the real `N`-tuple, corresponds to an honest sibling gate, and `ψ_h`'s
value there is exactly that gate's computed polynomial.
-/

namespace Lax461425Proofs.PatternsInductionPsiH

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open Lax461425Proofs.PatternsSupportDepth Lax461425Proofs.PatternsInductionSetup
open Lax461425Proofs.PatternsInductionNidx Lax461425Proofs.PatternsInductionTransitive
open Lax461425Proofs.PatternsRestrictedY Lax461425Proofs.PatternsInductionOrbitMap
open Lax461425Proofs.PatternsInductionReindex Lax461425Proofs.PatternsLabelledOps
open Lax461425Proofs.PatternsInductionHomRename Lax461425Proofs.PatternsInductionEquivariant
open Lax461425Proofs.RigidComputes
open scoped Classical

variable {K : Type*} [Field K] {n : ℕ} {C : Circuit (Fin n × Fin n) K}
variable (hrig : IsRigid C) (hn : 2 * supportSize C < n) {g h : C.Gate}

/-! ### Extracting one-sided fixing facts from `fixingSubgroup (Γ n) S` -/

omit [Field K] in
theorem fixingSubgroupΓ_left {S : Set (Fin n ⊕ Fin n)} {γ : Γ n}
    (hγ : γ ∈ fixingSubgroup (Γ n) S) : ∀ x ∈ leftPart S, γ.1 x = x := by
  rw [fixingSubgroupΓ_eq_prod] at hγ
  exact (mem_fixingSubgroup_iff (M := Equiv.Perm (Fin n)) (s := leftPart S) (m := γ.1)).mp
    (Subgroup.mem_prod.mp hγ).1

omit [Field K] in
theorem fixingSubgroupΓ_right {S : Set (Fin n ⊕ Fin n)} {γ : Γ n}
    (hγ : γ ∈ fixingSubgroup (Γ n) S) : ∀ x ∈ rightPart S, γ.2 x = x := by
  rw [fixingSubgroupΓ_eq_prod] at hγ
  exact (mem_fixingSubgroup_iff (M := Equiv.Perm (Fin n)) (s := rightPart S) (m := γ.2)).mp
    (Subgroup.mem_prod.mp hγ).2

/-! ### `hYtot`: the total `h_y` map -/

/-- **`hYtot`**: the total `h_y` map, `h` itself outside `Y_u`. -/
noncomputable def hYtot
    (y : Fin (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h)) → Fin n)
    (z : Fin (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) → Fin n) : C.Gate :=
  if hmem : (y, z) ∈ Y _ _ n (leftEnum hrig hn g) (rightEnum hrig hn g) then
    σOf hrig (Classical.choose (exists_γ_of_mem_Y hrig hn hmem)) h
  else h

omit [Field K] in
/-- **`hYtot`'s defining property.** For any `γ` fixing `sup g` pointwise and sending the real
`N`-tuple to `(y, z)`, `hYtot y z = σOf hrig γ h`. -/
theorem hYtot_eq_of_valid
    {y : Fin (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h)) → Fin n}
    {z : Fin (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) → Fin n}
    (hmem : (y, z) ∈ Y _ _ n (leftEnum hrig hn g) (rightEnum hrig hn g)) {γ : Γ n}
    (hγmem : γ ∈ fixingSubgroup (Γ n) (supOf hrig hn g))
    (hγy : γ.1 ∘ yReal (leftEnum hrig hn g) (leftEnum hrig hn h) = y)
    (hγz : γ.2 ∘ yReal (rightEnum hrig hn g) (rightEnum hrig hn h) = z) :
    hYtot hrig hn y z = σOf hrig γ h := by
  unfold hYtot
  rw [dif_pos hmem]
  obtain ⟨hγmem0, hγy0, hγz0⟩ := Classical.choose_spec (exists_γ_of_mem_Y hrig hn hmem)
  exact σOf_eq_of_both_valid hrig hn hγmem0 hγmem hγy0 hγy hγz0 hγz

/-! ### `ψ_h`'s assembly -/

/-- **`ψ_h`**: `φ_h`, padded along `ιPadEmb` on each side to `g`'s arity plus `N`'s. -/
noncomputable def ψh
    (φh : (Fin (leftCard hrig hn h) → Fin n) → (Fin (rightCard hrig hn h) → Fin n) →
      MvPolynomial (Fin n × Fin n) K) :
    (Fin (leftCard hrig hn g + ℓN (leftEnum hrig hn g) (leftEnum hrig hn h)) → Fin n) →
    (Fin (rightCard hrig hn g + ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) → Fin n) →
    MvPolynomial (Fin n × Fin n) K :=
  fun v' w' =>
    φh (v' ∘ ιPadEmb (leftEnum_injective hrig hn g) (leftEnum_injective hrig hn h))
      (w' ∘ ιPadEmb (rightEnum_injective hrig hn g) (rightEnum_injective hrig hn h))

/-- **`ψ_h` lies in the span**, at `sc h`-depth, restricted to the image of `h`'s own label
positions. -/
theorem ψh_mem {k : ℕ}
    (φh : (Fin (leftCard hrig hn h) → Fin n) → (Fin (rightCard hrig hn h) → Fin n) →
      MvPolynomial (Fin n × Fin n) K)
    (hφh_mem : φh ∈ span𝔗P K (sc C h) k n
      (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h)))) :
    ψh hrig hn φh ∈ span𝔗P K (sc C h) k n
      ((Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h))).image
        (Sum.map (ιPadEmb (leftEnum_injective hrig hn g) (leftEnum_injective hrig hn h))
          (ιPadEmb (rightEnum_injective hrig hn g) (rightEnum_injective hrig hn h)))) :=
  span𝔗P_pad_mem_restrict _ _ φh hφh_mem

omit [Field K] in
/-- The label-position `Finset` `ψh_mem` restricts to has `card ≤ k`, given `|sup(h)| ≤ k`. -/
theorem ψh_P_card_le {k : ℕ} (hsize : supportSize C ≤ k) :
    ((Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h))).image
        (Sum.map (ιPadEmb (leftEnum_injective hrig hn g) (leftEnum_injective hrig hn h))
          (ιPadEmb (rightEnum_injective hrig hn g) (rightEnum_injective hrig hn h)))).card ≤ k := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  exact leftCard_add_rightCard_le hrig hn h hsize

/-! ### `ψ_h`'s evaluation -/

/-- **`ψ_h`'s evaluation at a general `γ`-translate.** For any `γ` fixing `sup g` pointwise and
sending the real `N`-tuple to `(y, z)`, `ψ_h` evaluated at `(Fin.append u.1 y, Fin.append u.2 z)`
equals `φ_h` evaluated at `(γ.1 ∘ leftEnum h, γ.2 ∘ rightEnum h)`. -/
theorem ψh_eval_of_γ
    (φh : (Fin (leftCard hrig hn h) → Fin n) → (Fin (rightCard hrig hn h) → Fin n) →
      MvPolynomial (Fin n × Fin n) K)
    {y : Fin (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h)) → Fin n}
    {z : Fin (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) → Fin n} {γ : Γ n}
    (hγmem : γ ∈ fixingSubgroup (Γ n) (supOf hrig hn g))
    (hγy : γ.1 ∘ yReal (leftEnum hrig hn g) (leftEnum hrig hn h) = y)
    (hγz : γ.2 ∘ yReal (rightEnum hrig hn g) (rightEnum hrig hn h) = z) :
    ψh hrig hn φh (Fin.append (leftEnum hrig hn g) y) (Fin.append (rightEnum hrig hn g) z) =
      φh (γ.1 ∘ leftEnum hrig hn h) (γ.2 ∘ rightEnum hrig hn h) := by
  unfold ψh
  have hγ1 : ∀ x ∈ Set.range (leftEnum hrig hn g), γ.1 x = x := by
    rw [range_leftEnum]; exact fixingSubgroupΓ_left hγmem
  have hγ2 : ∀ x ∈ Set.range (rightEnum hrig hn g), γ.2 x = x := by
    rw [range_rightEnum]; exact fixingSubgroupΓ_right hγmem
  have heqL : (Fin.append (leftEnum hrig hn g) y) ∘
      ιPadEmb (leftEnum_injective hrig hn g) (leftEnum_injective hrig hn h) =
        γ.1 ∘ leftEnum hrig hn h := by
    rw [← hγy]; exact append_comp_ιPad (leftEnum_injective hrig hn g) hγ1
  have heqR : (Fin.append (rightEnum hrig hn g) z) ∘
      ιPadEmb (rightEnum_injective hrig hn g) (rightEnum_injective hrig hn h) =
        γ.2 ∘ rightEnum hrig hn h := by
    rw [← hγz]; exact append_comp_ιPad (rightEnum_injective hrig hn g) hγ2
  show φh ((Fin.append (leftEnum hrig hn g) y) ∘
      ιPadEmb (leftEnum_injective hrig hn g) (leftEnum_injective hrig hn h))
    ((Fin.append (rightEnum hrig hn g) z) ∘
      ιPadEmb (rightEnum_injective hrig hn g) (rightEnum_injective hrig hn h)) = _
  rw [heqL, heqR]

/-- **The main evaluation theorem.** For `(y, z) ∈ Y_u`, `ψ_h`'s value there is the computed
polynomial of the sibling gate `hYtot y z`. -/
theorem ψh_computesAt {k : ℕ}
    (φh : (Fin (leftCard hrig hn h) → Fin n) → (Fin (rightCard hrig hn h) → Fin n) →
      MvPolynomial (Fin n × Fin n) K)
    (hφh_mem : φh ∈ span𝔗P K (sc C h) k n
      (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h))))
    (hφh_eval : C.ComputesAt h (φh (leftEnum hrig hn h) (rightEnum hrig hn h)))
    {y : Fin (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h)) → Fin n}
    {z : Fin (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) → Fin n}
    (hmem : (y, z) ∈ Y _ _ n (leftEnum hrig hn g) (rightEnum hrig hn g)) :
    C.ComputesAt (hYtot hrig hn y z)
      (ψh hrig hn φh (Fin.append (leftEnum hrig hn g) y) (Fin.append (rightEnum hrig hn g) z)) := by
  obtain ⟨γ, hγmem, hγy, hγz⟩ := exists_γ_of_mem_Y hrig hn hmem
  rw [ψh_eval_of_γ hrig hn φh hγmem hγy hγz,
    span𝔗P_rename γ hφh_mem (leftEnum hrig hn h) (rightEnum hrig hn h),
    hYtot_eq_of_valid hrig hn hmem hγmem hγy hγz]
  exact computesAt_σOf_rename hrig γ hφh_eval

end Lax461425Proofs.PatternsInductionPsiH
