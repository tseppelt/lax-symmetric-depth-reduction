import Lax461425Proofs.PatternsInductionPsiH
import Lax461425Proofs.PatternsRestrictedSum
import Lax461425Proofs.PatternsRestrictedProd
import Mathlib.Order.Partition.Finpartition

/-!
**The orbit-level `ψ^O_Σ`/`ψ^O_Π` for `lem:induction`'s internal-gate case** (support-changing
children). For a child `h` of `g`, `Ofinset hrig hn g h` is the (finite) set of gates reachable
from `h` by `σOf hrig δ` for `δ` fixing `sup g` pointwise, realised concretely as the image of
`hYtot` over `Y_u`. We partition `Y_u` into the fibres of `hYtot`, show all fibres have the same
size (`G` acts transitively on `Y_u`, and `hYtot` is `G`-equivariant), and feed this into
`exists_ψSum`/`exists_ψProd` to get `ψ^O_Σ`/`ψ^O_Π` at depth `sc h + 1`, together with a choice
function `q` on `Ofinset hrig hn g h` with `C.ComputesAt h' (q h')` for every `h'` in it and
`ψ^O_Σ(u) = ∑_{h' ∈ O} q(h')`, `ψ^O_Π(u) = ∏_{h' ∈ O} q(h')`.
-/

namespace Lax461425Proofs.PatternsInductionOrbitSum

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open Lax461425Proofs.PatternsSupportDepth Lax461425Proofs.PatternsInductionSetup
open Lax461425Proofs.PatternsInductionNidx Lax461425Proofs.PatternsInductionTransitive
open Lax461425Proofs.PatternsRestrictedY Lax461425Proofs.PatternsInductionOrbitMap
open Lax461425Proofs.PatternsInductionReindex Lax461425Proofs.PatternsLabelledOps
open Lax461425Proofs.PatternsInductionHomRename Lax461425Proofs.PatternsInductionEquivariant
open Lax461425Proofs.RigidComputes Lax461425Proofs.PatternsInductionPsiH
open Lax461425Proofs.PatternsRestrictedSum Lax461425Proofs.PatternsRestrictedProd
open Lax461425Proofs.PatternsRestrictedMono
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {n : ℕ} {C : Circuit (Fin n × Fin n) K}
variable (hrig : IsRigid C) (hn : 2 * supportSize C < n) {g h : C.Gate}

/-! ### `Yu`: an abbreviation for `Y_u` -/

/-- `Y_u` for this `g, h`: pairs `(y, z)` avoiding `sup g` on each side, sized to `N`. -/
noncomputable def Yu : Finset
    ((Fin (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h)) → Fin n) ×
      (Fin (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) → Fin n)) :=
  Y _ _ n (leftEnum hrig hn g) (rightEnum hrig hn g)

/-! ### The `Γ n`-action on pairs, and its interaction with `Yu`/`hYtot` -/

/-- The diagonal action of `γ : Γ n` on a pair `(y, z)`. -/
def actOn (γ : Γ n)
    (x : (Fin (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h)) → Fin n) ×
      (Fin (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) → Fin n)) :
    (Fin (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h)) → Fin n) ×
      (Fin (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) → Fin n) :=
  (γ.1 ∘ x.1, γ.2 ∘ x.2)

omit [Field K] [CharZero K] in
theorem append_comp_perm_fix {m : ℕ} {v : Fin m → Fin n} {γ1 : Equiv.Perm (Fin n)}
    (hfix : ∀ x ∈ Set.range v, γ1 x = x) {ℓ' : ℕ} (y : Fin ℓ' → Fin n) :
    Fin.append v (γ1 ∘ y) = γ1 ∘ Fin.append v y := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · show Fin.append v (γ1 ∘ y) (Fin.castAdd ℓ' j) = γ1 (Fin.append v y (Fin.castAdd ℓ' j))
    rw [Fin.append_left, Fin.append_left]
    exact (hfix (v j) (Set.mem_range_self j)).symm
  · show Fin.append v (γ1 ∘ y) (Fin.natAdd m k) = γ1 (Fin.append v y (Fin.natAdd m k))
    rw [Fin.append_right, Fin.append_right]
    rfl

omit [Field K] [CharZero K] in
theorem actOn_mem_Yu {γ : Γ n} (hγ : γ ∈ fixingSubgroup (Γ n) (supOf hrig hn g))
    {x : (Fin (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h)) → Fin n) ×
      (Fin (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) → Fin n)}
    (hx : x ∈ Yu hrig hn) : actOn hrig hn γ x ∈ Yu hrig hn := by
  rw [Yu, mem_Y] at hx ⊢
  obtain ⟨hinj1, hinj2⟩ := hx
  have hfix1 : ∀ p ∈ Set.range (leftEnum hrig hn g), γ.1 p = p := by
    rw [range_leftEnum]; exact fixingSubgroupΓ_left hγ
  have hfix2 : ∀ p ∈ Set.range (rightEnum hrig hn g), γ.2 p = p := by
    rw [range_rightEnum]; exact fixingSubgroupΓ_right hγ
  refine ⟨?_, ?_⟩
  · show Function.Injective (Fin.append (leftEnum hrig hn g) (γ.1 ∘ x.1))
    rw [append_comp_perm_fix hfix1]
    exact γ.1.injective.comp hinj1
  · show Function.Injective (Fin.append (rightEnum hrig hn g) (γ.2 ∘ x.2))
    rw [append_comp_perm_fix hfix2]
    exact γ.2.injective.comp hinj2

omit [Field K] [CharZero K] in
/-- **`hYtot` is `G`-equivariant.** -/
theorem hYtot_smul {γ : Γ n} (hγ : γ ∈ fixingSubgroup (Γ n) (supOf hrig hn g))
    {x : (Fin (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h)) → Fin n) ×
      (Fin (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) → Fin n)}
    (hx : x ∈ Yu hrig hn) :
    hYtot hrig hn (actOn hrig hn γ x).1 (actOn hrig hn γ x).2 = σOf hrig γ (hYtot hrig hn x.1 x.2) := by
  show hYtot hrig hn (γ.1 ∘ x.1) (γ.2 ∘ x.2) = σOf hrig γ (hYtot hrig hn x.1 x.2)
  obtain ⟨δ, hδmem, hδy, hδz⟩ := exists_γ_of_mem_Y hrig hn hx
  have hx_eq : hYtot hrig hn x.1 x.2 = σOf hrig δ h := hYtot_eq_of_valid hrig hn hx hδmem hδy hδz
  have hγδmem : γ * δ ∈ fixingSubgroup (Γ n) (supOf hrig hn g) := Subgroup.mul_mem _ hγ hδmem
  have hγδy : (γ * δ).1 ∘ yReal (leftEnum hrig hn g) (leftEnum hrig hn h) = γ.1 ∘ x.1 := by
    show (γ.1 * δ.1) ∘ yReal (leftEnum hrig hn g) (leftEnum hrig hn h) = γ.1 ∘ x.1
    rw [Equiv.Perm.coe_mul, Function.comp_assoc, hδy]
  have hγδz : (γ * δ).2 ∘ yReal (rightEnum hrig hn g) (rightEnum hrig hn h) = γ.2 ∘ x.2 := by
    show (γ.2 * δ.2) ∘ yReal (rightEnum hrig hn g) (rightEnum hrig hn h) = γ.2 ∘ x.2
    rw [Equiv.Perm.coe_mul, Function.comp_assoc, hδz]
  have hmemYu : actOn hrig hn γ x ∈ Yu hrig hn := actOn_mem_Yu hrig hn hγ hx
  have hmemYu' : (γ.1 ∘ x.1, γ.2 ∘ x.2) ∈ Yu hrig hn := hmemYu
  rw [hYtot_eq_of_valid hrig hn hmemYu' hγδmem hγδy hγδz, hx_eq, σOf_mul]
  rfl

omit [Field K] [CharZero K] in
theorem actOn_actOn (γ1 γ2 : Γ n)
    (x : (Fin (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h)) → Fin n) ×
      (Fin (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) → Fin n)) :
    actOn hrig hn γ1 (actOn hrig hn γ2 x) = actOn hrig hn (γ1 * γ2) x := by
  show (γ1.1 ∘ (γ2.1 ∘ x.1), γ1.2 ∘ (γ2.2 ∘ x.2)) = ((γ1 * γ2).1 ∘ x.1, (γ1 * γ2).2 ∘ x.2)
  rw [show (γ1 * γ2).1 = γ1.1 * γ2.1 from rfl, show (γ1 * γ2).2 = γ1.2 * γ2.2 from rfl,
    Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, Function.comp_assoc, Function.comp_assoc]

omit [Field K] [CharZero K] in
theorem actOn_one
    (x : (Fin (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h)) → Fin n) ×
      (Fin (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) → Fin n)) :
    actOn hrig hn (1 : Γ n) x = x := by
  show ((1 : Equiv.Perm (Fin n)) ∘ x.1, (1 : Equiv.Perm (Fin n)) ∘ x.2) = x
  simp

omit [Field K] [CharZero K] in
/-- **Equal fibre size.** All fibres of `hYtot` over `Yu` have the same cardinality. -/
theorem card_filter_hYtot_eq
    {a b : (Fin (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h)) → Fin n) ×
      (Fin (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) → Fin n)}
    (ha : a ∈ Yu hrig hn) (hb : b ∈ Yu hrig hn) :
    ((Yu hrig hn).filter (fun x : (Fin (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h)) → Fin n) ×
        (Fin (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) → Fin n) =>
        hYtot hrig hn a.1 a.2 = hYtot hrig hn x.1 x.2)).card =
      ((Yu hrig hn).filter (fun x : (Fin (ℓN (leftEnum hrig hn g) (leftEnum hrig hn h)) → Fin n) ×
        (Fin (ℓN (rightEnum hrig hn g) (rightEnum hrig hn h)) → Fin n) =>
        hYtot hrig hn b.1 b.2 = hYtot hrig hn x.1 x.2)).card := by
  obtain ⟨hainj1, hainj2⟩ := mem_Y.mp ha
  obtain ⟨hbinj1, hbinj2⟩ := mem_Y.mp hb
  obtain ⟨-, hainj1', hacross1⟩ := Fin.append_injective_iff.mp hainj1
  obtain ⟨-, hainj2', hacross2⟩ := Fin.append_injective_iff.mp hainj2
  obtain ⟨-, hbinj1', hbcross1⟩ := Fin.append_injective_iff.mp hbinj1
  obtain ⟨-, hbinj2', hbcross2⟩ := Fin.append_injective_iff.mp hbinj2
  have hadisj1 : ∀ k, a.1 k ∉ leftPart (supOf hrig hn g) := by
    intro k hk; rw [← range_leftEnum] at hk; obtain ⟨i, hi⟩ := hk; exact hacross1 i k hi
  have hadisj2 : ∀ k, a.2 k ∉ rightPart (supOf hrig hn g) := by
    intro k hk; rw [← range_rightEnum] at hk; obtain ⟨j, hj⟩ := hk; exact hacross2 j k hj
  have hbdisj1 : ∀ k, b.1 k ∉ leftPart (supOf hrig hn g) := by
    intro k hk; rw [← range_leftEnum] at hk; obtain ⟨i, hi⟩ := hk; exact hbcross1 i k hi
  have hbdisj2 : ∀ k, b.2 k ∉ rightPart (supOf hrig hn g) := by
    intro k hk; rw [← range_rightEnum] at hk; obtain ⟨j, hj⟩ := hk; exact hbcross2 j k hj
  obtain ⟨γ, hγmem, hγ1, hγ2⟩ := exists_fixing_Γ_of_notMem hainj1' hbinj1' hainj2' hbinj2'
    hadisj1 hbdisj1 hadisj2 hbdisj2
  have hab : actOn hrig hn γ a = b := by
    show (γ.1 ∘ a.1, γ.2 ∘ a.2) = b
    exact Prod.ext_iff.mpr ⟨funext hγ1, funext hγ2⟩
  have hγinv : γ⁻¹ ∈ fixingSubgroup (Γ n) (supOf hrig hn g) := Subgroup.inv_mem _ hγmem
  have hba : actOn hrig hn γ⁻¹ b = a := by
    rw [← hab, actOn_actOn, inv_mul_cancel, actOn_one]
  refine Finset.card_nbij' (actOn hrig hn γ) (actOn hrig hn γ⁻¹) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    obtain ⟨hxmem, hxeq⟩ := hx
    refine ⟨actOn_mem_Yu hrig hn hγmem hxmem, ?_⟩
    have e1 := hYtot_smul hrig hn hγmem hxmem
    have e2 := hYtot_smul hrig hn hγmem ha
    rw [hab] at e2
    rw [e1, ← hxeq]
    exact e2
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    obtain ⟨hxmem, hxeq⟩ := hx
    refine ⟨actOn_mem_Yu hrig hn hγinv hxmem, ?_⟩
    have e1 := hYtot_smul hrig hn hγinv hxmem
    have e2 := hYtot_smul hrig hn hγinv hb
    rw [hba] at e2
    rw [e1, ← hxeq]
    exact e2
  · intro x _
    rw [actOn_actOn, inv_mul_cancel, actOn_one]
  · intro x _
    rw [actOn_actOn, mul_inv_cancel, actOn_one]

end Lax461425Proofs.PatternsInductionOrbitSum
