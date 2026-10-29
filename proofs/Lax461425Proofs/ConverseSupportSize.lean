import Lax461425Proofs.ConverseSymmetry
import Lax461425Proofs.ReducedRigid
import Lax461425Proofs.RigidReduced
import Lax461425Proofs.RigidSymmetric
import Lax461425Proofs.PatternsSupportAction

/-!
**Support size for `C = reduced C₀`** (part of `thm:converse`'s remaining item 1), where
`C₀ := circuit N n K hn0 hE` is the pre-rigidification circuit of `ConverseGates.lean`.

The key structural fact, proved once and for all gate kinds simultaneously
(`σOf_apply_toC'`): for `hrig : IsRigid (reduced C₀)`, the canonical automorphism `σOf hrig γ'`
acts on the reduced circuit's gates by *literally pushing the original `actGate N n γ'` action
on `C₀` through the quotient map* `toC'`:
$$
  \mathrm{σOf}\ \mathrm{hrig}\ γ'\ (\mathrm{toC'}\ C₀\ g) = \mathrm{toC'}\ C₀\ (\mathrm{actGate}\ N\ n\ γ'\ g)
$$
for *every* `g : CGate N n`, unconditionally (no fixing hypothesis needed). This sidesteps the
"extra automorphisms of `C₀`" subtlety entirely: we never need to know whether `C₀` itself is
rigid, only that `reduced C₀` is (via `ReducedRigid.isRigid`), and the formula is stated
uniformly in `g`, not tied to any specific choice of representative.

From this formula, `IsSupport (reduced C₀) (toC' C₀ g) S` reduces to a purely combinatorial
statement about `actGate`/`actAdm`/`actCoord` on `CGate N n`, with no further circuit-theoretic
content: we show that whenever `γ'` fixes the point set `gatePoints N n g` (the image, under the
gate's own admissible map, of its defining bag/intersection, or the two points named by an input
gate) pointwise, `actGate N n γ' g = g` *literally* (not just up to `Equiv`), which immediately
gives `IsSupport`. Since every bag has size `≤ k` (`NormDecomp.card_bag_le`), this gives
`supportSize (reduced C₀) ≤ k` once `k ≥ 2` (needed only for input gates' two-point supports).

This file does **not** attempt `supportSize`'s minimality direction, nor `supportDepth`; see the
module docstring of the handoff report for why `supportDepth` needs genuinely more (a
polynomial-level, not DAG-level, minimality argument) than what is established here.
-/

namespace Lax461425Proofs

open Classical Lax461425.Circuits Lax461425.HomomorphismPolynomials Lax461425.Forestwidth
open Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.RigidConstruction Lax461425Proofs.RigidRep Lax461425Proofs.RigidEquiv
open Lax461425Proofs.RigidSymmetric Lax461425Proofs.PatternsSupportAction

variable {F : Pattern} {Δ k : ℕ}

section SideOfAdm

variable {n : ℕ}

/-- The point of `[n] ⊎ [n]` corresponding to the value `γ x` at `x : ↥S`, placed on the row
side if `x` is a left (`F.A`) point and on the column side if it is a right (`F.B`) point. -/
noncomputable def sideOfAdm {S : Finset (F.A ⊕ F.B)} (γ : Adm F n S) (x : ↥S) :
    Fin n ⊕ Fin n :=
  Sum.map (fun _ : F.A => γ x) (fun _ : F.B => γ x) x.1

/-- Two admissible maps on `S` agree at `x` iff their `sideOfAdm` values at `x` agree: the
`Sum.inl`/`Sum.inr` wrapping chosen by `sideOfAdm` is determined by `x.1` alone, so it cancels.
-/
theorem sideOfAdm_eq_iff {S : Finset (F.A ⊕ F.B)} {γ γ' : Adm F n S} (x : ↥S) :
    sideOfAdm γ x = sideOfAdm γ' x ↔ γ x = γ' x := by
  unfold sideOfAdm
  rcases hx : x.1 with a | b <;> simp

/-- `actPoint` commutes with `sideOfAdm`, through `actAdm` on the admissible map: moving the
*point* `sideOfAdm γ x` by `γ'` is the same as reading off the point of the *relabelled* map
`actAdm n γ' γ`. -/
theorem actPoint_sideOfAdm (γ' : Γ n) {S : Finset (F.A ⊕ F.B)} (γ : Adm F n S) (x : ↥S) :
    actPoint γ' (sideOfAdm γ x) = sideOfAdm (actAdm n γ' γ) x := by
  unfold sideOfAdm actAdm actPoint actCoord
  rcases hx : x.1 with a | b <;> simp

/-- If `γ'` fixes, pointwise, every point named by `γ` (via `sideOfAdm`, over all of `S`), then
`γ'` does not change `γ` at all: `actAdm n γ' γ = γ`. -/
theorem actAdm_eq_self_of_fixes {S : Finset (F.A ⊕ F.B)} (γ : Adm F n S) (γ' : Γ n)
    (hfix : ∀ p ∈ (S.attach.image (sideOfAdm γ) : Finset (Fin n ⊕ Fin n)),
      actPoint γ' p = p) :
    actAdm n γ' γ = γ := by
  funext x
  have hmem : sideOfAdm γ x ∈ (S.attach.image (sideOfAdm γ) : Finset (Fin n ⊕ Fin n)) :=
    Finset.mem_image_of_mem _ (Finset.mem_attach _ x)
  have h := hfix _ hmem
  rw [actPoint_sideOfAdm] at h
  exact (sideOfAdm_eq_iff x).mp h

end SideOfAdm

section PointSet

variable (N : NormDecomp F Δ k) (n : ℕ)

/-- The point set associated to a gate: the image, under `sideOfAdm`, of the admissible map
carried by an `R`- or `S`-gate (over its bag, resp. bag intersection), or the two points named
by an input gate. -/
noncomputable def gatePoints : CGate N n → Finset (Fin n ⊕ Fin n)
  | .R t γ => (N.bag t).attach.image (sideOfAdm γ)
  | .S c δ => (N.bag (N.parent c.1) ∩ N.bag c.1).attach.image (sideOfAdm δ)
  | .inp i j => {Sum.inl i, Sum.inr j}

/-- If `γ'` fixes `gatePoints N n g` pointwise, it does not move `g` at all under `actGate`. -/
theorem actGate_eq_self_of_fixes (γ' : Γ n) (g : CGate N n)
    (hfix : ∀ p ∈ (gatePoints N n g : Finset (Fin n ⊕ Fin n)), actPoint γ' p = p) :
    actGate N n γ' g = g := by
  cases g with
  | R t γ =>
      show CGate.R t (actAdm n γ' γ) = CGate.R t γ
      rw [actAdm_eq_self_of_fixes γ γ' hfix]
  | S c δ =>
      show CGate.S c (actAdm n γ' δ) = CGate.S c δ
      rw [actAdm_eq_self_of_fixes δ γ' hfix]
  | inp i j =>
      show CGate.inp (γ'.1 i) (γ'.2 j) = CGate.inp i j
      have h1 : actPoint γ' (Sum.inl i) = Sum.inl i := hfix _ (by simp [gatePoints])
      have h2 : actPoint γ' (Sum.inr j) = Sum.inr j := hfix _ (by simp [gatePoints])
      simp only [actPoint, Sum.map_inl, Sum.map_inr] at h1 h2
      rw [Sum.inl_injective h1, Sum.inr_injective h2]

/-- `gatePoints` has size at most `k` (given `k ≥ 2`, used only for input gates): `R`/`S`-gates'
point sets have size at most the bag (resp. bag intersection) they come from, which is `≤ k` by
`NormDecomp.card_bag_le`; input gates' point sets have exactly two points. -/
theorem card_gatePoints_le (hk2 : 2 ≤ k) (g : CGate N n) : (gatePoints N n g).card ≤ k := by
  cases g with
  | R t γ =>
      calc (gatePoints N n (.R t γ)).card ≤ (N.bag t).attach.card := Finset.card_image_le
        _ = (N.bag t).card := Finset.card_attach
        _ ≤ k := N.card_bag_le t
  | S c δ =>
      calc (gatePoints N n (.S c δ)).card
          ≤ (N.bag (N.parent c.1) ∩ N.bag c.1).attach.card := Finset.card_image_le
        _ = (N.bag (N.parent c.1) ∩ N.bag c.1).card := Finset.card_attach
        _ ≤ (N.bag c.1).card := Finset.card_le_card Finset.inter_subset_right
        _ ≤ k := N.card_bag_le c.1
  | inp i j =>
      have h2 : (gatePoints N n (.inp i j)).card ≤ 2 := by
        show ({Sum.inl i, Sum.inr j} : Finset (Fin n ⊕ Fin n)).card ≤ 2
        exact le_trans (Finset.card_insert_le _ _) (by simp)
      omega

end PointSet

section SupportToC'

variable (N : NormDecomp F Δ k) (n : ℕ) {K : Type*} (hn0 : 0 < n) (hE : ∃ a b, F.mult a b ≠ 0)

/-- **The key structural formula.** The canonical rigid automorphism `σOf hrig γ'` acts on the
reduced circuit's gates by pushing `actGate N n γ'`, the original action on `C₀`, through the
quotient map `toC'`, *for every `g`, unconditionally*. -/
theorem σOf_apply_toC' (hrig : IsRigid (reduced (circuit N n K hn0 hE))) (γ' : Γ n)
    (g : CGate N n) :
    σOf hrig γ' (toC' (circuit N n K hn0 hE) g) =
      toC' (circuit N n K hn0 hE) (actGate N n γ' g) := by
  set C₀ := circuit N n K hn0 hE with hC₀
  have hextγ' : Extends C₀ (actGateEquiv N n γ') (actVar γ') :=
    ⟨actGate_label N n γ', actGate_wire N n γ'⟩
  have hextγ'2 : Extends C₀ (actGateEquiv N n γ') (⇑(Equiv.prodCongr γ'.1 γ'.2)) := hextγ'
  rw [← σOf_unique hrig (extends_toC'Equiv hextγ')]
  show toC' C₀ (actGate N n γ' (rep C₀ g)) = toC' C₀ (actGate N n γ' g)
  have hEquiv := (equiv_extends C₀ hextγ'2 (rep C₀ g) g).mpr (equiv_symm C₀ (rep_equiv C₀ g))
  exact toC'_eq_of_equiv C₀ hEquiv

/-- **Every gate of `reduced C₀` has a support of size `≤ k`.** The point set `gatePoints N n g`
supports `toC' C₀ g`, for every `g`. -/
theorem isSupport_toC' (hrig : IsRigid (reduced (circuit N n K hn0 hE))) (g : CGate N n) :
    IsSupport (reduced (circuit N n K hn0 hE)) (toC' (circuit N n K hn0 hE) g)
      (gatePoints N n g : Set (Fin n ⊕ Fin n)) := by
  set C₀ := circuit N n K hn0 hE with hC₀
  intro γ' σ hfix hext
  rw [σOf_unique hrig hext, σOf_apply_toC' N n hn0 hE hrig γ' g]
  have hfix' : ∀ p ∈ (gatePoints N n g : Finset (Fin n ⊕ Fin n)), actPoint γ' p = p := by
    intro p hp
    exact hfix p hp
  rw [actGate_eq_self_of_fixes N n γ' g hfix']

/-- **Support size bound.** `supportSize (reduced C₀) ≤ k`, given `k ≥ 2`. -/
theorem supportSize_reduced_le (hk2 : 2 ≤ k)
    (hrig : IsRigid (reduced (circuit N n K hn0 hE))) :
    supportSize (reduced (circuit N n K hn0 hE)) ≤ k := by
  apply Nat.sInf_le
  intro p
  refine ⟨(gatePoints N n p.1 : Set (Fin n ⊕ Fin n)), ?_, ?_⟩
  · have h := isSupport_toC' N n hn0 hE hrig p.1
    rwa [toC'_self] at h
  · rw [Set.ncard_coe_finset]
    exact card_gatePoints_le N n hk2 p.1

/-- **Convenience corollary.** Combining the pieces needed to invoke
`supportSize_reduced_le`: given `IsMatrixSymmetric C₀` and that `C₀` has at least `2` as the
forestwidth parameter, the reduced circuit (which is automatically reduced and rigid) has
support size `≤ k`. -/
theorem supportSize_reduced_le' (hk2 : 2 ≤ k) :
    supportSize (reduced (circuit N n K hn0 hE)) ≤ k := by
  have hsym₀ : IsMatrixSymmetric (circuit N n K hn0 hE) := isMatrixSymmetric_circuit N n hn0 hE
  have hred : (reduced (circuit N n K hn0 hE)).IsReduced :=
    Lax461425Proofs.RigidReduced.isReduced_reduced (circuit N n K hn0 hE)
  have hsym : IsMatrixSymmetric (reduced (circuit N n K hn0 hE)) :=
    isMatrixSymmetric_reduced (circuit N n K hn0 hE) hsym₀
  have hrig : IsRigid (reduced (circuit N n K hn0 hE)) :=
    Lax461425Proofs.ReducedRigid.isRigid hsym hred
  exact supportSize_reduced_le N n hn0 hE hk2 hrig

end SupportToC'

end Lax461425Proofs
