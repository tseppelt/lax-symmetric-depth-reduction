import Lax461425Proofs.PatternsInductionOrbitWitness

/-!
**The orbit-level `ψ^O_Σ`/`ψ^O_Π`, assembled.** Applies `exists_ψSum`/`exists_ψProd`
(`PatternsRestrictedSum`/`PatternsRestrictedProd`) to `ψ_h` (`PatternsInductionPsiH`) with the
partition `Qpart` (`PatternsInductionOrbitWitness`), producing witnesses at depth `sc h + 1`
whose value at `g`'s canonical enumeration is the sum/product, over `Ofinset hrig hn g h` (the
image of `hYtot` over `Yu`, i.e. the full orbit of `h` under `fixingSubgroup (Γ n) (sup g)`), of
a choice function `q` with `C.ComputesAt h' (q h')` for every `h'` in the orbit.
-/

namespace Lax461425Proofs.PatternsInductionOrbitFinal

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open Lax461425Proofs.PatternsSupportDepth Lax461425Proofs.PatternsInductionSetup
open Lax461425Proofs.PatternsInductionNidx Lax461425Proofs.PatternsInductionTransitive
open Lax461425Proofs.PatternsRestrictedY Lax461425Proofs.PatternsInductionOrbitMap
open Lax461425Proofs.PatternsInductionReindex Lax461425Proofs.PatternsLabelledOps
open Lax461425Proofs.PatternsInductionHomRename Lax461425Proofs.PatternsInductionEquivariant
open Lax461425Proofs.RigidComputes Lax461425Proofs.PatternsInductionPsiH
open Lax461425Proofs.PatternsRestrictedSum Lax461425Proofs.PatternsRestrictedProd
open Lax461425Proofs.PatternsRestrictedMono Lax461425Proofs.PatternsInductionOrbitSum
open Lax461425Proofs.PatternsInductionOrbitWitness
open scoped Classical

set_option maxHeartbeats 4000000

variable {K : Type*} [Field K] [CharZero K] {n : ℕ} {C : Circuit (Fin n × Fin n) K}
variable (hrig : IsRigid C) (hn : 2 * supportSize C < n) {g h : C.Gate}

/-! ### `Ofinset`: the orbit, as a `Finset C.Gate` -/

/-- **`Ofinset`**: the image of `hYtot` over `Yu`, i.e. the full orbit of `h` under
`fixingSubgroup (Γ n) (sup g)`. -/
noncomputable def Ofinset : Finset C.Gate :=
  (Yu hrig hn (g := g) (h := h)).image (fun x => hYtot hrig hn x.1 x.2)

omit [Field K] [CharZero K] in
theorem mem_Ofinset_iff {h' : C.Gate} :
    h' ∈ Ofinset hrig hn (g := g) (h := h) ↔
      ∃ x : Pairs hrig hn (g := g) (h := h), x ∈ Yu hrig hn ∧ hYtot hrig hn x.1 x.2 = h' := by
  rw [Ofinset, Finset.mem_image]

/-! ### `ψ_h`'s value agrees across any two points with the same `hYtot`-value -/

variable {k : ℕ}
variable (φh : (Fin (leftCard hrig hn h) → Fin n) → (Fin (rightCard hrig hn h) → Fin n) →
  MvPolynomial (Fin n × Fin n) K)
variable (hφh_mem : φh ∈ span𝔗P K (sc C h) k n
  (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h))))
variable (hφh_eval : C.ComputesAt h (φh (leftEnum hrig hn h) (rightEnum hrig hn h)))

omit [CharZero K] in
theorem ψh_eq_of_hYtot_eq
    (hφh_mem : φh ∈ span𝔗P K (sc C h) k n
      (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h))))
    (hφh_eval : C.ComputesAt h (φh (leftEnum hrig hn h) (rightEnum hrig hn h)))
    {x1 x2 : Pairs hrig hn (g := g) (h := h)} (h1 : x1 ∈ Yu hrig hn)
    (h2 : x2 ∈ Yu hrig hn) (heq : hYtot hrig hn x1.1 x1.2 = hYtot hrig hn x2.1 x2.2) :
    ψh hrig hn φh (Fin.append (leftEnum hrig hn g) x1.1) (Fin.append (rightEnum hrig hn g) x1.2) =
      ψh hrig hn φh (Fin.append (leftEnum hrig hn g) x2.1)
        (Fin.append (rightEnum hrig hn g) x2.2) := by
  have c1 := ψh_computesAt hrig hn φh hφh_mem hφh_eval h1
  have c2 := ψh_computesAt hrig hn φh hφh_mem hφh_eval h2
  rw [heq] at c1
  exact computesAt_unique C _ c1 c2

/-! ### `qfun`: the choice function on `Ofinset` -/

/-- **`qfun`**: for `h' ∈ Ofinset`, the (well-defined, by `ψh_eq_of_hYtot_eq`) value `ψ_h` takes
on the fibre of `h'`; `0` outside `Ofinset`. -/
noncomputable def qfun (h' : C.Gate) : MvPolynomial (Fin n × Fin n) K :=
  if hh' : ∃ x : Pairs hrig hn (g := g) (h := h), x ∈ Yu hrig hn ∧ hYtot hrig hn x.1 x.2 = h' then
    ψh hrig hn φh (Fin.append (leftEnum hrig hn g) hh'.choose.1)
      (Fin.append (rightEnum hrig hn g) hh'.choose.2)
  else 0

omit [CharZero K] in
theorem qfun_eq_of_mem
    (hφh_mem : φh ∈ span𝔗P K (sc C h) k n
      (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h))))
    (hφh_eval : C.ComputesAt h (φh (leftEnum hrig hn h) (rightEnum hrig hn h)))
    {x : Pairs hrig hn (g := g) (h := h)} (hx : x ∈ Yu hrig hn) :
    qfun hrig hn (g := g) φh (hYtot hrig hn x.1 x.2) =
      ψh hrig hn φh (Fin.append (leftEnum hrig hn g) x.1) (Fin.append (rightEnum hrig hn g) x.2) := by
  rw [qfun]
  have hex : ∃ x' : Pairs hrig hn (g := g) (h := h), x' ∈ Yu hrig hn ∧
      hYtot hrig hn x'.1 x'.2 = hYtot hrig hn x.1 x.2 := ⟨x, hx, rfl⟩
  rw [dif_pos hex]
  exact ψh_eq_of_hYtot_eq hrig hn φh hφh_mem hφh_eval hex.choose_spec.1 hx
    hex.choose_spec.2

omit [CharZero K] in
theorem computesAt_qfun
    (hφh_mem : φh ∈ span𝔗P K (sc C h) k n
      (Finset.univ : Finset (Fin (leftCard hrig hn h) ⊕ Fin (rightCard hrig hn h))))
    (hφh_eval : C.ComputesAt h (φh (leftEnum hrig hn h) (rightEnum hrig hn h)))
    {h' : C.Gate} (hh' : h' ∈ Ofinset hrig hn (g := g) (h := h)) :
    C.ComputesAt h' (qfun hrig hn (g := g) φh h') := by
  obtain ⟨x, hx, rfl⟩ := mem_Ofinset_iff hrig hn |>.mp hh'
  rw [qfun_eq_of_mem hrig hn φh hφh_mem hφh_eval hx]
  exact ψh_computesAt hrig hn φh hφh_mem hφh_eval hx

end Lax461425Proofs.PatternsInductionOrbitFinal
