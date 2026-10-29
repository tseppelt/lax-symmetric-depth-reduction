import Lax461425Proofs.PatternsLabelledOps

/-!
---
title: Monotonicity of the labelled-graph classes in the depth bound
type: lemma
---
A small general fact used repeatedly in `lem:restricted`: the classes `𝒯^{Δ,k}(ℓ,r)`,
`𝒯^{Δ,k}_P(ℓ,r)`, and their spans `𝔗^{Δ,k}_{n,P}(ℓ,r)` are monotone increasing in `Δ`. The point
is that a root-exact decomposition witnessing depth `≤ Δ` also witnesses depth `≤ Δ'` for any
`Δ' ≥ Δ`: once the iterated parent map reaches the root, it stays there (`parent root = root`),
so iterating further never leaves it.
-/

namespace Lax461425Proofs.PatternsRestrictedMono

open Lax461425.HomomorphismPolynomials Lax461425Proofs.PatternsLabelledBasic
open Lax461425Proofs.PatternsLabelledOps

variable {ℓ r : ℕ}

/-- If the iterated parent map fixes a point after `Δ` steps, it stays fixed after any larger
number of steps: iterating a map that fixes a point `x` keeps fixing `x`. -/
theorem iterate_eq_of_iterate_eq_of_le {α : Type*} {f : α → α} {x a : α} {Δ Δ' : ℕ} (hle : Δ ≤ Δ')
    (hfix : f x = x) (h : f^[Δ] a = x) : f^[Δ'] a = x := by
  obtain ⟨e, rfl⟩ := Nat.le.dest hle
  clear hle
  induction e with
  | zero => simpa using h
  | succ e ih =>
      have hstep : Δ + (e + 1) = (Δ + e) + 1 := by omega
      rw [hstep, Function.iterate_succ_apply', ih, hfix]

/-- A root-exact decomposition of depth `≤ Δ` is also one of depth `≤ Δ'` for any `Δ' ≥ Δ`:
reuse the same tree, only reproving the depth bound. -/
noncomputable def monoDecomposition {G : LabelledPattern ℓ r} {Δ Δ' k : ℕ}
    (hle : Δ ≤ Δ') (D : RootExactDecomposition G Δ k) : RootExactDecomposition G Δ' k where
  Node := D.Node
  root := D.root
  parent := D.parent
  parent_root := D.parent_root
  depth_le := fun t => iterate_eq_of_iterate_eq_of_le hle D.parent_root (D.depth_le t)
  bag := D.bag
  bag_root := D.bag_root
  card_bag_le := D.card_bag_le
  exists_mem_bag := D.exists_mem_bag
  exists_edge_mem_bag := D.exists_edge_mem_bag
  connected := D.connected

/-- `InClass` is monotone increasing in the depth bound `Δ`. -/
theorem mono_inClass {G : LabelledPattern ℓ r} {Δ Δ' k : ℕ} (hle : Δ ≤ Δ') (h : InClass Δ k G) :
    InClass Δ' k G := by
  obtain ⟨D⟩ := h
  exact ⟨monoDecomposition hle D⟩

/-- `InClassP` is monotone increasing in the depth bound `Δ`, for a fixed `P`. -/
theorem mono_inClassP {G : LabelledPattern ℓ r} {Δ Δ' k : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)}
    (hle : Δ ≤ Δ') (h : InClassP Δ k P G) : InClassP Δ' k P G :=
  ⟨mono_inClass hle h.1, h.2⟩

/-- **The span `𝔗^{Δ,k}_{n,P}(ℓ,r)` is monotone increasing in the depth bound `Δ`.** -/
theorem span𝔗P_mono {K : Type*} [Field K] {Δ Δ' k n : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)}
    (hle : Δ ≤ Δ') : span𝔗P K Δ k n P ≤ span𝔗P K Δ' k n P := by
  apply Submodule.span_mono
  rintro f ⟨G, hG, rfl⟩
  exact ⟨G, mono_inClassP hle hG, rfl⟩

end Lax461425Proofs.PatternsRestrictedMono
