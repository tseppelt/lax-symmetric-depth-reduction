import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Finite.List
import Lax461425.Supports
import Lax461425.HomomorphismPolynomials

/-!
---
title: Symmetric depth hierarchy
type: theorem
---
For $\Delta, n \geq 1$, let $T_{\Delta,n}$ denote the full $n$-ary tree of depth $\Delta$,
viewed as a pattern.

1. For $\Delta \geq 1$ and $n \geq 20$, every matrix-symmetric circuit of support depth
   $\leq \Delta$ computing $\hom_{T_{\Delta,n},n}$ has orbit size at least
   $$
     n^{\log_2 n - \Delta \log_2 \log_2 n - 3}.
   $$
2. For $\Delta \geq 1$ and $n \geq 5$, there is a matrix-symmetric circuit of support depth
   $\leq \Delta + 1$ and orbit size $\leq n^2$ computing $\hom_{T_{\Delta,n},n}$.

-/

namespace Lax461425.DepthHierarchy

open Circuits MatrixSymmetry Supports HomomorphismPolynomials

/-- The words over `Fin n` of length at most `Δ` whose length satisfies `p`. -/
abbrev Words (Δ n : ℕ) (p : ℕ → Prop) : Type :=
  {w : List (Fin n) // w.length ≤ Δ ∧ p w.length}

instance (Δ n : ℕ) (p : ℕ → Prop) : Finite (Words Δ n p) :=
  ((List.finite_length_le (Fin n) Δ).subset fun _ hw => hw.1).to_subtype

/-- The full `n`-ary tree `T_{Δ,n}` of depth `Δ`: its vertices are the words over `Fin n` of
length at most `Δ`, words of even length on the left and of odd length on the right, and a word
`w` is adjacent to the words `w ++ [i]`. -/
noncomputable def fullTree (Δ n : ℕ) : Pattern where
  A := Words Δ n Even
  B := Words Δ n Odd
  fintypeA := Fintype.ofFinite _
  fintypeB := Fintype.ofFinite _
  decEqA := inferInstance
  decEqB := inferInstance
  mult a b := by
    classical
    exact if (∃ i, b.1 = a.1 ++ [i]) ∨ ∃ i, a.1 = b.1 ++ [i] then 1 else 0

/-- Every reduced matrix-symmetric circuit of support depth `≤ Δ` computing `hom_{T_{Δ,n},n}`
has orbit size at least `n ^ (log₂ n - Δ log₂ log₂ n - 3)`. -/
axiom orbitSize_ge {K : Type*} [Field K] [CharZero K] {Δ n : ℕ} (hΔ : 1 ≤ Δ) (hn : 20 ≤ n)
    (C : Circuit (Fin n × Fin n) K) (hC : C.Computes (hom K (fullTree Δ n) n))
    (hred : C.IsReduced) (hsym : IsMatrixSymmetric C) (hdepth : supportDepth C ≤ Δ) :
    (n : ℝ) ^ (Real.logb 2 n - Δ * Real.logb 2 (Real.logb 2 n) - 3) ≤ orbitSize C

/-- `hom_{T_{Δ,n},n}` is computed by a reduced matrix-symmetric circuit of support depth
`≤ Δ + 1` and orbit size `≤ n ^ 2`. -/
axiom exists_circuit {K : Type*} [Field K] [CharZero K] {Δ n : ℕ} (hΔ : 1 ≤ Δ) (hn : 5 ≤ n) :
    ∃ C : Circuit (Fin n × Fin n) K,
      C.Computes (hom K (fullTree Δ n) n) ∧ C.IsReduced ∧ IsMatrixSymmetric C ∧
        supportDepth C ≤ Δ + 1 ∧ orbitSize C ≤ n ^ 2

end Lax461425.DepthHierarchy
