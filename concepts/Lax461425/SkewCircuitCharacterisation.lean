import Lax461425.SymmetricFamilies
import Lax461425.SymmetricClasses
import Lax461425.SymmetricVNP
import Lax461425.SymmetricABPs
import Lax461425.SkewFromABP
import Lax461425.PatternWidths
import Lax461425.Supports
import Lax461425.SupportTheorem
import Lax461425.Rigidification
import Lax461425.ReducedRigid
import Mathlib.LinearAlgebra.Span.Defs

/-!
---
title: Characterisation of matrix-symmetric skew circuits
type: theorem
---
Over a field of characteristic zero, a reduced matrix-symmetric skew circuit on an `n × n`
matrix with support size at most `k`, where `2 ≤ k` and `2k + 1 ≤ n`, computes a linear
combination of homomorphism polynomials of patterns of pathwidth at most `2k`.
Together with symmetric ABPs for patterns of bounded pathwidth, it follows that a family of
polynomials $(p_n)$ is computed by matrix-symmetric skew circuits of polynomial orbit size
if, and only if, there is a constant $k$ such that every $p_n$ is a
linear combination of homomorphism polynomials $\hom_{F,n}$ of patterns $F$ of pathwidth at
most $k$.
-/
namespace Lax461425.SkewCircuitCharacterisation

open Circuits CircuitProperties MatrixSymmetry Supports
open SymmetricFamilies SymmetricClasses SymmetricVNP SymmetricABPs HomomorphismPolynomials
open PatternWidths

/-- A bounded-support reduced skew circuit computes a combination of bounded-pathwidth
homomorphism polynomials. -/
axiom mem_span_hom {K : Type*} [Field K] [CharZero K] {k n : ℕ} (hk : 2 ≤ k)
    (hn : 2 * k + 1 ≤ n) (C : Circuit (Fin n × Fin n) K)
    (hred : C.IsReduced) (hsym : IsMatrixSymmetric C) (hsize : supportSize C ≤ k)
    (hskew : IsSkew C) {p : MatrixPolynomial n K} (hp : C.Computes p) :
    p ∈ Submodule.span K {q | ∃ F : Pattern, PathwidthLE (2 * k) F ∧ hom K F n = q}

/-- `symVS` consists of the families spanned by homomorphism polynomials of patterns of
bounded pathwidth. -/
axiom characterisation {K : Type*} [Field K] [CharZero K] (f : MatrixFamily K) :
    InSymVS f ↔ ∃ k : ℕ, ∀ n,
      f n ∈ Submodule.span K {q | ∃ F : Pattern, PathwidthLE k F ∧ hom K F n = q}

end Lax461425.SkewCircuitCharacterisation
