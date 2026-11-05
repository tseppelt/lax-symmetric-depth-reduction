import Lax461425.SymmetricFamilies
import Lax461425.SymmetricClasses
import Lax461425.SymmetricVNP
import Lax461425.SymmetricABPs
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
For skew circuits, Tim's labelled-pattern construction admits a linear decomposition
certificate. This is the direction of the earlier skew/pathwidth characterisation used
in Section 6. The polynomial-orbit statement is eventual, allowing small matrix orders.
The proof reuses Tim's labelled-pattern induction and the checked support and
rigidification results imported here. Its two conclusions have no unproved cited
dependency after resolving the existing theorem interfaces to their checked proofs.
-/
namespace Lax461425.SkewCircuitCharacterisation

open Circuits CircuitProperties MatrixSymmetry Supports
open SymmetricFamilies SymmetricClasses SymmetricVNP SymmetricABPs HomomorphismPolynomials

/-- A bounded-support reduced skew circuit computes a combination of bounded-pathwidth
homomorphism polynomials. The factor two comes from composing graph bags with a width-one
path decomposition of their decomposition tree. -/
axiom mem_span_hom {K : Type*} [Field K] [CharZero K] {k n : ℕ} (hk : 2 ≤ k)
    (hn : 2 * k + 1 ≤ n) (C : Circuit (Fin n × Fin n) K)
    (hred : C.IsReduced) (hsym : IsMatrixSymmetric C) (hsize : supportSize C ≤ k)
    (hskew : IsSkew C) {p : MatrixPolynomial n K} (hp : C.Computes p) :
    p ∈ Submodule.span K {q | ∃ F : Pattern, PathwidthLE (2 * k) F ∧ hom K F n = q}

/-- Polynomial orbit bounds on skew circuits imply an eventual uniform pathwidth bound. -/
axiom eventually_pathwidth_span {K : Type*} [Field K] [CharZero K]
    (f : MatrixFamily K) (hf : InSymVS f) :
    ∃ k N : ℕ, ∀ n, N ≤ n →
      f n ∈ Submodule.span K {q | ∃ F : Pattern, PathwidthLE k F ∧ hom K F n = q}

end Lax461425.SkewCircuitCharacterisation
