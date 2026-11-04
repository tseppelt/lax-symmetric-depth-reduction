import Lax461425.HomomorphismPolynomials

/-!
---
title: Padding and indexing bipartite patterns
type: definition
---
Square-indexed patterns give all summands in Section 7 the same auxiliary-variable type.
Padding adjoins isolated vertices on each side. Its homomorphism identity is proved
internally in the proof module `Section7Padding`, without a separate result node.
-/

namespace Lax461425.PatternPadding

open HomomorphismPolynomials

/-- A bipartite pattern on the fixed square bipartition `Fin n ⊎ Fin n`. -/
def squarePattern (n : ℕ) (m : Fin n → Fin n → ℕ) : Pattern where
  A := Fin n
  B := Fin n
  mult := m

/-- Adjoin enough isolated vertices to reach `n` vertices on each side when the original
parts have at most `n` vertices. This definition is meaningful without those bounds. -/
def padPattern (F : Pattern) (n : ℕ) : Pattern where
  A := F.A ⊕ Fin (n - Fintype.card F.A)
  B := F.B ⊕ Fin (n - Fintype.card F.B)
  mult
    | .inl a, .inl b => F.mult a b
    | _, _ => 0

end Lax461425.PatternPadding
