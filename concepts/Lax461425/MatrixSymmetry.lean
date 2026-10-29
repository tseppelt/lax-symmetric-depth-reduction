import Mathlib.GroupTheory.Perm.Basic
import Lax461425.Circuits

/-!
---
title: Matrix-symmetric circuits
type: definition
---
For $n \in \mathbb{N}$, let $\mathcal{X}_n = \{x_{i,j} : i, j \in [n]\}$ be the entries of an
$n \times n$ matrix of variables. The group $\Gamma_n = \mathbf{Sym}_n \times \mathbf{Sym}_n$
acts on $\mathcal{X}_n$ by permuting rows and columns independently,
$(\sigma, \tau)\, x_{i,j} = x_{\sigma(i), \tau(j)}$, and on the disjoint union
$[n] \uplus [n]$ of a copy of $[n]$ indexing the rows (the left side) and a copy indexing the
columns (the right side).

Let $C$ be an algebraic circuit with variables $\mathcal{X}_n$. A permutation $\sigma$ of the
gates of $C$ *extends* $\gamma \in \Gamma_n$ if it preserves the labels of internal gates and
the multiplicities of wires, $m(\sigma g, \sigma h) = m(g, h)$, and maps every input gate
labelled by a variable $x$ to a gate labelled by $\gamma x$ and every input gate labelled by a
constant to a gate labelled by the same constant. Such permutations are the circuit
automorphisms extending $\gamma$.

The circuit $C$ is *matrix-symmetric* if every $\gamma \in \Gamma_n$ extends to a circuit
automorphism, and *rigid* if every $\gamma \in \Gamma_n$ extends to a unique circuit
automorphism. Let $\mathbf{Aut}_\Gamma(C)$ be the group of circuit automorphisms extending
some element of $\Gamma_n$. The *orbit size* of $C$ is
$$
  \max_{g} \bigl|\{\sigma(g) : \sigma \in \mathbf{Aut}_\Gamma(C)\}\bigr|,
$$
the maximum taken over all gates $g$ of $C$.
-/

namespace Lax461425.MatrixSymmetry

open Circuits

/-- The group `Γₙ = Symₙ × Symₙ` permuting rows and columns. -/
abbrev Γ (n : ℕ) := Equiv.Perm (Fin n) × Equiv.Perm (Fin n)

/-- The action of `Γₙ` on the variables: `(σ, τ) x_{i,j} = x_{σ(i), τ(j)}`. -/
def actVar {n : ℕ} (γ : Γ n) (x : Fin n × Fin n) : Fin n × Fin n :=
  (γ.1 x.1, γ.2 x.2)

/-- The action of `Γₙ` on `[n] ⊎ [n]`: rows on the left, columns on the right. -/
def actPoint {n : ℕ} (γ : Γ n) : Fin n ⊕ Fin n → Fin n ⊕ Fin n :=
  Sum.map γ.1 γ.2

variable {V K : Type*}

/-- The permutation `σ` of the gates is a circuit automorphism extending the renaming `π` of
the variables. -/
def Extends (C : Circuit V K) (σ : C.Gate ≃ C.Gate) (π : V → V) : Prop :=
  (∀ g, C.label (σ g) = (C.label g).map π) ∧ ∀ g h, C.wire (σ g) (σ h) = C.wire g h

variable {n : ℕ} (C : Circuit (Fin n × Fin n) K)

/-- Every element of `Γₙ` extends to a circuit automorphism. -/
def IsMatrixSymmetric : Prop :=
  ∀ γ : Γ n, ∃ σ : C.Gate ≃ C.Gate, Extends C σ (actVar γ)

/-- Every element of `Γₙ` extends to a unique circuit automorphism. -/
def IsRigid : Prop :=
  ∀ γ : Γ n, ∃! σ : C.Gate ≃ C.Gate, Extends C σ (actVar γ)

/-- The orbit of a gate under the circuit automorphisms extending elements of `Γₙ`. -/
def orbit (g : C.Gate) : Set C.Gate :=
  {g' | ∃ (γ : Γ n) (σ : C.Gate ≃ C.Gate), Extends C σ (actVar γ) ∧ σ g = g'}

/-- The maximum size of an orbit of a gate. -/
noncomputable def orbitSize : ℕ :=
  Finset.univ.sup fun g => (orbit C g).ncard

end Lax461425.MatrixSymmetry
