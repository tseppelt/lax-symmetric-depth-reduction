import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card
import Lax871432.GraphClasses

/-!
---
title: Oddomorphisms
type: definition
---
Let $F$ and $G$ be graphs and $\varphi \colon F \to G$ a homomorphism. A vertex
$a \in V(F)$ is *$\varphi$-even* if $|N_F(a) \cap \varphi^{-1}(x)|$ is even for every
$x \in N_G(\varphi(a))$, and *$\varphi$-odd* if it is odd for every such $x$. The homomorphism
$\varphi$ is an *oddomorphism* if

1. every vertex $a \in V(F)$ is $\varphi$-even or $\varphi$-odd, and
2. for every $x \in V(G)$, the fibre $\varphi^{-1}(x)$ contains an odd number of $\varphi$-odd
   vertices.

The homomorphism $\varphi$ is a *weak oddomorphism* if there is a subgraph $F' \subseteq F$ such
that the restriction $\varphi|_{F'} \colon F' \to G$ is an oddomorphism. These notions are due
to Roberson.

A class $\mathcal{F}$ of finite simple graphs is *closed under weak oddomorphisms* if
$G \in \mathcal{F}$ whenever $F \in \mathcal{F}$ and there is a weak oddomorphism
$F \to G$.

Following the definition literally, a vertex $a$ with $N_G(\varphi(a)) = \emptyset$ is both
$\varphi$-even and $\varphi$-odd. Subgraphs $F'$ need not be spanning or induced.
-/

namespace Lax461425.Oddomorphisms

open Lax871432.GraphClasses

variable {V W : Type*} {F : SimpleGraph V} {G : SimpleGraph W}

/-- The neighbours of `a` in `F` that `φ` maps to `x`, i.e. `N_F(a) ∩ φ⁻¹(x)`. -/
def neighborsOver (φ : F →g G) (a : V) (x : W) : Set V :=
  {b | F.Adj a b ∧ φ b = x}

/-- `a` is `φ`-even: it has an even number of neighbours over every neighbour of `φ a`. -/
def IsEven (φ : F →g G) (a : V) : Prop :=
  ∀ x, G.Adj (φ a) x → Even (neighborsOver φ a x).ncard

/-- `a` is `φ`-odd: it has an odd number of neighbours over every neighbour of `φ a`. -/
def IsOdd (φ : F →g G) (a : V) : Prop :=
  ∀ x, G.Adj (φ a) x → Odd (neighborsOver φ a x).ncard

/-- `φ` is an oddomorphism: every vertex is `φ`-even or `φ`-odd, and every fibre contains an
odd number of `φ`-odd vertices. -/
structure IsOddomorphism (φ : F →g G) : Prop where
  even_or_odd : ∀ a, IsEven φ a ∨ IsOdd φ a
  odd_card_fibre : ∀ x, Odd {a | φ a = x ∧ IsOdd φ a}.ncard

/-- `φ` is a weak oddomorphism: its restriction to some subgraph of `F` is an oddomorphism. -/
def IsWeakOddomorphism (φ : F →g G) : Prop :=
  ∃ F' : F.Subgraph, IsOddomorphism (φ.comp F'.hom)

/-- `𝓕` is closed under weak oddomorphisms: the target of a weak oddomorphism from a member
is a member. -/
def IsWeakOddomorphismClosed (𝓕 : GraphClass) : Prop :=
  ∀ {V W : Type} [Finite V] [Finite W] {F : SimpleGraph V} {G : SimpleGraph W} (φ : F →g G),
    IsWeakOddomorphism φ → 𝓕.Mem F → 𝓕.Mem G

end Lax461425.Oddomorphisms
