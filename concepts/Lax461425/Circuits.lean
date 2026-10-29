import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Set.Card
import Mathlib.Logic.Relation

/-!
---
title: Algebraic circuits
type: definition
---
An *algebraic circuit* over a commutative ring $\mathbb{K}$ with variables from a set $V$ is a
finite directed acyclic graph whose input gates are labelled by variables or constants of
$\mathbb{K}$ and whose internal gates are labelled by $+$ or $\times$. We allow unbounded fan-in
and parallel wires: the number of wires from a gate $h$ to a gate $g$ is the *multiplicity*
$m(g,h) \in \mathbb{N}$, and $h$ is a *child* of $g$ if $m(g,h) > 0$. Input gates have no
children. There is a distinguished output gate, and every gate lies on a path to it.

Every gate $g$ computes a polynomial $p_g \in \mathbb{K}[V]$: an input gate computes its label,
and
$$
  p_g = \sum_h m(g,h)\, p_h \quad\text{or}\quad p_g = \prod_h p_h^{m(g,h)}
$$
if $g$ is a sum or a product gate, respectively, so that wires are counted with multiplicity
and empty sums and products are $0$ and $1$. The circuit *computes* the polynomial of its
output gate. Formally, "the gate $g$ computes $p$" is defined inductively by these rules, so
that exactly the polynomials obtained by evaluating the circuit bottom-up are computed. Every
gate computes exactly one polynomial; the values $p_h$ at children $h$ with $m(g,h) = 0$ do not
contribute.

The *size* of a circuit is the number of its gates and wires, counting multiplicities. A
*path* of length $m$ is a sequence of gates $g_0, \dots, g_m$ such that $g_{i+1}$ is a child of
$g_i$ for all $i < m$. The *depth* is the maximum length of a path. Since every gate lies on a
path to the output gate, this is the maximum number of wires on a path from the output gate to
a gate without children, e.g. an input gate.

A circuit is *reduced* if no two distinct input gates have the same label and no two distinct
internal gates have the same label and the same multiset of children, i.e. the same
multiplicities $m(g, \cdot)$.
-/

namespace Lax461425.Circuits

/-- The label of a gate: a variable, a constant, or one of the operations `+` and `×`. -/
inductive GateLabel (V K : Type*) where
  | var (x : V)
  | const (c : K)
  | add
  | mul

namespace GateLabel

variable {V K : Type*}

/-- Input gates are the gates labelled by a variable or a constant. -/
def IsInput : GateLabel V K → Prop
  | var _ => True
  | const _ => True
  | add => False
  | mul => False

/-- Rename the variable of a label along `π`, keeping constants and operations fixed. -/
def map (π : V → V) : GateLabel V K → GateLabel V K
  | var x => var (π x)
  | const c => const c
  | add => add
  | mul => mul

end GateLabel

/-- An algebraic circuit with variables `V` and constants from `K`. -/
structure Circuit (V K : Type*) where
  /-- The finite set of gates. -/
  Gate : Type
  [fintypeGate : Fintype Gate]
  /-- The label of each gate. -/
  label : Gate → GateLabel V K
  /-- `wire g h` is the multiplicity of the wire from `h` into `g`. -/
  wire : Gate → Gate → ℕ
  /-- The output gate. -/
  out : Gate
  /-- Input gates have no children. -/
  wire_eq_zero_of_isInput : ∀ g h, (label g).IsInput → wire g h = 0
  /-- There is no directed cycle. -/
  acyclic : ∀ g, ¬ Relation.TransGen (fun h g => 0 < wire g h) g g
  /-- Every gate lies on a path to the output gate. -/
  reaches_out : ∀ g, Relation.ReflTransGen (fun h g => 0 < wire g h) g out

attribute [instance] Circuit.fintypeGate

namespace Circuit

variable {V K : Type*} (C : Circuit V K)

/-- `C.ComputesAt g p`: the gate `g` computes the polynomial `p`. A sum or product gate
computes the sum or product of polynomials `q h` computed at its children `h`, counted with
multiplicity. -/
inductive ComputesAt [CommSemiring K] (C : Circuit V K) : C.Gate → MvPolynomial V K → Prop
  | var {g : C.Gate} {x : V} : C.label g = .var x → C.ComputesAt g (MvPolynomial.X x)
  | const {g : C.Gate} {c : K} : C.label g = .const c → C.ComputesAt g (MvPolynomial.C c)
  | add {g : C.Gate} (q : C.Gate → MvPolynomial V K) : C.label g = .add →
      (∀ h, 0 < C.wire g h → C.ComputesAt h (q h)) → C.ComputesAt g (∑ h, C.wire g h • q h)
  | mul {g : C.Gate} (q : C.Gate → MvPolynomial V K) : C.label g = .mul →
      (∀ h, 0 < C.wire g h → C.ComputesAt h (q h)) → C.ComputesAt g (∏ h, q h ^ C.wire g h)

/-- The circuit computes the polynomial `p` at its output gate. -/
def Computes [CommSemiring K] (p : MvPolynomial V K) : Prop :=
  C.ComputesAt C.out p

/-- The number of gates plus the number of wires, counted with multiplicity. -/
def size : ℕ :=
  Fintype.card C.Gate + ∑ g, ∑ h, C.wire g h

/-- The gates `p 0, …, p m` form a path: each `p (i + 1)` is a child of `p i`. -/
def IsPath {m : ℕ} (p : Fin (m + 1) → C.Gate) : Prop :=
  ∀ i : Fin m, 0 < C.wire (p i.castSucc) (p i.succ)

/-- The maximum length of a path. -/
noncomputable def depth : ℕ :=
  sSup {m | ∃ p : Fin (m + 1) → C.Gate, C.IsPath p}

/-- No two distinct input gates carry the same label, and no two distinct internal gates carry
the same label and the same multiset of children. -/
def IsReduced : Prop :=
  (∀ g g', (C.label g).IsInput → C.label g = C.label g' → g = g') ∧
    ∀ g g', ¬ (C.label g).IsInput → C.label g = C.label g' → C.wire g = C.wire g' → g = g'

end Circuit

end Lax461425.Circuits
