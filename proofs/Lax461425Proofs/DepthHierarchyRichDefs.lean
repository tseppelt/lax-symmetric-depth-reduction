import Lax461425.DepthHierarchy
import Lax461425.NonUniformClosure
import Lax461425.Forestwidth
import Lax461425.Oddomorphisms

/-!
Richness (`(Δ,k)`-rich graphs, the dual of `Δ`-forestwidth) and the statements of the lemmas
used in the proof of the first assertion of the depth hierarchy theorem. Each lemma is proved in
its own module `DepthHierarchy*.lean` with the same name and statement; the assembly
`DepthHierarchyLower.lean` imports `DepthHierarchyRichStubs.lean` until all are done.
-/

namespace Lax461425Proofs.DepthHierarchy

open Lax461425 Lax461425.Forestwidth Lax461425.NonUniformClosure Lax461425.Oddomorphisms
  Lax461425.HomomorphismPolynomials Lax68.GraphMinors

/-- `RichSet F k j S`: the vertex set `S` induces a connected `(j+1, k)`-rich subgraph of `F`.
`(1,k)`-rich: connected with at least `k+1` vertices. `(j+2,k)`-rich: connected and containing
`k+1` pairwise disjoint vertex sets inducing connected `(j+1,k)`-rich subgraphs. -/
def RichSet {V : Type*} (F : SimpleGraph V) (k : ℕ) : ℕ → Set V → Prop
  | 0, S => (F.induce S).Connected ∧ k + 1 ≤ S.ncard
  | j + 1, S => (F.induce S).Connected ∧
      ∃ T : Fin (k + 1) → Set V, (∀ i, T i ⊆ S ∧ RichSet F k j (T i)) ∧
        Pairwise (Function.onFun Disjoint T)

/-- `F` is `(Δ,k)`-rich (`Δ ≥ 1`): some connected induced subgraph is. -/
def IsRich {V : Type*} (F : SimpleGraph V) (k Δ : ℕ) : Prop := ∃ S, RichSet F k (Δ - 1) S

/-- The full `m`-ary tree of depth `Δ` as a simple graph on words. -/
def treeG (Δ m : ℕ) : SimpleGraph {w : List (Fin m) // w.length ≤ Δ} where
  Adj w w' := (∃ i, w'.1 = w.1 ++ [i]) ∨ ∃ i, w.1 = w'.1 ++ [i]
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun w h => by
    rcases h with ⟨i, h⟩ | ⟨i, h⟩ <;>
      · have := congrArg List.length h; simp at this⟩

instance (Δ m : ℕ) : Finite {w : List (Fin m) // w.length ≤ Δ} :=
  (List.finite_length_le (Fin m) Δ).to_subtype

noncomputable instance (Δ m : ℕ) : Fintype {w : List (Fin m) // w.length ≤ Δ} :=
  Fintype.ofFinite _

end Lax461425Proofs.DepthHierarchy
