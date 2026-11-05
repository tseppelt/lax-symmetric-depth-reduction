import Lax461425Proofs.Section6ABPToSkew
import Lax461425Proofs.SymmetricABPPaths

/-!
Finite linear combinations of ABPs. Each branch has an initial coefficient edge; all
other added edges have label one. The orbit argument uses distinct branch path lengths,
proved separately, rather than labels that distinguish branches.
-/

namespace Lax461425Proofs.Section6ABPSum

open Lax461425.SymmetricABPs
open scoped Classical

noncomputable section

variable {I V : Type} {K : Type*} [Fintype I] [Nonempty I] [Fintype V] [Field K]
variable (G : I → ABP V K) (c : I → K)

inductive Vertex where
  | source
  | entry (i : I)
  | branch (i : I) (v : (G i).Vertex)
  | exit (i : I)
  | sink

def vertexEquiv : Vertex G ≃ Unit ⊕ (I ⊕ ((Σ i, (G i).Vertex) ⊕ (I ⊕ Unit))) where
  toFun
    | .source => .inl ()
    | .entry i => .inr (.inl i)
    | .branch i v => .inr (.inr (.inl ⟨i, v⟩))
    | .exit i => .inr (.inr (.inr (.inl i)))
    | .sink => .inr (.inr (.inr (.inr ())))
  invFun
    | .inl _ => .source
    | .inr (.inl i) => .entry i
    | .inr (.inr (.inl ⟨i, v⟩)) => .branch i v
    | .inr (.inr (.inr (.inl i))) => .exit i
    | .inr (.inr (.inr (.inr _))) => .sink
  left_inv := by intro v; cases v <;> rfl
  right_inv := by intro v; rcases v with u | (i | (v | (i | u))) <;> rfl

instance : Fintype (Vertex G) := Fintype.ofEquiv _ (vertexEquiv G).symm
instance : DecidableEq (Vertex G) := Classical.decEq _

def edge : Vertex G → Vertex G → Prop
  | .source, .entry _ => True
  | .entry i, .branch j v => ∃ h : i = j, h.symm ▸ v = (G i).source
  | .branch i u, .branch j v => ∃ h : i = j, (G i).edge u (h.symm ▸ v)
  | .branch i u, .exit j => i = j ∧ u = (G i).sink
  | .exit _, .sink => True
  | _, _ => False

def constForm (k : K) : AffineForm V K := ⟨k, fun _ => 0⟩

def label : Vertex G → Vertex G → AffineForm V K
  | .source, .entry i => constForm (c i)
  | .entry _, .branch _ _ => constForm 1
  | .branch i u, .branch j v =>
      if h : i = j then (G i).label u (h.symm ▸ v) else constForm 0
  | .branch i _, .exit _ => constForm 1
  | .exit _, .sink => constForm 1
  | _, _ => constForm 0

def maxHeight : ℕ := Finset.univ.sup fun i =>
  Finset.univ.sup (Section6ABPToSkew.height (G i))

theorem height_le_max (i : I) (v : (G i).Vertex) :
    Section6ABPToSkew.height (G i) v ≤ maxHeight G :=
  (Finset.le_sup (f := Section6ABPToSkew.height (G i)) (Finset.mem_univ v)).trans
    (Finset.le_sup (f := fun i => Finset.univ.sup (Section6ABPToSkew.height (G i)))
      (Finset.mem_univ i))

def rank : Vertex G → ℕ
  | .source => 0
  | .entry _ => 1
  | .branch i v => Section6ABPToSkew.height (G i) v + 2
  | .exit _ => maxHeight G + 3
  | .sink => maxHeight G + 4

theorem edge_rank {u v : Vertex G} (huv : edge G u v) : rank G u < rank G v := by
  cases u <;> cases v <;> simp only [edge] at huv
  all_goals try contradiction
  case source.entry i => simp [rank]
  case entry.branch i j v => rcases huv with ⟨rfl, hv⟩; simp [rank]
  case branch.branch i u j v =>
    rcases huv with ⟨rfl, huv⟩
    exact Nat.add_lt_add_right (Section6ABPToSkew.height_lt (G _) huv) 2
  case branch.exit i u j =>
    rcases huv with ⟨rfl, rfl⟩
    have hh := height_le_max G i (G i).sink
    simp only [rank]; omega
  case exit.sink i => simp [rank]

theorem branch_reaches (i : I) {u v : (G i).Vertex}
    (h : Relation.ReflTransGen (G i).edge u v) :
    Relation.ReflTransGen (edge G) (.branch i u) (.branch i v) := by
  induction h with
  | refl => exact .refl
  | tail _ huv ih => exact ih.tail ⟨rfl, huv⟩

theorem source_reaches (v : Vertex G) : Relation.ReflTransGen (edge G) .source v := by
  have he (i : I) : Relation.ReflTransGen (edge G) .source (.entry i) := .single trivial
  have hb (i : I) (v : (G i).Vertex) :
      Relation.ReflTransGen (edge G) .source (.branch i v) := by
    have hstart : Relation.ReflTransGen (edge G) .source (.branch i (G i).source) :=
      (he i).tail (show edge G (.entry i) (.branch i (G i).source) from ⟨rfl, rfl⟩)
    exact hstart.trans (branch_reaches G i ((G i).source_reaches v))
  have hx (i : I) : Relation.ReflTransGen (edge G) .source (.exit i) :=
    (hb i (G i).sink).tail ⟨rfl, rfl⟩
  cases v with
  | source => exact .refl
  | entry i => exact he i
  | branch i v => exact hb i v
  | exit i => exact hx i
  | sink => exact (hx (Classical.choice inferInstance)).tail trivial

theorem reaches_sink (v : Vertex G) : Relation.ReflTransGen (edge G) v .sink := by
  have hx (i : I) : Relation.ReflTransGen (edge G) (.exit i) .sink := .single trivial
  have hb (i : I) (v : (G i).Vertex) :
      Relation.ReflTransGen (edge G) (.branch i v) .sink := by
    have hlast : Relation.ReflTransGen (edge G) (.branch i v) (.exit i) :=
      (branch_reaches G i ((G i).reaches_sink v)).tail
        (show edge G (.branch i (G i).sink) (.exit i) from ⟨rfl, rfl⟩)
    exact hlast.trans (hx i)
  have he (i : I) : Relation.ReflTransGen (edge G) (.entry i) .sink := by
    have hstart : Relation.ReflTransGen (edge G) (.entry i) (.branch i (G i).source) :=
      .single ⟨rfl, rfl⟩
    exact hstart.trans (hb i (G i).source)
  cases v with
  | source =>
    have hstart : Relation.ReflTransGen (edge G) .source
        (.entry (Classical.choice inferInstance)) := .single trivial
    exact hstart.trans (he (Classical.choice inferInstance))
  | entry i => exact he i
  | branch i v => exact hb i v
  | exit i => exact hx i
  | sink => exact .refl

/-- A finite sum of branches with coefficient edges and unit-labelled padding. -/
abbrev abp : ABP V K where
  Vertex := Vertex G
  edge := edge G
  decEdge := Classical.decRel _
  label := label G c
  source := .source
  sink := .sink
  source_no_incoming := by intro v; cases v <;> simp [edge]
  sink_no_outgoing := by intro v; cases v <;> simp [edge]
  acyclic := by
    intro v h
    have hh : ∀ {u v}, Relation.TransGen (edge G) u v → rank G u < rank G v := by
      intro u v h
      induction h with
      | single h => exact edge_rank G h
      | tail _ h ih => exact ih.trans (edge_rank G h)
    exact (Nat.lt_irrefl _) (hh h)
  source_reaches := source_reaches G
  reaches_sink := reaches_sink G

end
end Lax461425Proofs.Section6ABPSum
